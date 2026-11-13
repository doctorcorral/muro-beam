------------------------------------------------------------------------
-- A checked trace.
--
--   * a g1 cell is used once, then collected (or reused in place)
--   * a gω cell is used and stays live across collect
--   * an interval cell is used and its residual does not change
--   * a g0 cell is not dereferenced in run mode
--   * sending g1 moves the only reference from process 0 to process 1
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Example where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base as Vec using ()
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (run) renaming (ok to okR)
open import Muro.Grade using
  ( Grade; g0; g1; gω; aff
  ; GTm; gvar; glam; gapp; gze; gmatch; decide
  ; grade-once; grade-twice; grade-match-once; grade-match-many )

open import MuroBeam.Grade using (selfKept)
open import MuroBeam.Heap using
  ( Obj; cell; Status; live; free; payload; status
  ; Ref; ref; residual; checked; obj; count
  ; Val; nat; suc↑; clo )
open import MuroBeam.Lib using (lookup)
open import MuroBeam.Process using
  ( Proc; proc; ready; idle; Msg; msg; Sys; sys; heap; procs; roots; inbox
  ; ctl; Ctl; ev; rv; Frame; fn
  ; refsOf; rootAt; deref; send; recv; alloc; reuse
  ; eval1; runFor )
open import MuroBeam.Ref using
  ( RVal; rnat; RCtl; rrv; startR; runR; closedLam )
open import MuroBeam.Collect using (collect)
open import MuroBeam.Source using (Checked; term; noEscape?)
open import MuroBeam.Lower using (lower)
open import MuroBeam.Cex public using (cex)
open import MuroBeam.Boundary using (inBoundary?; yes; no)

take : ∀ {A : Set} → A → Maybe A → A
take _ (just x) = x
take d nothing  = d

two : Sys
two = sys [] (proc zero ready [] [] idle ∷ proc (suc zero) ready [] [] idle ∷ [])

resOf : Maybe Ref → Maybe Grade
resOf nothing  = nothing
resOf (just r) = just (residual r)

resAt : Sys → ℕ → ℕ → Maybe Grade
resAt s i j = resOf (rootAt s i j)

stOf : Maybe Obj → Maybe Status
stOf nothing  = nothing
stOf (just o) = just (status o)

stAt : List Obj → ℕ → Maybe Status
stAt os i = stOf (lookup os i)

natOf : Val → Maybe ℕ
natOf (nat n)    = just n
natOf (suc↑ _)   = nothing
natOf (clo _ _)  = nothing

payOf : Maybe Obj → Maybe ℕ
payOf nothing  = nothing
payOf (just o) = natOf (payload o)

payAt : List Obj → ℕ → Maybe ℕ
payAt os i = payOf (lookup os i)

procOf : Maybe Proc → Proc
procOf nothing  = proc zero ready [] [] idle
procOf (just p) = p

atProc : Sys → ℕ → Proc
atProc s i = procOf (lookup (procs s) i)

mailObj : List Msg → Maybe ℕ
mailObj []             = nothing
mailObj (msg r ∷ _)    = just (obj r)

rootObj : List Ref → Maybe ℕ
rootObj []       = nothing
rootObj (r ∷ _)  = just (obj r)

------------------------------------------------------------------------
-- Grade 1: one use, then the slot is free. Reuse overwrites it in place.
------------------------------------------------------------------------

g1-alloc : Sys
g1-alloc = take two (alloc two zero g1 (suc (suc (suc (suc (suc (suc (suc zero))))))))

ex-g1-fresh : resAt g1-alloc zero zero ≡ just g1
ex-g1-fresh = refl

g1-used : Sys
g1-used = take g1-alloc (deref run g1-alloc zero zero)

ex-g1-spent : resAt g1-used zero zero ≡ just g0
ex-g1-spent = refl

g1-collected : Sys
g1-collected = collect g1-used

ex-g1-freed : stAt (heap g1-collected) zero ≡ just free
ex-g1-freed = refl

ex-g1-roots-dropped : roots (atProc g1-collected zero) ≡ []
ex-g1-roots-dropped = refl

g1-reused : Sys
g1-reused = take g1-used (reuse g1-used zero zero g1 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

ex-reuse-payload : payAt (heap g1-reused) zero ≡ just (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
ex-reuse-payload = refl

ex-reuse-residual : resAt g1-reused zero zero ≡ just g1
ex-reuse-residual = refl

------------------------------------------------------------------------
-- ω stays ω, and collect keeps the cell.
------------------------------------------------------------------------

ω-alloc : Sys
ω-alloc = take two (alloc two zero gω (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

ω-used : Sys
ω-used = take ω-alloc (deref run ω-alloc zero zero)

ex-ω-kept : resAt ω-used zero zero ≡ just gω
ex-ω-kept = refl

ω-collected : Sys
ω-collected = collect ω-used

ex-ω-live : stAt (heap ω-collected) zero ≡ just live
ex-ω-live = refl

------------------------------------------------------------------------
-- An interval is kept alive: the use does not change the residual.
------------------------------------------------------------------------

iv-alloc : Sys
iv-alloc = take two (alloc two zero aff (suc zero))

iv-used : Sys
iv-used = take iv-alloc (deref run iv-alloc zero zero)

ex-iv-kept : resAt iv-used zero zero ≡ just aff
ex-iv-kept = refl

------------------------------------------------------------------------
-- Grade 0 is not dereferenced in run mode.
------------------------------------------------------------------------

z-alloc : Sys
z-alloc = take two (alloc two zero g0 zero)

ex-g0-not-dereferenced : deref run z-alloc zero zero ≡ nothing
ex-g0-not-dereferenced = refl

------------------------------------------------------------------------
-- Sending g1 moves the only reference onto the receiver's mailbox.
------------------------------------------------------------------------

sent : Sys
sent = take two (send g1-alloc zero zero (suc zero))

ex-send-sender-empty : roots (atProc sent zero) ≡ []
ex-send-sender-empty = refl

ex-send-mailbox : mailObj (inbox (atProc sent (suc zero))) ≡ just zero
ex-send-mailbox = refl

ex-send-unique : count zero (refsOf sent) ≡ suc zero
ex-send-unique = refl

got : Sys
got = take sent (recv sent (suc zero))

ex-recv-root : rootObj (roots (atProc got (suc zero))) ≡ just zero
ex-recv-root = refl

ex-recv-inbox-empty : inbox (atProc got (suc zero)) ≡ []
ex-recv-inbox-empty = refl

ex-recv-still-unique : count zero (refsOf got) ≡ suc zero
ex-recv-still-unique = refl

------------------------------------------------------------------------
-- Lowered checked terms. A closed λ is one step to a closure.
-- The additive counterexample gets stuck with its g1 cell still live.
------------------------------------------------------------------------

lamBack : (c t : Grade) (b : GTm 1) → Sys
lamBack c t b =
  sys (cell (clo [] (zero , glam c t b)) live ∷ [])
      (proc zero ready [] [] (rv (ref zero gω gω (selfKept gω)) [] []) ∷ [])

once : Checked
once = record { term = glam g1 g0 (gvar fzero) ; ok = grade-once }

ex-once : runFor 1 (lower once) ≡ lamBack g1 g0 (gvar fzero)
ex-once = refl

twice : Checked
twice = record
  { term = glam gω g0 (gapp (gvar fzero) (gvar fzero))
  ; ok = grade-twice }

ex-twice : runFor 1 (lower twice) ≡ lamBack gω g0 (gapp (gvar fzero) (gvar fzero))
ex-twice = refl

match-once : Checked
match-once = record
  { term = glam g1 g0 (gmatch (gvar fzero) gze (gvar fzero))
  ; ok = grade-match-once }

ex-match-once : runFor 1 (lower match-once)
               ≡ lamBack g1 g0 (gmatch (gvar fzero) gze (gvar fzero))
ex-match-once = refl

match-many : Checked
match-many = record
  { term = glam gω g0 (gmatch (gvar fzero) gze (gapp (gvar fzero) (gvar fzero)))
  ; ok = grade-match-many }

ex-match-many : runFor 1 (lower match-many)
               ≡ lamBack gω g0 (gmatch (gvar fzero) gze (gapp (gvar fzero) (gvar fzero)))
ex-match-many = refl

-- λ(g1) x. (λ(gω) f. f f) (λ(aff) _. x), applied to zero.
-- The term is MuroBeam.Cex.cex. decide accepts it. The inner λ would
-- capture the still-live g1, so eval1 refuses that closure. collect
-- keeps the g1 cell.
cex-ok : decide run Vec.[] cex ≡ okR Vec.[]
cex-ok = refl

cexApp : Checked
cexApp = record { term = gapp cex gze ; ok = cex-app-ok }
  where
  cex-app-ok : decide run Vec.[] (gapp cex gze) ≡ okR Vec.[]
  cex-app-ok = refl

stuck : Sys
stuck = runFor 6 (lower cexApp)

ex-cex-stuck : eval1 stuck zero ≡ nothing
ex-cex-stuck = refl

ex-cex-kept : stAt (heap (collect stuck)) (suc zero) ≡ just live
ex-cex-kept = refl

ex-cex-dead : stAt (heap (collect stuck)) zero ≡ just free
ex-cex-dead = refl

------------------------------------------------------------------------
-- Boundary v1. `grade-once` builds no closure under its g1 binder, so
-- the fragment accepts it. The §2B term puts both inner closures under
-- that binder, so the fragment refuses it.
------------------------------------------------------------------------

boundary-accept : inBoundary? (term once) ≡ yes _
boundary-accept = refl

boundary-refuse : inBoundary? cex ≡ no _
boundary-refuse = refl

-- `InBoundary` implies `NoEscape`. `grade-once` is in the filter, so
-- the capture restriction holds, and one eval step builds the closure.
-- The §2B term is outside both.
once-no-escape : noEscape? (term once) ≡ yes _
once-no-escape = refl

cex-escapes : noEscape? cex ≡ no _
cex-escapes = refl

------------------------------------------------------------------------
-- A grade-1 use inside `InBoundary`. The reference machine returns
-- zero. The CEK does too, and the binder has been popped: the run
-- ends on a nat, which is the adequate trace of muro's `grade-once`
-- shape applied to zero. The four `ex-*` lemmas above are the
-- closures of muro's own checked examples (`grade-once`,
-- `grade-twice`, `grade-match-once`, `grade-match-many`).
------------------------------------------------------------------------

use1 : GTm 0
use1 = gapp (glam g1 g0 (gvar fzero)) gze

use1-ok : decide run Vec.[] use1 ≡ okR Vec.[]
use1-ok = refl

use1c : Checked
use1c = record { term = use1 ; ok = use1-ok }

use1-boundary : inBoundary? use1 ≡ yes _
use1-boundary = refl

use1-no-escape : noEscape? use1 ≡ yes _
use1-no-escape = refl

use1-ref : runR 40 (startR use1) ≡ rrv (rnat zero) []
use1-ref = refl

-- The nat the CEK returned, when the control is a value and the stack
-- is empty. `payAt` reads a flat payload.
resultNat : Sys → Maybe ℕ
resultNat s with ctl (atProc s zero)
... | rv r [] [] = payAt (heap s) (obj r)
... | _          = nothing

use1-cek : resultNat (runFor 40 (lower use1c)) ≡ just zero
use1-cek = refl

use1-halt : eval1 (runFor 40 (lower use1c)) zero ≡ nothing
use1-halt = refl

once-ref : runR 1 (startR (term once)) ≡ rrv (closedLam (gvar fzero)) []
once-ref = refl

------------------------------------------------------------------------
-- `NoEscape` does not make the CEK follow the reference machine.
-- λ(ω) f. (λ(g1) x. x) f, applied to λ(ω) _. 0, is in `InBoundary`.
-- The reference β returns the argument closure. The CEK is standing
-- on that β and `eval1` is nothing: the argument object is also in
-- the environment, so `badG1` refuses the step.
------------------------------------------------------------------------

alias : GTm 0
alias =
  gapp
    (glam gω g0
      (gapp (glam g1 g0 (gvar fzero)) (gvar fzero)))
    (glam gω g0 gze)

alias-ok : decide run Vec.[] alias ≡ okR Vec.[]
alias-ok = refl

aliasc : Checked
aliasc = record { term = alias ; ok = alias-ok }

alias-boundary : inBoundary? alias ≡ yes _
alias-boundary = refl

alias-no-escape : noEscape? alias ≡ yes _
alias-no-escape = refl

alias-ref : runR 40 (startR alias) ≡ rrv (closedLam gze) []
alias-ref = refl

stuckBeta : Sys → Bool
stuckBeta s with ctl (atProc s zero)
... | rv _ _ (fn _ ∷ _) = true
... | _                 = false

alias-cek : stuckBeta (runFor 40 (lower aliasc)) ≡ true
alias-cek = refl

alias-halt : eval1 (runFor 40 (lower aliasc)) zero ≡ nothing
alias-halt = refl
