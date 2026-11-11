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

open import Data.Fin.Base using () renaming (zero to fzero; suc to fsuc)
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
  ; ctl; Ctl; ev; rv
  ; refsOf; rootAt; deref; send; recv; alloc; reuse
  ; eval1; runFor )
open import MuroBeam.Collect using (collect)
open import MuroBeam.Source using (Checked)
open import MuroBeam.Lower using (lower)

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
-- decide accepts it. The inner λ would capture the still-live g1, so
-- eval1 refuses that closure. collect keeps the g1 cell.
cex : GTm 0
cex =
  glam g1 g0
    (gapp
      (glam gω g0 (gapp (gvar fzero) (gvar fzero)))
      (glam aff g0 (gvar (fsuc fzero))))

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
