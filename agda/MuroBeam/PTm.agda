------------------------------------------------------------------------
-- checkP, lowerP, and the process-layer safety theorems.
-- Grade decisions go through muro's decide, sat, and checkGrade.
-- No new lattice. No multiplicative application.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.PTm where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero)
open import Data.List.Base using (List; length) renaming ([] to nil; _∷_ to _∷ₗ_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import Data.Unit.Base using (⊤; tt)
open import Muro.Base using
  ( run; Result; ok; fail; Use; U0; U1; Uω; _>>=_; _>>_; _orElse_; guard )
open import Muro.Grade using
  ( Grade; g0; g1; gω; gze; Count; finᶜ; many; Point; fin; pt
  ; sat; checkGrade
  ; Pair; gp; Spent; sp; Uses; GCtx; GTm
  ; decide; under; hold; addU; oneS; charge; zeros; pcomp )

open import MuroBeam.Boundary using (inB?; Cxt)
open import MuroBeam.Grade using (kind; Kind; Kmove; Kcopy)
open import MuroBeam.Heap using
  ( Obj; Ref; count; Bound; bnil; Grade1Unique; uniq-nil )
open import MuroBeam.Process using
  ( Sys; sys; Proc; proc; ready; Msg; pr; refsOf; AllInv; refs-inv )
open import MuroBeam.PSyntax using
  ( Thin; t[]; keep; skip
  ; PTm; done; send; recv; spawn; seq
  ; await; ignore; nignore
  ; awaitT; ignoreT; flushT; ncheckT; ndemonT
  ; Code; go; Flight; isProtoAt )
open import MuroBeam.PRun using (spawn1)
open import MuroBeam.Unique using (WF)

------------------------------------------------------------------------
-- A point saturates its own finite count. g1 therefore passes sat
-- at one. A larger finite point passes sat at that point, and the
-- use vector, not this gate, is what `hold` later discharges.
-- g0 never reaches this gate: `kind` is nothing, and `sat g0 (finᶜ 1)`
-- is the refusal.
------------------------------------------------------------------------

selfSat : Grade → Bool
selfSat (pt (fin n)) = sat (pt (fin n)) (finᶜ n)
selfSat _ = false

sendGate : Grade → Result ⊤
sendGate g with kind g
... | nothing    = guard "erased variable used computationally" (sat g (finᶜ 1))
... | just Kmove = guard "move" (selfSat g)
... | just Kcopy =
  checkGrade run g U0 orElse checkGrade run g U1 orElse checkGrade run g Uω

compOf : Spent → Count
compOf (sp c _) = c

typeOf : Spent → Count
typeOf (sp _ t) = t

isZeroCount : Count → Bool
isZeroCount (finᶜ zero)    = true
isZeroCount (finᶜ (suc _)) = false
isZeroCount many = false

isOneCount : Count → Bool
isOneCount (finᶜ (suc zero)) = true
isOneCount (finᶜ zero)       = false
isOneCount (finᶜ (suc (suc _))) = false
isOneCount many            = false

boundaryOk : ∀ {A : Set} → Dec A → Result ⊤
boundaryOk (yes _) = ok tt
boundaryOk (no _)  = fail "outside the boundary"

comps : ∀ {n} → GCtx n → Cxt n
comps []             = []
comps (gp c _ ∷ Γ)   = c ∷ comps Γ

replyTok : Result ⊤
replyTok = guard "reply" (sat g1 (finᶜ 1))

------------------------------------------------------------------------
-- Thin the context the child sees. keep keeps the grade. skip drops it.
------------------------------------------------------------------------

thinCtx : ∀ {m n} → Thin m n → GCtx n → Result (GCtx m)
thinCtx t[]             []       = ok []
thinCtx (skip th)       (_ ∷ Γ)  = thinCtx th Γ
thinCtx (keep th)       (p ∷ Γ)  = thinCtx th Γ >>= λ Γ' → ok (p ∷ Γ')

-- A protocol consumer at this index is one computational use, and that
-- use is not added to the child's. Anything else moved must be quiet
-- in the parent. A copy is held on each side and the parent use remains.
slot : ∀ {n} → ℕ → Grade → Grade → Spent → Spent → PTm n → Result Spent
slot i c t v u tm with isProtoAt i tm
... | true =
  guard "protocol" (isOneCount (compOf u)) >>
  hold run c t v >>
  ok v
... | false with kind c
... | nothing =
  guard "erased variable used computationally" (sat c (finᶜ 1)) >>
  ok u
... | just Kmove =
  guard "moved" (isZeroCount (compOf u) ∧ isZeroCount (typeOf u)) >>
  hold run c t v >>
  ok v
... | just Kcopy =
  hold run c t v >>
  hold run c t u >>
  ok u

merge : ∀ {m n k} → ℕ → Thin m n → GCtx n → Uses m → Uses n → PTm k → Result (Uses n)
merge _ t[]       []           []        []       _  = ok []
merge i (skip th) (_ ∷ Γ)      cu        (u ∷ pu) tm =
  merge (suc i) th Γ cu pu tm >>= λ rest → ok (u ∷ rest)
merge i (keep th) (gp c t ∷ Γ) (v ∷ cu)  (u ∷ pu) tm =
  slot i c t v u tm >>= λ w →
  merge (suc i) th Γ cu pu tm >>= λ rest → ok (w ∷ rest)

------------------------------------------------------------------------
-- The checker. `seq` asks `decide` and `inB?`. A recv binder is `under`.
-- A send is one computational use, gated by `sat` or `checkGrade`.
------------------------------------------------------------------------

checkP : ∀ {n} → GCtx n → PTm n → Result (Uses n)
checkP {n} Γ done = ok (zeros {n})
checkP Γ (send _ x k) =
  sendGate (pcomp (lookup Γ x)) >>
  checkP Γ k >>= λ uk →
  ok (addU (oneS x (charge run)) uk)
checkP Γ (recv c t k) =
  checkP (gp c t ∷ Γ) k >>= λ uk →
  under run c t uk
checkP Γ (spawn th ch pa) =
  thinCtx th Γ >>= λ Γ' →
  checkP Γ' ch >>= λ cu →
  checkP Γ pa >>= λ pu →
  merge zero th Γ cu pu pa
checkP Γ (seq e k) =
  boundaryOk (inB? (comps Γ) e) >>
  decide run Γ e >>= λ eu →
  checkP (gp gω g0 ∷ Γ) k >>= λ uk →
  under run gω g0 uk >>= λ ku →
  ok (addU eu ku)
checkP Γ (await x k) =
  checkP Γ k >>= λ uk →
  ok (addU (oneS x (charge run)) uk)
checkP Γ (ignore x k) =
  checkP Γ k >>= λ uk →
  ok (addU (oneS x (charge run)) uk)
checkP Γ (nignore x k) =
  checkP Γ k >>= λ uk →
  ok (addU (oneS x (charge run)) uk)
checkP Γ (awaitT _ k)  = replyTok >> checkP Γ k
checkP Γ (ignoreT _ k) = replyTok >> checkP Γ k
checkP Γ (flushT _ k)  = replyTok >> checkP Γ k
checkP Γ (ncheckT _ k) = replyTok >> checkP Γ k
checkP Γ (ndemonT _ k) = replyTok >> checkP Γ k

------------------------------------------------------------------------
-- Lowering. One process, empty heap, the checked program in `pr`.
------------------------------------------------------------------------

record CheckedP : Set where
  constructor checkedP
  field
    prog : PTm 0
    okp  : checkP [] prog ≡ ok []

lowerP : CheckedP → Sys
lowerP p =
  sys (nil {A = Obj})
    (proc zero ready (nil {A = Ref}) (nil {A = Msg})
       (pr (go (CheckedP.prog p)
             (nil {A = Ref}) (nil {A = Flight})
             (nil {A = ℕ}) (nil {A = ℕ})))
     ∷ₗ nil {A = Proc})

lowerP-refs : ∀ p → refsOf (lowerP p) ≡ nil {A = Ref}
lowerP-refs p = refl

lowerP-wf : ∀ p → WF (lowerP p)
lowerP-wf p = bnil , uniq-nil

-- Same strength as send-preserves-residual. Every Ref carries Kept.
spawn-preserves-residual : ∀ {s i t} →
  spawn1 s i ≡ just t →
  AllInv (refsOf t)
spawn-preserves-residual _ = refs-inv _

------------------------------------------------------------------------
-- Open programs the traces run. The use that remains is the child's
-- single send of the grade-1 slot. `hold` discharged it; the parent
-- protocol use is the shape check and is not added again.
------------------------------------------------------------------------

g1ctx : GCtx 1
g1ctx = gp g1 g0 ∷ []

ignoreProg : PTm 1
ignoreProg = spawn (keep t[]) (send zero fzero (done {1})) (ignore fzero (done {1}))

ignore-checks : checkP g1ctx ignoreProg ≡ ok (sp (finᶜ 1) (finᶜ 0) ∷ [])
ignore-checks = refl

roundProg : PTm 1
roundProg = spawn (keep t[]) (send zero fzero (done {1})) (recv gω g0 (done {2}))

round-checks : checkP g1ctx roundProg ≡ ok (sp (finᶜ 1) (finᶜ 0) ∷ [])
round-checks = refl

closedSeq : PTm 0
closedSeq = seq gze (done {1})

closed-checks : checkP [] closedSeq ≡ ok []
closed-checks = refl
