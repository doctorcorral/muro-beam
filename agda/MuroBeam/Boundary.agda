------------------------------------------------------------------------
-- MuroBeam.Boundary. boundary v1.
--
-- The contract a program targeting this runtime relies on. Heap,
-- Process, Collect, and Lower are the implementation. This module
-- re-exports them. It adds no typing judgment. vendor/muro is
-- untouched. Application stays additive: `decide` on `gapp` is `addU`.
--
-- Dependency. The arrow runs from Boundary into the v1a modules.
-- Those modules do not import Boundary, so there is no cycle.
-- MuroBeam.Example is the client: it decides `grade-once` and the §2B
-- term. A pure Muro mirror of this module is later work. The intended
-- Muro-side spelling, once an emitter exists, is
--
--   import beam "muro-beam-boundary"
--   def myProc : run Π (r : BeamGrade) → InBoundary r → Proc
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Boundary where

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base as Vec using (Vec; lookup)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no) public
open import Relation.Nullary.Negation.Core using (¬_) public

open import Muro.Grade
  using (Grade; Point; fin; inf; pt; iv; aff
        ; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch)
  renaming (g0 to grade0; g1 to grade1; gω to gradeω)
  public

open import MuroBeam.Grade using
  ( Kept; iv-kept; isG1; isZeroGrade
  ; kind; Kind; Kmove; Kcopy
  ; spend; spend-finite; spend-ω; spend-iv
  ; Spent; spent
  ) public
open import MuroBeam.Heap using
  ( Val; nat; suc↑; clo; Ref; Ordered; checked; spendRef
  ) public
open import MuroBeam.Process using
  ( Sys; alloc; deref; send; anyG1
  ; reuse-ordered; grade0-not-dereferenced
  ) public
open import MuroBeam.Collect using
  ( Step; Reach; collect; collect-safe; collect-frees-zero
  ; residual-inv-step
  ) public
open import MuroBeam.Unique using
  ( WF; grade1-unique; send-g1-moves
  ) public
open import MuroBeam.Source using (Checked; term) public
open import MuroBeam.Source using
  ( g1InScope; predG; NoEsc; NoEscape
  ; ne-var; ne-typ; ne-ze; ne-su; ne-app; ne-pi; ne-lam; ne-mat )
open import MuroBeam.Lower using
  ( lower; Step*; lower-safe; lower-g0-never-deref
  ) public

private
  boom : true ≡ false → ⊥
  boom ()

------------------------------------------------------------------------
-- boundary v1
------------------------------------------------------------------------

boundary-version : ℕ
boundary-version = 1

------------------------------------------------------------------------
-- Three grades. Intervals are not a fourth runtime grade.
--
--   pt (fin 0)  is g0.  `kind` refuses a send. `spend` refuses a use.
--                       `collect` drops a g0 residual.
--   pt (fin 1)  is g1.  `kind` is Kmove. Uniqueness is `grade1-unique`.
--   pt inf      is ω.   `kind` is Kcopy. `spend-ω` leaves the residual.
--   iv a b      is ω.   The same keep-alive behaviour: `kind` is Kcopy,
--                       `spend-iv` leaves the residual, and
--                       `isZeroGrade` is false, so `collect` keeps the
--                       root. `aff` is that interval.
--   pt (fin n)  for n ≥ 2 is outside the three. Send moves it and spend
--                       decrements it. `grade1-unique` does not apply.
--                       `beamGrade` returns nothing.
------------------------------------------------------------------------

data BeamGrade : Set where
  g0 g1 ω : BeamGrade

beamGrade : Grade → Maybe BeamGrade
beamGrade (pt (fin zero))          = just g0
beamGrade (pt (fin (suc zero)))    = just g1
beamGrade (pt (fin (suc (suc _)))) = nothing
beamGrade (pt inf)                 = just ω
beamGrade (iv _ _)                 = just ω

beam-g0 : beamGrade grade0 ≡ just g0
beam-g0 = refl

beam-g1 : beamGrade grade1 ≡ just g1
beam-g1 = refl

beam-ω : beamGrade gradeω ≡ just ω
beam-ω = refl

beam-iv : ∀ a b → beamGrade (iv a b) ≡ just ω
beam-iv _ _ = refl

beam-fin2 : beamGrade (pt (fin (suc (suc zero)))) ≡ nothing
beam-fin2 = refl

-- The three send behaviours, read off `kind` (MuroBeam.Grade), which
-- pattern-matches on muro's own `Grade`. Not a second lattice.
g0-not-sent : kind grade0 ≡ nothing
g0-not-sent = refl

g1-moved : kind grade1 ≡ just Kmove
g1-moved = refl

ω-copied : kind gradeω ≡ just Kcopy
ω-copied = refl

iv-copied : ∀ a b → kind (iv a b) ≡ kind gradeω
iv-copied _ _ = refl

-- An interval use does not change the residual. `spend-iv` is the proof.
iv-residual-stays : ∀ {a b} →
  spend (iv-kept {a} {b}) ≡ just (spent (iv a b) iv-kept)
iv-residual-stays = spend-iv

------------------------------------------------------------------------
-- Payloads. `Val` is the v1a type: a flat nat, a `suc↑` reference,
-- or a closure with the `List Ref` it captured. `Ordered` is the
-- heap invariant those references live under.
------------------------------------------------------------------------

BeamVal : Set
BeamVal = Val

------------------------------------------------------------------------
-- The fragment.
--
-- `InBoundary` is a predicate on a closed `GTm`. Lowering consumes a
-- `Checked` term, and that term has scope 0, so the contract is stated
-- there. `InB` is the same predicate under the binders the walk has
-- entered. Free variables of an open term are not graded by
-- `InBoundary`; they are graded only once a binder in this term puts
-- them in `InB`'s context.
--
-- A `glam` is refused when a grade-1 binder is already in scope. v1a's
-- `eval1` captures the whole environment (`clo env`), and `anyG1`
-- refuses that step. The §2B term is this shape: both inner closures
-- sit under the outer `g1`, including the `g1` variable captured by
-- the closure that is passed to the `ω` binder. The check is
-- conservative. A `glam` under a `g1` binder is refused even when a
-- particular trace never enters that binder. A `gvar` whose binder is
-- `g0` is refused, because `spend` refuses a `g0` residual. Uses are
-- not counted: two uses of a `g1` variable are `decide`'s refusal, and
-- connecting that count to a trace is v1c.
--
-- A `gpi` body is erased at run time. It is still scanned. A closure
-- written there, under a `g1` binder, is refused. That refuses more
-- than `eval1` will reach.
--
-- What a `yes` guarantees is `capture-check-clear`: if the dynamic
-- environment realises the syntactic context, `anyG1` is false at
-- every `glam` the fragment accepts. It does not by itself say that
-- every `Step*` from `lower` avoids a stuck `eval1`. Shape-stuck
-- terms (`gapp gze gze`) are in the fragment. A second alias of a `g1`
-- pointer (`badG1`) is not decided here. Those are v1c (`NoEscape`,
-- `budget-adequate`).
------------------------------------------------------------------------

Cxt : ℕ → Set
Cxt n = Vec Grade n

-- Same boolean as `g1InScope`. A `glam` under it is the capture
-- `eval1` refuses, so `InB` implies `NoEsc`.
sharpCxt : ∀ {n} → Cxt n → Bool
sharpCxt = g1InScope

-- Same predecessor grade `NoEsc` uses on a match.
predGrade : ∀ {n} → Cxt n → GTm n → Grade
predGrade = predG

data InB {n} (Γ : Cxt n) : GTm n → Set where
  ib-var : ∀ x → isZeroGrade (lookup Γ x) ≡ false → InB Γ (gvar x)
  ib-typ : ∀ x → InB Γ (gtyp x)
  ib-ze  : InB Γ gze
  ib-su  : ∀ {e} → InB Γ e → InB Γ (gsu e)
  ib-app : ∀ {f a} → InB Γ f → InB Γ a → InB Γ (gapp f a)
  ib-pi  : ∀ {c t b} → InB (c Vec.∷ Γ) b → InB Γ (gpi c t b)
  ib-lam : ∀ {c t b} → sharpCxt Γ ≡ false → InB (c Vec.∷ Γ) b →
           InB Γ (glam c t b)
  ib-mat : ∀ {e z s} → InB Γ e → InB Γ z →
           InB (predGrade Γ e Vec.∷ Γ) s → InB Γ (gmatch e z s)

InBoundary : GTm 0 → Set
InBoundary t = InB Vec.[] t

-- The filter implies the capture restriction. The `g0` premise of
-- `ib-var` is dropped: `NoEscape` does not refuse a `g0` variable.
-- The converse is not claimed.
inBoundary→noEscape : ∀ {e} → InBoundary e → NoEscape e
inBoundary→noEscape = toNo Vec.[]
  where
  toNo : ∀ {n} (Γ : Cxt n) {e} → InB Γ e → NoEsc Γ e
  toNo Γ (ib-var x _)     = ne-var x
  toNo Γ (ib-typ x)       = ne-typ x
  toNo _ ib-ze            = ne-ze
  toNo Γ (ib-su p)        = ne-su (toNo Γ p)
  toNo Γ (ib-app pf pa)   = ne-app (toNo Γ pf) (toNo Γ pa)
  toNo _ (ib-pi p)        = ne-pi (toNo _ p)
  toNo _ (ib-lam q p)     = ne-lam q (toNo _ p)
  toNo Γ (ib-mat pe pz ps) = ne-mat (toNo Γ pe) (toNo Γ pz) (toNo _ ps)

-- A `glam` the fragment accepts is not under a grade-1 binder.
lam-not-under-g1 : ∀ {n} {Γ : Cxt n} {c t b} →
  InB Γ (glam c t b) → sharpCxt Γ ≡ false
lam-not-under-g1 (ib-lam p _) = p

-- The inner closure of the §2B shape. Context `(g1)` blocks it.
g1-blocks-lam : ∀ {c t b} → ¬ InB (grade1 Vec.∷ Vec.[]) (glam c t b)
g1-blocks-lam ib = boom (lam-not-under-g1 ib)

-- The dynamic environment realises the syntactic context.
data EnvGrades : ∀ {n} → Cxt n → List Ref → Set where
  eg-nil  : EnvGrades Vec.[] []
  eg-cons : ∀ {n g} {Γ : Cxt n} {r rs} →
            checked r ≡ g →
            EnvGrades Γ rs →
            EnvGrades (g Vec.∷ Γ) (r ∷ rs)

sharp-env : ∀ {n} {Γ : Cxt n} {rs} →
  EnvGrades Γ rs → sharpCxt Γ ≡ anyG1 rs
sharp-env eg-nil = refl
sharp-env (eg-cons {g = g} eq rest) rewrite eq =
  cong (isG1 g ∨_) (sharp-env rest)

-- Where the fragment allows a closure, the machine's capture flag is
-- clear, provided the environment realises the context.
capture-check-clear : ∀ {n} {Γ : Cxt n} {c t b rs} →
  InB Γ (glam c t b) →
  EnvGrades Γ rs →
  anyG1 rs ≡ false
capture-check-clear ib eg =
  trans (sym (sharp-env eg)) (lam-not-under-g1 ib)

-- `lower` starts from the empty environment. `anyG1 []` is false for
-- every closed λ, in the fragment or not. This is `capture-check-clear`
-- at that environment. Carrying `EnvGrades` along `eval1` is v1c.
closed-lam-clear : ∀ {c t b} →
  InBoundary (glam c t b) → anyG1 [] ≡ false
closed-lam-clear ib = capture-check-clear ib eg-nil

------------------------------------------------------------------------
-- Decision. Structural on the term. No fuel, no pragma.
------------------------------------------------------------------------

inB? : ∀ {n} (Γ : Cxt n) (t : GTm n) → Dec (InB Γ t)
inB? Γ (gvar x) = varAns (isZeroGrade (lookup Γ x)) refl
  where
  varAns : (z : Bool) → isZeroGrade (lookup Γ x) ≡ z → Dec (InB Γ (gvar x))
  varAns true  eq = no (λ { (ib-var _ ez) → boom (trans (sym eq) ez) })
  varAns false eq = yes (ib-var x eq)
inB? Γ (gtyp _) = yes (ib-typ _)
inB? Γ gze = yes ib-ze
inB? Γ (gsu e) with inB? Γ e
... | yes p = yes (ib-su p)
... | no ¬p = no (λ { (ib-su p) → ¬p p })
inB? Γ (gapp f a) with inB? Γ f | inB? Γ a
... | yes pf | yes pa = yes (ib-app pf pa)
... | no ¬f  | _      = no (λ { (ib-app pf _) → ¬f pf })
... | yes _  | no ¬a  = no (λ { (ib-app _ pa) → ¬a pa })
inB? Γ (gpi c _ b) with inB? (c Vec.∷ Γ) b
... | yes p = yes (ib-pi p)
... | no ¬p = no (λ { (ib-pi p) → ¬p p })
inB? Γ (glam c ty b) = lamAns (sharpCxt Γ) (inB? (c Vec.∷ Γ) b) refl
  where
  lamAns : (s : Bool) → Dec (InB (c Vec.∷ Γ) b) → sharpCxt Γ ≡ s →
           Dec (InB Γ (glam c ty b))
  lamAns true  _       eq = no (λ ib → boom (trans (sym eq) (lam-not-under-g1 ib)))
  lamAns false (yes p) eq = yes (ib-lam eq p)
  lamAns false (no ¬p) _  = no (λ { (ib-lam _ p) → ¬p p })
inB? Γ (gmatch e z s) with inB? Γ e | inB? Γ z | inB? (predGrade Γ e Vec.∷ Γ) s
... | yes pe | yes pz | yes ps = yes (ib-mat pe pz ps)
... | no ¬e  | _      | _      = no (λ { (ib-mat pe _ _) → ¬e pe })
... | yes _  | no ¬z  | _      = no (λ { (ib-mat _ pz _) → ¬z pz })
... | yes _  | yes _  | no ¬s  = no (λ { (ib-mat _ _ ps) → ¬s ps })

inBoundary? : (t : GTm 0) → Dec (InBoundary t)
inBoundary? t = inB? Vec.[] t
