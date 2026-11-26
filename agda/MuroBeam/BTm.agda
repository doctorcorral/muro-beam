------------------------------------------------------------------------
-- Local code terms. `BTm` is muro's `GTm` plus `gref k`, a use of
-- global definition k, plus `gcon` / `gcase` for declared data
-- (B1d). The grade checker is not muro's: `decideB` copies `decide`
-- on the old constructors, charges a `gref` nothing in the local
-- context, adds the uses of every `gcon` argument, and checks a
-- `gcase` arm under `arity` copies of `predPair`. A definition is
-- closed code, used at grade ω. The bound is the number of
-- definitions in scope, not a second lattice.
--
-- `embed` is the gref-free, constructor-free fragment. `decide-embed`
-- says `decideB` agrees with muro's `decide` there, for any bound.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.BTm where

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<ᵇ_; _+_)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Mode; spec; Result; ok; fail; _>>=_; _>>_; guard)
import Muro.Grade as MG

open MG using
  ( Grade; Pair; gp; aff; gω; GCtx; Uses; Spent; sp; Count; finᶜ
  ; decide; under; addU; maxU; oneS; charge; zeros; pcomp; ptype )

------------------------------------------------------------------------
-- Syntax. The old constructors have the same names as `GTm`.
-- `gref` is not a de Bruijn index: it names a definition.
------------------------------------------------------------------------

-- A `garm` binds `binds` constructor fields, last field nearest
-- (de Bruijn 0), then continues at the outer scope. The tag is the
-- 0-based constructor index in the data type's declaration order.
mutual
  data Arm (n : ℕ) : Set where
    arm : ℕ → (binds : ℕ) → BTm (binds + n) → Arm n

  data BTm (n : ℕ) : Set where
    gvar   : Fin n → BTm n
    gtyp   : Fin n → BTm n
    glam   : Grade → Grade → BTm (suc n) → BTm n
    gpi    : Grade → Grade → BTm (suc n) → BTm n
    gapp   : BTm n → BTm n → BTm n
    gze    : BTm n
    gsu    : BTm n → BTm n
    gmatch : BTm n → BTm n → BTm (suc n) → BTm n
    gref   : ℕ → BTm n
    gcon   : ℕ → List (BTm n) → BTm n
    gcase  : BTm n → List (Arm n) → BTm n

embed : ∀ {n} → MG.GTm n → BTm n
embed (MG.gvar x) = gvar x
embed (MG.gtyp x) = gtyp x
embed (MG.glam c t b) = glam c t (embed b)
embed (MG.gpi c t b) = gpi c t (embed b)
embed (MG.gapp f a) = gapp (embed f) (embed a)
embed MG.gze = gze
embed (MG.gsu e) = gsu (embed e)
embed (MG.gmatch e z s) = gmatch (embed e) (embed z) (embed s)

-- A variable inherits its binder. Anything else, including `gref`,
-- binds an affine predecessor. That is `predPair`'s catch-all.
predPair : ∀ {n} → GCtx n → BTm n → Pair
predPair Γ (gvar x) = Vec.lookup Γ x
predPair _ _        = gp aff gω

-- `w` is the definition bound. It is not the local context length,
-- and a binder does not change it. `k <ᵇ w` accepts definition k.
-- The use vector is zeros: a `gref` is an ω copy of code, not a use
-- of a local binder, and `under` does not discharge it.
-- Peel `k` binders, each at the same pair, after the body is checked.
unders : ∀ {n} (k : ℕ) → Mode → Grade → Grade → Uses (k + n) → Result (Uses n)
unders zero _ _ _ us = ok us
unders {n} (suc k) m c t us = under m c t us >>= unders {n} k m c t

tel : ∀ {n} (k : ℕ) → Pair → GCtx n → GCtx (k + n)
tel zero _ Γ = Γ
tel (suc k) p Γ = p Vec.∷ tel k p Γ

mutual
  decideB : ∀ {n} → ℕ → Mode → GCtx n → BTm n → Result (Uses n)
  decideB _ m _ (gvar x) = ok (oneS x (charge m))
  decideB _ _ _ (gtyp x) = ok (oneS x (sp (finᶜ zero) (finᶜ (suc zero))))
  decideB w m Γ (glam c t body) =
    decideB w m (gp c t Vec.∷ Γ) body >>= λ us →
    under m c t us
  decideB w _ Γ (gpi c t body) =
    decideB w spec (gp c t Vec.∷ Γ) body >>= λ us →
    under spec c t us
  decideB w m Γ (gapp f a) =
    decideB w m Γ f >>= λ fu →
    decideB w m Γ a >>= λ au →
    ok (addU fu au)
  decideB _ _ _ gze = ok zeros
  decideB w m Γ (gsu e) = decideB w m Γ e
  decideB w m Γ (gmatch e z s) =
    decideB w m Γ e >>= λ eu →
    decideB w m Γ z >>= λ zu →
    let p = predPair Γ e in
    decideB w m (p Vec.∷ Γ) s >>= λ su →
    under m (pcomp p) (ptype p) su >>= λ srest →
    ok (addU eu (maxU zu srest))
  decideB w _ _ (gref k) = guard "bad gref" (k <ᵇ w) >> ok zeros
  decideB w m Γ (gcon _ es) = decideArgs w m Γ es
  decideB w m Γ (gcase e []) = decideB w m Γ e >>= λ _ → fail "empty gcase"
  decideB w m Γ (gcase e (a ∷ as)) =
    decideB w m Γ e >>= λ eu →
    decideArms w m Γ (predPair Γ e) (a ∷ as) >>= λ au →
    ok (addU eu au)

  decideArgs : ∀ {n} → ℕ → Mode → GCtx n → List (BTm n) → Result (Uses n)
  decideArgs _ _ _ [] = ok zeros
  decideArgs w m Γ (e ∷ es) =
    decideB w m Γ e >>= λ eu →
    decideArgs w m Γ es >>= λ ru →
    ok (addU eu ru)

  decideArm : ∀ {n} → ℕ → Mode → GCtx n → Pair → Arm n → Result (Uses n)
  decideArm w m Γ p (arm _ k body) =
    decideB w m (tel k p Γ) body >>= unders k m (pcomp p) (ptype p)

  decideArms : ∀ {n} → ℕ → Mode → GCtx n → Pair → List (Arm n) → Result (Uses n)
  decideArms _ _ _ _ [] = fail "empty gcase"
  decideArms w m Γ p (a ∷ []) = decideArm w m Γ p a
  decideArms w m Γ p (a ∷ a2 ∷ as) =
    decideArm w m Γ p a >>= λ u0 →
    decideArms w m Γ p (a2 ∷ as) >>= λ u1 →
    ok (maxU u0 u1)

-- `embed` does not invent a `gref`, so the predecessor grade agrees.
pred-embed : ∀ {n} (Γ : GCtx n) (e : MG.GTm n) →
             predPair Γ (embed e) ≡ MG.predPair Γ e
pred-embed _ (MG.gvar _) = refl
pred-embed _ (MG.gtyp _) = refl
pred-embed _ (MG.glam _ _ _) = refl
pred-embed _ (MG.gpi _ _ _) = refl
pred-embed _ (MG.gapp _ _) = refl
pred-embed _ MG.gze = refl
pred-embed _ (MG.gsu _) = refl
pred-embed _ (MG.gmatch _ _ _) = refl

decide-embed : ∀ {n} w m (Γ : GCtx n) (e : MG.GTm n) →
               decideB w m Γ (embed e) ≡ decide m Γ e
decide-embed _ _ _ (MG.gvar _) = refl
decide-embed _ _ _ (MG.gtyp _) = refl
decide-embed w m Γ (MG.glam c t b)
  rewrite decide-embed w m (gp c t Vec.∷ Γ) b = refl
decide-embed w _ Γ (MG.gpi c t b)
  rewrite decide-embed w spec (gp c t Vec.∷ Γ) b = refl
decide-embed w m Γ (MG.gapp f a)
  rewrite decide-embed w m Γ f | decide-embed w m Γ a = refl
decide-embed _ _ _ MG.gze = refl
decide-embed w m Γ (MG.gsu e) rewrite decide-embed w m Γ e = refl
decide-embed w m Γ (MG.gmatch e z s)
  rewrite decide-embed w m Γ e
        | decide-embed w m Γ z
        | pred-embed Γ e
        | decide-embed w m (MG.predPair Γ e Vec.∷ Γ) s = refl

-- The code table is a list. Index 0 is the first definition.
lookupIx : ∀ {A : Set} → List A → ℕ → Maybe A
lookupIx []       _       = nothing
lookupIx (x ∷ _)  zero    = just x
lookupIx (_ ∷ xs) (suc k) = lookupIx xs k
