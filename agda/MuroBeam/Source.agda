------------------------------------------------------------------------
-- A closed run-mode term that muro's grade checker accepts, and the
-- capture restriction the v1a machine can keep.
--
-- `NoEscape` is not the spec's position predicate on finite and
-- interval grades. This machine refuses every `glam` while a `g1` is
-- in the environment (`anyG1`), including a λ that sits in the head of
-- a β-redex. The predicate below is that restriction, stated on the
-- syntax: no `glam` is placed where `g1InScope` is true. `InBoundary`
-- implies it. The converse is false: `InBoundary` also refuses a `g0`
-- variable. A finite point above 1, and an interval, may still be
-- captured. That gap is recorded in DESIGN.md.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Source where

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import Muro.Base using (run) renaming (ok to okR)
open import Muro.Grade using
  ( Grade; aff; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch; decide )
open import MuroBeam.Grade using (isG1)

record Checked : Set where
  field
    term : GTm 0
    ok   : decide run [] term ≡ okR []

open Checked public

------------------------------------------------------------------------
-- A grade-1 binder anywhere in the context.
------------------------------------------------------------------------

g1InScope : ∀ {n} → Vec Grade n → Bool
g1InScope []      = false
g1InScope (g ∷ Γ) = isG1 g ∨ g1InScope Γ

-- Same predecessor grade `predPair` uses. A variable inherits its
-- binder. Anything else is the affine interval, which is not g1.
predG : ∀ {n} → Vec Grade n → GTm n → Grade
predG Γ (gvar x) = lookup Γ x
predG _ _        = aff

------------------------------------------------------------------------
-- No λ under a g1 binder. Open terms carry the context the walk has
-- entered. `NoEscape` is the closed predicate.
------------------------------------------------------------------------

data NoEsc {n} (Γ : Vec Grade n) : GTm n → Set where
  ne-var : (x : Fin n) → NoEsc Γ (gvar x)
  ne-typ : (x : Fin n) → NoEsc Γ (gtyp x)
  ne-ze  : NoEsc Γ gze
  ne-su  : ∀ {e} → NoEsc Γ e → NoEsc Γ (gsu e)
  ne-app : ∀ {f a} → NoEsc Γ f → NoEsc Γ a → NoEsc Γ (gapp f a)
  ne-pi  : ∀ {c t b} → NoEsc (c ∷ Γ) b → NoEsc Γ (gpi c t b)
  ne-lam : ∀ {c t b} → g1InScope Γ ≡ false → NoEsc (c ∷ Γ) b →
           NoEsc Γ (glam c t b)
  ne-mat : ∀ {e z s} → NoEsc Γ e → NoEsc Γ z →
           NoEsc (predG Γ e ∷ Γ) s → NoEsc Γ (gmatch e z s)

NoEscape : GTm 0 → Set
NoEscape e = NoEsc [] e

private
  boom : true ≡ false → ⊥
  boom ()

noEsc? : ∀ {n} (Γ : Vec Grade n) (e : GTm n) → Dec (NoEsc Γ e)
noEsc? Γ (gvar x) = yes (ne-var x)
noEsc? Γ (gtyp x) = yes (ne-typ x)
noEsc? Γ gze = yes ne-ze
noEsc? Γ (gsu e) with noEsc? Γ e
... | yes p = yes (ne-su p)
... | no ¬p = no (λ { (ne-su p) → ¬p p })
noEsc? Γ (gapp f a) with noEsc? Γ f | noEsc? Γ a
... | yes pf | yes pa = yes (ne-app pf pa)
... | no ¬f  | _      = no (λ { (ne-app pf _) → ¬f pf })
... | yes _  | no ¬a  = no (λ { (ne-app _ pa) → ¬a pa })
noEsc? Γ (gpi c _ b) with noEsc? (c ∷ Γ) b
... | yes p = yes (ne-pi p)
... | no ¬p = no (λ { (ne-pi p) → ¬p p })
noEsc? Γ (glam c t b) = lamAns (g1InScope Γ) (noEsc? (c ∷ Γ) b) refl
  where
  lamAns : (s : Bool) → Dec (NoEsc (c ∷ Γ) b) → g1InScope Γ ≡ s →
           Dec (NoEsc Γ (glam c t b))
  lamAns true  _       eq = no (λ { (ne-lam p _) → boom (trans (sym eq) p) })
  lamAns false (yes p) eq = yes (ne-lam eq p)
  lamAns false (no ¬p) _  = no (λ { (ne-lam _ p) → ¬p p })
noEsc? Γ (gmatch e z s) with noEsc? Γ e | noEsc? Γ z | noEsc? (predG Γ e ∷ Γ) s
... | yes pe | yes pz | yes ps = yes (ne-mat pe pz ps)
... | no ¬e  | _      | _      = no (λ { (ne-mat pe _ _) → ¬e pe })
... | yes _  | no ¬z  | _      = no (λ { (ne-mat _ pz _) → ¬z pz })
... | yes _  | yes _  | no ¬s  = no (λ { (ne-mat _ _ ps) → ¬s ps })

noEscape? : (e : GTm 0) → Dec (NoEscape e)
noEscape? e = noEsc? [] e
