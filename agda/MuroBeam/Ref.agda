------------------------------------------------------------------------
-- Grade-free CBV environment machine on `GTm`.
--
-- `_↦_` is one step. It does not read a grade, and a variable lookup
-- always returns the value in the environment. The CEK spends a
-- residual and refuses `badG1`, so a step here need not be a `Step`.
-- `lower-sim` is that missing correspondence. It is not defined in
-- this module: under the `NoEscape` that `InBoundary` implies, the
-- forward statement is false. `MuroBeam.Example` gives the term.
-- Backward simulation and determinacy are not stated.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Ref where

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; lookup) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import Muro.Grade using
  ( GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch )

data RVal : Set where
  rnat : ℕ → RVal
  rsuc : RVal → RVal
  rlam : ∀ {n} → Vec RVal n → GTm (suc n) → RVal

data RFrame : Set where
  rar : ∀ {n} → GTm n → Vec RVal n → RFrame
  rfn : RVal → RFrame
  rsu : RFrame
  rmt : ∀ {n} → GTm n → GTm (suc n) → Vec RVal n → RFrame

data RCtl : Set where
  rev : ∀ {n} → GTm n → Vec RVal n → List RFrame → RCtl
  rrv : RVal → List RFrame → RCtl

startR : GTm 0 → RCtl
startR e = rev e []ᵥ []

-- A λ evaluated in the empty environment.
closedLam : GTm 1 → RVal
closedLam b = rlam []ᵥ b

applyV : RVal → RVal → List RFrame → Maybe RCtl
applyV (rlam env b) v k = just (rev b (v ∷ᵥ env) k)
applyV (rnat _)     _ _ = nothing
applyV (rsuc _)     _ _ = nothing

matchV : RVal → ∀ {n} → GTm n → GTm (suc n) → Vec RVal n →
         List RFrame → Maybe RCtl
matchV (rnat zero)    z _ env k = just (rev z env k)
matchV (rnat (suc _)) _ _ _   _ = nothing
matchV (rsuc p)       _ s env k = just (rev s (p ∷ᵥ env) k)
matchV (rlam _ _)     _ _ _   _ = nothing

-- One grade-free step. `nothing` is a finished value or a shape error.
rstep : RCtl → Maybe RCtl
rstep (rev (gvar x) env k) = just (rrv (lookup env x) k)
rstep (rev (gtyp _) _ k) = just (rrv (rnat zero) k)
rstep (rev (gpi _ _ _) _ k) = just (rrv (rnat zero) k)
rstep (rev (glam _ _ b) env k) = just (rrv (rlam env b) k)
rstep (rev (gapp f a) env k) = just (rev f env (rar a env ∷ k))
rstep (rev gze _ k) = just (rrv (rnat zero) k)
rstep (rev (gsu e) env k) = just (rev e env (rsu ∷ k))
rstep (rev (gmatch e z s) env k) = just (rev e env (rmt z s env ∷ k))
rstep (rrv _ []) = nothing
rstep (rrv v (rar a env ∷ k)) = just (rev a env (rfn v ∷ k))
rstep (rrv v (rfn f ∷ k)) = applyV f v k
rstep (rrv v (rsu ∷ k)) = just (rrv (rsuc v) k)
rstep (rrv v (rmt z s env ∷ k)) = matchV v z s env k

data _↦_ : RCtl → RCtl → Set where
  r-step : ∀ {s t} → rstep s ≡ just t → s ↦ t

-- Fuel-bounded evaluation. Structural on the fuel. Stays put when
-- `rstep` returns `nothing`.
runR : ℕ → RCtl → RCtl
runR zero s = s
runR (suc n) s with rstep s
... | just t  = runR n t
... | nothing = s
