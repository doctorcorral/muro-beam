------------------------------------------------------------------------
-- Residual grades on top of Muro.Grade.
--
-- A reference stores the grade muro checked and a residual computational
-- grade. `Kept residual checked` is the v0 reading of residual ≤ checked.
-- Finite points step down by one use. ω and intervals stay where they are:
-- v0 keeps those roots alive.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Grade where

open import Data.Bool.Base using (Bool; true; false; not; _∧_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Mode; run; spec; evid)
open import Muro.Grade using
  ( Point; Grade; fin; inf; pt; iv; g0; g1; gω
  ; _≤ᵍ_; _≤ᵖ_
  ; grade-erased-first
  )

open import MuroBeam.Lib using
  ( ⊥; ¬_
  ; ≤-refl; lower; ≤ᵇ-complete; ∧-both
  )

------------------------------------------------------------------------
-- Kept: residual ≤ checked, in a form the runtime can step.
------------------------------------------------------------------------

data Kept : Grade → Grade → Set where
  fin-kept : ∀ {k n} → k ≤ n → Kept (pt (fin k)) (pt (fin n))
  ω-kept   : Kept gω gω
  iv-kept  : ∀ {a b} → Kept (iv a b) (iv a b)

selfKept : (g : Grade) → Kept g g
selfKept (pt (fin n)) = fin-kept ≤-refl
selfKept (pt inf)     = ω-kept
selfKept (iv _ _)     = iv-kept

≤ᵖ-refl : ∀ p → (p ≤ᵖ p) ≡ true
≤ᵖ-refl (fin n) = ≤ᵇ-complete (≤-refl {n})
≤ᵖ-refl inf     = refl

kept→≤ᵍ : ∀ {r c} → Kept r c → (r ≤ᵍ c) ≡ true
kept→≤ᵍ (fin-kept le)      = ≤ᵇ-complete le
kept→≤ᵍ ω-kept             = refl
kept→≤ᵍ (iv-kept {a} {b})  = ∧-both (≤ᵖ-refl a) (≤ᵖ-refl b)

------------------------------------------------------------------------
-- A residual of point 0 is exhausted. Intervals are not that point.
------------------------------------------------------------------------

isZeroGrade : Grade → Bool
isZeroGrade (pt (fin zero))    = true
isZeroGrade (pt (fin (suc _))) = false
isZeroGrade (pt inf)           = false
isZeroGrade (iv _ _)           = false

isZero-sound : ∀ g → isZeroGrade g ≡ true → g ≡ g0
isZero-sound (pt (fin zero))    refl = refl
isZero-sound (pt (fin (suc _))) ()
isZero-sound (pt inf)           ()
isZero-sound (iv _ _)           ()

isZero-complete : ∀ g → g ≡ g0 → isZeroGrade g ≡ true
isZero-complete .g0 refl = refl

isG1 : Grade → Bool
isG1 (pt (fin zero))           = false
isG1 (pt (fin (suc zero)))     = true
isG1 (pt (fin (suc (suc _))))  = false
isG1 (pt inf)                  = false
isG1 (iv _ _)                  = false

isG1-sound : ∀ g → isG1 g ≡ true → g ≡ g1
isG1-sound (pt (fin zero))          ()
isG1-sound (pt (fin (suc zero)))    refl = refl
isG1-sound (pt (fin (suc (suc _)))) ()
isG1-sound (pt inf)                 ()
isG1-sound (iv _ _)                 ()

isG1-complete : ∀ g → g ≡ g1 → isG1 g ≡ true
isG1-complete .g1 refl = refl

isG1-cong : ∀ {a b} → a ≡ b → isG1 a ≡ isG1 b
isG1-cong refl = refl

------------------------------------------------------------------------
-- Send classifies the checked grade. g1 moves. ω and intervals copy.
-- Point 0 is not sendable.
------------------------------------------------------------------------

data Kind : Set where
  Kmove Kcopy : Kind

kind : Grade → Maybe Kind
kind (pt (fin zero))    = nothing
kind (pt (fin (suc _))) = just Kmove
kind (pt inf)           = just Kcopy
kind (iv _ _)           = just Kcopy

kind-g1 : kind g1 ≡ just Kmove
kind-g1 = refl

copy-not-g1 : ∀ g → kind g ≡ just Kcopy → isG1 g ≡ false
copy-not-g1 (pt (fin zero))          ()
copy-not-g1 (pt (fin (suc _)))       ()
copy-not-g1 (pt inf)                 refl = refl
copy-not-g1 (iv _ _)                 refl = refl

------------------------------------------------------------------------
-- One computational use. Nothing on a zero residual.
------------------------------------------------------------------------

data Spent (c : Grade) : Set where
  spent : (r : Grade) → Kept r c → Spent c

spend : ∀ {r c} → Kept r c → Maybe (Spent c)
spend (fin-kept {k = zero}  _) = nothing
spend (fin-kept {k = suc k} {n} le) =
  just (spent (pt (fin k)) (fin-kept (lower le)))
spend ω-kept = just (spent gω ω-kept)
spend (iv-kept {a} {b}) = just (spent (iv a b) iv-kept)

spend-zero : ∀ {r c} (k : Kept r c) → r ≡ g0 → spend k ≡ nothing
spend-zero (fin-kept {k = zero} _) refl = refl
spend-zero (fin-kept {k = suc _} _) ()
spend-zero ω-kept ()
spend-zero iv-kept ()

spend-finite : ∀ {k n} (le : suc k ≤ n) →
  spend (fin-kept {k = suc k} {n} le) ≡
  just (spent (pt (fin k)) (fin-kept (lower le)))
spend-finite _ = refl

spend-ω : spend ω-kept ≡ just (spent gω ω-kept)
spend-ω = refl

spend-iv : ∀ {a b} → spend (iv-kept {a} {b}) ≡ just (spent (iv a b) iv-kept)
spend-iv = refl

-- muro refuses a computational use of grade 0 in run mode. The runtime
-- theorem `grade0-not-dereferenced` is the same fact on a step.
checker-erased : grade-erased-first ≡ grade-erased-first
checker-erased = refl

-- Run is the only mode in which v0 dereferences. The names are in scope
-- so the step relation can mention them without a second import cycle.
run-mode : Mode
run-mode = run
