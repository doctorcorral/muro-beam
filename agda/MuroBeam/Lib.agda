------------------------------------------------------------------------
-- Small lemmas. Kept here so the book does not import Data.Nat.Properties.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Lib where

open import Data.Bool.Base using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤ᵇ_; _≡ᵇ_; _<ᵇ_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong)

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

¬_ : Set → Set
¬ A = A → ⊥

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

infix 3 _≢_

------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step z≤n       = z≤n
≤-step (s≤s le)  = s≤s (≤-step le)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n       _         = z≤n
≤-trans (s≤s ab)  (s≤s bc)  = s≤s (≤-trans ab bc)

-- The only proof of suc k ≤ n is s≤s, so one clause covers it.
lower : ∀ {k n} → suc k ≤ n → k ≤ n
lower (s≤s le) = ≤-step le

+-identityʳ : ∀ a → a + zero ≡ a
+-identityʳ zero    = refl
+-identityʳ (suc a) rewrite +-identityʳ a = refl

+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b rewrite +-suc a b = refl

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero    b rewrite +-identityʳ b = refl
+-comm (suc a) b rewrite +-comm a b | sym (+-suc b a) = refl

+-swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
+-swap a b c =
  trans (sym (+-assoc a b c))
        (trans (cong (λ z → z + c) (+-comm a b))
               (+-assoc b a c))

+-zero : ∀ a b → a + b ≡ 0 → a ≡ 0 × b ≡ 0
+-zero zero    zero    refl = refl , refl
+-zero zero    (suc _) ()
+-zero (suc _) _       ()

suc≰id : ∀ n → suc n ≤ n → ⊥
suc≰id zero    ()
suc≰id (suc n) (s≤s le) = suc≰id n le

≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

≡ᵇ-cong : ∀ a b i → a ≡ b → (a ≡ᵇ i) ≡ (b ≡ᵇ i)
≡ᵇ-cong a .a i refl = refl

≡ᵇ-sym : ∀ a b → (a ≡ᵇ b) ≡ (b ≡ᵇ a)
≡ᵇ-sym zero    zero    = refl
≡ᵇ-sym zero    (suc _) = refl
≡ᵇ-sym (suc _) zero    = refl
≡ᵇ-sym (suc a) (suc b) = ≡ᵇ-sym a b

≡ᵇ-sound : ∀ m n → (m ≡ᵇ n) ≡ true → m ≡ n
≡ᵇ-sound zero    zero    refl = refl
≡ᵇ-sound zero    (suc _) ()
≡ᵇ-sound (suc _) zero    ()
≡ᵇ-sound (suc m) (suc n) eq   = cong suc (≡ᵇ-sound m n eq)

<≡ᵇ-false : ∀ {m n} → suc m ≤ n → (m ≡ᵇ n) ≡ false
<≡ᵇ-false {m} {n} lt with m ≡ᵇ n in eq
... | true  = ⊥-elim (suc≰id n (subst≤ (≡ᵇ-sound m n eq) lt))
  where
  subst≤ : ∀ {m n i} → m ≡ i → suc m ≤ n → suc i ≤ n
  subst≤ refl le = le
... | false = refl

-- m ≤ n implies the boolean order used by Muro.Grade.
<ᵇ-complete : ∀ {m n} → m ≤ n → (m <ᵇ suc n) ≡ true
<ᵇ-complete {zero}  {n}     z≤n      = refl
<ᵇ-complete {suc m} {suc n} (s≤s le) = <ᵇ-complete {m} {n} le

≤ᵇ-complete : ∀ {m n} → m ≤ n → (m ≤ᵇ n) ≡ true
≤ᵇ-complete z≤n       = refl
≤ᵇ-complete (s≤s le)  = <ᵇ-complete le

plus : ℕ → ℕ → ℕ
plus zero    n = n
plus (suc m) n = suc (plus m n)

plus-suc : ∀ i n → plus i (suc n) ≡ suc (plus i n)
plus-suc zero    n = refl
plus-suc (suc i) n rewrite plus-suc i n = refl

plus-zero : ∀ i → plus i zero ≡ i
plus-zero zero    = refl
plus-zero (suc i) rewrite plus-zero i = refl

------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

∧-both : ∀ {x y} → x ≡ true → y ≡ true → (x ∧ y) ≡ true
∧-both refl refl = refl

∧-cong : ∀ {a b c d} → a ≡ b → c ≡ d → (a ∧ c) ≡ (b ∧ d)
∧-cong refl refl = refl

∨-comm : ∀ a b → a ∨ b ≡ b ∨ a
∨-comm true  true  = refl
∨-comm true  false = refl
∨-comm false true  = refl
∨-comm false false = refl

∨-assoc : ∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
∨-assoc true  b c = refl
∨-assoc false b c = refl

∨-swap : ∀ a b c → a ∨ (b ∨ c) ≡ b ∨ (a ∨ c)
∨-swap a b c =
  trans (sym (∨-assoc a b c))
        (trans (cong (λ z → z ∨ c) (∨-comm a b))
               (∨-assoc b a c))

∨-trueʳ : ∀ b → (b ∨ true) ≡ true
∨-trueʳ true  = refl
∨-trueʳ false = refl

∨-falseʳ : ∀ b → (b ∨ false) ≡ b
∨-falseʳ true  = refl
∨-falseʳ false = refl

∨-congʳ : ∀ {a b c} → b ≡ c → (a ∨ b) ≡ (a ∨ c)
∨-congʳ refl = refl

ext : Bool → ℕ
ext true  = 1
ext false = 0

ext-cong : ∀ {a b} → a ≡ b → ext a ≡ ext b
ext-cong refl = refl

ext-1 : ∀ b → ext b ≡ 1 → b ≡ true
ext-1 true  refl = refl
ext-1 false ()

ext-0 : ∀ b → ext b ≡ 0 → b ≡ false
ext-0 false refl = refl
ext-0 true  ()

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

lookup : ∀ {A : Set} → List A → ℕ → Maybe A
lookup []       _       = nothing
lookup (x ∷ _)  zero    = just x
lookup (_ ∷ xs) (suc n) = lookup xs n

mapRem : ∀ {A : Set} → A → Maybe (A × List A) → Maybe (A × List A)
mapRem _ nothing         = nothing
mapRem y (just (z , zs)) = just (z , y ∷ zs)

removeAt : ∀ {A : Set} → ℕ → List A → Maybe (A × List A)
removeAt _       []       = nothing
removeAt zero    (x ∷ xs) = just (x , xs)
removeAt (suc n) (x ∷ xs) = mapRem x (removeAt n xs)

mapCons : ∀ {A : Set} → A → Maybe (List A) → Maybe (List A)
mapCons _ nothing   = nothing
mapCons y (just ys) = just (y ∷ ys)

update : ∀ {A : Set} → ℕ → A → List A → Maybe (List A)
update _       _ []       = nothing
update zero    a (_ ∷ xs) = just (a ∷ xs)
update (suc n) a (x ∷ xs) = mapCons x (update n a xs)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ []       ys = refl
length-++ (x ∷ xs) ys rewrite length-++ xs ys = refl
