------------------------------------------------------------------------
-- Shared heap. Objects are scalar cells. References live in processes
-- and in messages; this module is the cell, the reference, and the
-- counting lemmas those references need.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Heap where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; _≡ᵇ_; _<ᵇ_)
open import Data.Product.Base using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong)

open import Muro.Grade using (Grade; g0; g1; _≤ᵍ_; GTm)

open import MuroBeam.Grade using
  ( Kept; selfKept; kept→≤ᵍ
  ; isZeroGrade; isG1; isG1-cong
  ; Spent; spent; spend; spend-zero
  )
open import MuroBeam.Lib using
  ( ⊥-elim
  ; ≤-trans; ≡ᵇ-cong; <≡ᵇ-false
  ; +-assoc; +-swap; +-identityʳ; +-zero
  ; ext; ext-cong; ext-0
  ; ∨-assoc; ∨-swap; ∨-falseʳ; ∧-cong
  ; lookup; removeAt; mapRem
  ; ++-assoc
  )

------------------------------------------------------------------------
-- Cells
------------------------------------------------------------------------

data Status : Set where
  live free : Status

------------------------------------------------------------------------
-- A root: checked grade, residual grade, and the inequality.
------------------------------------------------------------------------

record Ref : Set where
  constructor ref
  field
    obj      : ℕ
    checked  : Grade
    residual : Grade
    kept     : Kept residual checked

open Ref public

------------------------------------------------------------------------
-- Payloads. nat is copied on deref. suc↑ and clo hold child Refs.
-- The child index of a successor is obj of its Ref.
------------------------------------------------------------------------

data Val : Set where
  nat  : ℕ → Val
  suc↑ : Ref → Val
  clo  : List Ref → Σ ℕ (λ n → GTm n) → Val

kids : Val → List Ref
kids (nat _)    = []
kids (suc↑ r)   = r ∷ []
kids (clo rs _) = rs

kidsBelow : ℕ → List Ref → Bool
kidsBelow _ []       = true
kidsBelow n (r ∷ rs) = (obj r <ᵇ n) ∧ kidsBelow n rs

childrenBelow : ℕ → Val → Bool
childrenBelow _ (nat _)    = true
childrenBelow n (suc↑ r)   = obj r <ᵇ n
childrenBelow n (clo rs _) = kidsBelow n rs

record Obj : Set where
  constructor cell
  field
    payload : Val
    status  : Status

open Obj public

edgeRefs : List Obj → List Ref
edgeRefs []       = []
edgeRefs (o ∷ os) = kids (payload o) ++ edgeRefs os

edgeRefs-++ : ∀ xs ys → edgeRefs (xs ++ ys) ≡ edgeRefs xs ++ edgeRefs ys
edgeRefs-++ []       ys = refl
edgeRefs-++ (o ∷ os) ys rewrite edgeRefs-++ os ys =
  sym (++-assoc (kids (payload o)) (edgeRefs os) (edgeRefs ys))

------------------------------------------------------------------------
-- Ordered: every child index is strictly below its parent.
------------------------------------------------------------------------

data AllBelow (n : ℕ) : List Ref → Set where
  abnil  : AllBelow n []
  abcons : ∀ {r rs} → obj r < n → AllBelow n rs → AllBelow n (r ∷ rs)

data Below (n : ℕ) : Val → Set where
  b-nat : ∀ {k} → Below n (nat k)
  b-suc : ∀ {r} → obj r < n → Below n (suc↑ r)
  b-clo : ∀ {rs tm} → AllBelow n rs → Below n (clo rs tm)

Ordered : List Obj → Set
Ordered h = ∀ i o → lookup h i ≡ just o → Below i (payload o)

ordered-nil : Ordered []
ordered-nil i o ()

residual-inv : Ref → Set
residual-inv r = (residual r ≤ᵍ checked r) ≡ true

ref-inv : ∀ r → residual-inv r
ref-inv r = kept→≤ᵍ (kept r)

applySpend : ℕ → (c : Grade) → Maybe (Spent c) → Maybe Ref
applySpend o c nothing              = nothing
applySpend o c (just (spent r' k')) = just (ref o c r' k')

spendRef : Ref → Maybe Ref
spendRef (ref o c r k) = applySpend o c (spend k)

spendRef-zero : ∀ r → residual r ≡ g0 → spendRef r ≡ nothing
spendRef-zero (ref o c r k) eq rewrite spend-zero k eq = refl

spendRef-obj : ∀ r r' → spendRef r ≡ just r' → obj r' ≡ obj r
spendRef-obj (ref o c _ k) r' eq = body (spend k) eq
  where
  body : (s : Maybe (Spent c)) → applySpend o c s ≡ just r' → obj r' ≡ o
  body nothing ()
  body (just (spent _ _)) refl = refl

spendRef-checked : ∀ r r' → spendRef r ≡ just r' → checked r' ≡ checked r
spendRef-checked (ref o c _ k) r' eq = body (spend k) eq
  where
  body : (s : Maybe (Spent c)) → applySpend o c s ≡ just r' → checked r' ≡ c
  body nothing ()
  body (just (spent _ _)) refl = refl

------------------------------------------------------------------------
-- How many references point at an object, and whether one of them is g1.
------------------------------------------------------------------------

count : ℕ → List Ref → ℕ
count i []       = zero
count i (r ∷ rs) = ext (obj r ≡ᵇ i) + count i rs

hasG1 : ℕ → List Ref → Bool
hasG1 i []       = false
hasG1 i (r ∷ rs) = ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ∨ hasG1 i rs

-- A grade-1 reference is the only reference to its object.
Grade1Unique : List Ref → Set
Grade1Unique rs = ∀ i → hasG1 i rs ≡ true → count i rs ≡ 1

uniq-nil : Grade1Unique []
uniq-nil i ()

same-unique : ∀ {rs rs'} →
  (∀ i → count i rs' ≡ count i rs) →
  (∀ i → hasG1 i rs' ≡ hasG1 i rs) →
  Grade1Unique rs → Grade1Unique rs'
same-unique cq hq u i h rewrite hq i | cq i = u i h

------------------------------------------------------------------------
-- Every referenced index lies in the heap.
------------------------------------------------------------------------

data Bound : ℕ → List Ref → Set where
  bnil  : ∀ {n} → Bound n []
  bcons : ∀ {n r rs} → obj r < n → Bound n rs → Bound n (r ∷ rs)

bound-++ : ∀ {n xs ys} → Bound n xs → Bound n ys → Bound n (xs ++ ys)
bound-++ bnil          ys = ys
bound-++ (bcons lt xs) ys = bcons lt (bound-++ xs ys)

obj≠ : ∀ o {n i} → suc o ≤ n → n ≤ i → (o ≡ᵇ i) ≡ false
obj≠ o o<n ni = <≡ᵇ-false (≤-trans o<n ni)

bound-count0 : ∀ {n rs} → Bound n rs → ∀ i → n ≤ i → count i rs ≡ 0
bound-count0 bnil i _ = refl
bound-count0 (bcons {r = r} lt rest) i n≤i
  rewrite obj≠ (obj r) lt n≤i | bound-count0 rest i n≤i = refl

count0-has : ∀ i rs → count i rs ≡ 0 → hasG1 i rs ≡ false
count0-has i []       _  = refl
count0-has i (r ∷ rs) eq with +-zero (ext (obj r ≡ᵇ i)) (count i rs) eq
... | eqa , eqr rewrite ext-0 (obj r ≡ᵇ i) eqa | count0-has i rs eqr = refl

------------------------------------------------------------------------
-- List surgery on references.
------------------------------------------------------------------------

count-++ : ∀ i xs ys → count i (xs ++ ys) ≡ count i xs + count i ys
count-++ i []       ys = refl
count-++ i (r ∷ xs) ys
  rewrite count-++ i xs ys
        | sym (+-assoc (ext (obj r ≡ᵇ i)) (count i xs) (count i ys)) = refl

has-++ : ∀ i xs ys → hasG1 i (xs ++ ys) ≡ (hasG1 i xs ∨ hasG1 i ys)
has-++ i []       ys = refl
has-++ i (r ∷ xs) ys
  rewrite has-++ i xs ys =
  sym (∨-assoc ((obj r ≡ᵇ i) ∧ isG1 (checked r)) (hasG1 i xs) (hasG1 i ys))

count-snoc : ∀ i xs r →
  count i (xs ++ (r ∷ [])) ≡ count i xs + ext (obj r ≡ᵇ i)
count-snoc i xs r =
  trans (count-++ i xs (r ∷ []))
        (cong (count i xs +_) (+-identityʳ (ext (obj r ≡ᵇ i))))

has-snoc : ∀ i xs r →
  hasG1 i (xs ++ (r ∷ [])) ≡ (hasG1 i xs ∨ ((obj r ≡ᵇ i) ∧ isG1 (checked r)))
has-snoc i xs r rewrite has-++ i xs (r ∷ []) =
  cong (hasG1 i xs ∨_) (∨-falseʳ ((obj r ≡ᵇ i) ∧ isG1 (checked r)))

removeAt-count : ∀ i n xs r ys →
  removeAt n xs ≡ just (r , ys) →
  count i xs ≡ ext (obj r ≡ᵇ i) + count i ys
removeAt-count i n xs r ys eq = go n xs r ys eq
  where
  go : ∀ n xs r ys → removeAt n xs ≡ just (r , ys) →
       count i xs ≡ ext (obj r ≡ᵇ i) + count i ys
  go n [] r ys ()
  go zero (x ∷ xs) .x .xs refl = refl
  go (suc n) (x ∷ xs) r ys eq = step (removeAt n xs) eq refl
    where
    step : (m : Maybe (Ref × List Ref)) → mapRem x m ≡ just (r , ys) →
           removeAt n xs ≡ m →
           count i (x ∷ xs) ≡ ext (obj r ≡ᵇ i) + count i ys
    step nothing () _
    step (just (z , zs)) refl eqm =
      trans (cong (ext (obj x ≡ᵇ i) +_) (go n xs z zs eqm))
            (+-swap (ext (obj x ≡ᵇ i)) (ext (obj z ≡ᵇ i)) (count i zs))

removeAt-has : ∀ i n xs r ys →
  removeAt n xs ≡ just (r , ys) →
  hasG1 i xs ≡ ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ∨ hasG1 i ys
removeAt-has i n xs r ys eq = go n xs r ys eq
  where
  go : ∀ n xs r ys → removeAt n xs ≡ just (r , ys) →
       hasG1 i xs ≡ ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ∨ hasG1 i ys
  go n [] r ys ()
  go zero (x ∷ xs) .x .xs refl = refl
  go (suc n) (x ∷ xs) r ys eq = step (removeAt n xs) eq refl
    where
    step : (m : Maybe (Ref × List Ref)) → mapRem x m ≡ just (r , ys) →
           removeAt n xs ≡ m →
           hasG1 i (x ∷ xs) ≡ ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ∨ hasG1 i ys
    step nothing () _
    step (just (z , zs)) refl eqm rewrite go n xs z zs eqm =
      ∨-swap ((obj x ≡ᵇ i) ∧ isG1 (checked x))
             ((obj z ≡ᵇ i) ∧ isG1 (checked z))
             (hasG1 i zs)

repl : ℕ → Ref → List Ref → List Ref
repl _ _ []             = []
repl zero    r (_ ∷ xs) = r ∷ xs
repl (suc n) r (x ∷ xs) = x ∷ repl n r xs

repl-count : ∀ i n xs r r0 →
  lookup xs n ≡ just r0 →
  obj r ≡ obj r0 →
  count i (repl n r xs) ≡ count i xs
repl-count i n xs r r0 eq eo = go n xs r0 eq eo
  where
  go : ∀ n xs r0 → lookup xs n ≡ just r0 → obj r ≡ obj r0 →
       count i (repl n r xs) ≡ count i xs
  go n [] r0 () _
  go zero (x ∷ xs) .x refl refl = refl
  go (suc n) (x ∷ xs) r0 eq eo =
    cong (ext (obj x ≡ᵇ i) +_) (go n xs r0 eq eo)

repl-has : ∀ i n xs r r0 →
  lookup xs n ≡ just r0 →
  obj r ≡ obj r0 →
  checked r ≡ checked r0 →
  hasG1 i (repl n r xs) ≡ hasG1 i xs
repl-has i n xs r r0 eq eo ec = go n xs r0 eq eo ec
  where
  go : ∀ n xs r0 → lookup xs n ≡ just r0 → obj r ≡ obj r0 → checked r ≡ checked r0 →
       hasG1 i (repl n r xs) ≡ hasG1 i xs
  go n [] r0 () _ _
  go zero (x ∷ xs) .x refl refl refl = refl
  go (suc n) (x ∷ xs) r0 eq eo ec =
    cong (λ b → ((obj x ≡ᵇ i) ∧ isG1 (checked x)) ∨ b) (go n xs r0 eq eo ec)

bound-repl : ∀ {n} i xs r r0 →
  Bound n xs →
  lookup xs i ≡ just r0 →
  obj r ≡ obj r0 →
  Bound n (repl i r xs)
bound-repl {n} i xs r r0 bd eq eo = go i xs bd eq eo
  where
  go : ∀ i xs → Bound n xs → lookup xs i ≡ just r0 → obj r ≡ obj r0 →
       Bound n (repl i r xs)
  go i [] bd () _
  go zero (x ∷ xs) (bcons lt rest) refl refl = bcons lt rest
  go (suc i) (x ∷ xs) (bcons lt rest) eq eo = bcons lt (go i xs rest eq eo)

bound-remove : ∀ {n} i xs r ys →
  Bound n xs →
  removeAt i xs ≡ just (r , ys) →
  Bound n ys × obj r < n
bound-remove {n} i xs r ys bd eq = go i xs r ys bd eq
  where
  go : ∀ i xs r ys → Bound n xs → removeAt i xs ≡ just (r , ys) →
       Bound n ys × obj r < n
  go i [] r ys bd ()
  go zero (y ∷ ys') .y .ys' (bcons lt rest) refl = rest , lt
  go (suc i) (x ∷ xs) r ys (bcons lt rest) eq = step (removeAt i xs) eq refl rest
    where
    step : (m : Maybe (Ref × List Ref)) → mapRem x m ≡ just (r , ys) →
           removeAt i xs ≡ m → Bound n xs → Bound n ys × obj r < n
    step nothing () _ _
    step (just (z , zs)) refl eqm rest' with go i xs z zs rest' eqm
    ... | bzs , oz = bcons lt bzs , oz
