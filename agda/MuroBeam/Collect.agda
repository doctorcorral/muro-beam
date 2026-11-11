------------------------------------------------------------------------
-- Total ordered collection.
--
-- Marks are seeded from roots, mailboxes, environments, and frames whose
-- residual is not the point g0. One structural pass then walks from the
-- highest index down and marks a child only when its index is lower and
-- its residual is not g0. A slot that is not marked is freed and cleared.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Collect where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (Mode; run)
open import Muro.Grade using (Grade; g0)
open import MuroBeam.Grade using (isZeroGrade)
open import MuroBeam.Heap using
  ( Obj; cell; Status; live; free; Ref; residual; obj; status; payload
  ; Val; nat; kids; edgeRefs )
open import MuroBeam.Lib using
  ( ⊥; ⊥-elim; lookup; ≡ᵇ-refl; ∨-assoc; ∨-trueʳ; ∨-false; ∧-split; ∧-trueˡ
  ; ≤-refl; ≤-trans; lower; +-identityʳ; +-suc; ++-assoc
  ; lookup-<; In; in-here; in-there; ltᵇ-sound; ltᵇ-complete
  ; <+suc )
open import MuroBeam.Process using
  ( Proc; proc; PState; Msg; msg; Sys; sys; heap; procs; roots; inbox
  ; refsOf; liveRefs; ctlRefsPs; refsPs; AllInv; refs-inv
  ; deref; send; recv; alloc; reuse; eval1 )

open Obj public

------------------------------------------------------------------------
-- Keepers: residual is not the point g0.
------------------------------------------------------------------------

anyKeeper : ℕ → List Ref → Bool
anyKeeper i []       = false
anyKeeper i (r ∷ rs) =
  ((obj r ≡ᵇ i) ∧ not (isZeroGrade (residual r))) ∨ anyKeeper i rs

any-++ : ∀ i xs ys → anyKeeper i (xs ++ ys) ≡ (anyKeeper i xs ∨ anyKeeper i ys)
any-++ i []       ys = refl
any-++ i (r ∷ xs) ys rewrite any-++ i xs ys =
  sym (∨-assoc ((obj r ≡ᵇ i) ∧ not (isZeroGrade (residual r))) (anyKeeper i xs) (anyKeeper i ys))

keeper : ∀ {r rs i} → In r rs → obj r ≡ i → isZeroGrade (residual r) ≡ false →
         anyKeeper i rs ≡ true
keeper {r} (in-here {xs}) refl z = here
  where
  here : anyKeeper (obj r) (r ∷ xs) ≡ true
  here rewrite ≡ᵇ-refl (obj r) | z = refl
keeper (in-there inn) eq z rewrite keeper inn eq z = ∨-trueʳ _

------------------------------------------------------------------------
-- Boolean vector, updated only from false to true.
------------------------------------------------------------------------

lookupB : List Bool → ℕ → Bool
lookupB []      _       = false
lookupB (b ∷ _) zero    = b
lookupB (_ ∷ bs) (suc n) = lookupB bs n

setBit : ℕ → List Bool → List Bool
setBit _ []             = []
setBit zero    (_ ∷ bs) = true ∷ bs
setBit (suc n) (b ∷ bs) = b ∷ setBit n bs

true≢false : true ≡ false → ⊥
true≢false ()

set-mono : ∀ j bs i → lookupB bs i ≡ true → lookupB (setBit j bs) i ≡ true
set-mono j [] i ()
set-mono zero    (_ ∷ _)  zero    _  = refl
set-mono zero    (_ ∷ bs) (suc i) eq = eq
set-mono (suc j) (_ ∷ bs) zero    eq = eq
set-mono (suc j) (_ ∷ bs) (suc i) eq = set-mono j bs i eq

setBit-high : ∀ j bs i → j < i → lookupB (setBit j bs) i ≡ lookupB bs i
setBit-high _ [] _ _ = refl
setBit-high zero    (_ ∷ _)  zero    ()
setBit-high zero    (_ ∷ bs) (suc _) _  = refl
setBit-high (suc _) (_ ∷ _)  zero    ()
setBit-high (suc j) (_ ∷ bs) (suc i) (s≤s lt) = setBit-high j bs i lt

setBit-≠ : ∀ j bs i → (j ≡ᵇ i) ≡ false → lookupB (setBit j bs) i ≡ lookupB bs i
setBit-≠ _ [] _ _ = refl
setBit-≠ zero    (_ ∷ _)  zero    ()
setBit-≠ zero    (_ ∷ bs) (suc _) _  = refl
setBit-≠ (suc _) (_ ∷ bs) zero    _  = refl
setBit-≠ (suc j) (_ ∷ bs) (suc i) eq = setBit-≠ j bs i eq

setBit-at : ∀ j bs → j < length bs → lookupB (setBit j bs) j ≡ true
setBit-at _ [] ()
setBit-at zero    (_ ∷ _)  _        = refl
setBit-at (suc j) (_ ∷ bs) (s≤s lt) = setBit-at j bs lt

length-setBit : ∀ j bs → length (setBit j bs) ≡ length bs
length-setBit _ []             = refl
length-setBit zero    (_ ∷ _)  = refl
length-setBit (suc j) (_ ∷ bs) rewrite length-setBit j bs = refl

markOn : Bool → ℕ → List Bool → List Bool
markOn true  j bs = setBit j bs
markOn false _ bs = bs

markOne : ℕ → Ref → List Bool → List Bool
markOne p r bs = markOn ((obj r <ᵇ p) ∧ not (isZeroGrade (residual r))) (obj r) bs

one-stable : ∀ p r bs i → p ≤ i → lookupB (markOne p r bs) i ≡ lookupB bs i
one-stable p r bs i le with (obj r <ᵇ p) ∧ not (isZeroGrade (residual r)) in eq
... | false = refl
... | true  = setBit-high (obj r) bs i (≤-trans (and-lt eq) le)
  where
  and-lt : ((obj r <ᵇ p) ∧ not (isZeroGrade (residual r))) ≡ true → obj r < p
  and-lt e = ltᵇ-sound (obj r) p (proj₁ (∧-split e))

one-mono : ∀ p r bs i → lookupB bs i ≡ true → lookupB (markOne p r bs) i ≡ true
one-mono p r bs i eq with (obj r <ᵇ p) ∧ not (isZeroGrade (residual r))
... | false = eq
... | true  = set-mono (obj r) bs i eq

length-markOne : ∀ p r bs → length (markOne p r bs) ≡ length bs
length-markOne p r bs with (obj r <ᵇ p) ∧ not (isZeroGrade (residual r))
... | false = refl
... | true  = length-setBit (obj r) bs

markKids : ℕ → List Ref → List Bool → List Bool
markKids _ []       bs = bs
markKids p (r ∷ rs) bs = markKids p rs (markOne p r bs)

kids-stable : ∀ p rs bs i → p ≤ i → lookupB (markKids p rs bs) i ≡ lookupB bs i
kids-stable _ []       bs _ _  = refl
kids-stable p (r ∷ rs) bs i le =
  trans (kids-stable p rs (markOne p r bs) i le) (one-stable p r bs i le)

kids-mono : ∀ p rs bs i → lookupB bs i ≡ true → lookupB (markKids p rs bs) i ≡ true
kids-mono _ []       bs _ eq = eq
kids-mono p (r ∷ rs) bs i eq = kids-mono p rs (markOne p r bs) i (one-mono p r bs i eq)

length-markKids : ∀ p rs bs → length (markKids p rs bs) ≡ length bs
length-markKids _ []       bs = refl
length-markKids p (r ∷ rs) bs
  rewrite length-markKids p rs (markOne p r bs)
        | length-markOne p r bs = refl

under : ∀ {m n k} → m < n → n ≡ k → m < k
under lt refl = lt

markKids-set : ∀ p rs bs r →
  In r rs →
  obj r < p →
  isZeroGrade (residual r) ≡ false →
  obj r < length bs →
  lookupB (markKids p rs bs) (obj r) ≡ true
markKids-set p (r ∷ rs) bs .r in-here lt z len =
  kids-mono p rs (markOne p r bs) (obj r) (one-set p r bs lt z len)
  where
  one-set : ∀ p' r' bs' →
            obj r' < p' →
            isZeroGrade (residual r') ≡ false →
            obj r' < length bs' →
            lookupB (markOne p' r' bs') (obj r') ≡ true
  one-set p' r' bs' lt' z' len' with (obj r' <ᵇ p') ∧ not (isZeroGrade (residual r')) in eq
  ... | true  = setBit-at (obj r') bs' len'
  ... | false =
    ⊥-elim (true≢false (trans (sym (∧-both' lt' z')) eq))
    where
    nz : not (isZeroGrade (residual r')) ≡ true
    nz rewrite z' = refl
    ∧-both' : obj r' < p' → isZeroGrade (residual r') ≡ false →
              ((obj r' <ᵇ p') ∧ not (isZeroGrade (residual r'))) ≡ true
    ∧-both' lt'' _ rewrite ltᵇ-complete lt'' | nz = refl
markKids-set p (y ∷ rs) bs r (in-there inn) lt z len =
  markKids-set p rs (markOne p y bs) r inn lt z
    (under len (sym (length-markOne p y bs)))

one-no : ∀ slot p r bs →
  lookupB bs slot ≡ false →
  ((obj r ≡ᵇ slot) ∧ not (isZeroGrade (residual r))) ≡ false →
  lookupB (markOne p r bs) slot ≡ false
one-no slot p r bs ez hf with (obj r <ᵇ p) ∧ not (isZeroGrade (residual r)) in eq
... | false = ez
... | true with obj r ≡ᵇ slot in eb
...   | false = trans (setBit-≠ (obj r) bs slot eb) ez
...   | true  = ⊥-elim (true≢false (trans (sym (proj₂ (∧-split eq))) hf))

markKids-no : ∀ slot p rs bs →
  lookupB bs slot ≡ false →
  anyKeeper slot rs ≡ false →
  lookupB (markKids p rs bs) slot ≡ false
markKids-no _ _ [] bs ez _ = ez
markKids-no slot p (r ∷ rs) bs ez na =
  let hf , tf = ∨-false _ _ na in
  markKids-no slot p rs (markOne p r bs) (one-no slot p r bs ez hf) tf

------------------------------------------------------------------------
-- Downward pass. The tail (higher indices) is processed first.
------------------------------------------------------------------------

markIf : Bool → ℕ → List Ref → List Bool → List Bool
markIf true  i rs bs = markKids i rs bs
markIf false _ _  bs = bs

go : List Obj → ℕ → List Bool → List Bool
go []       _ bs = bs
go (o ∷ os) i bs =
  markIf (lookupB (go os (suc i) bs) i) i (kids (payload o)) (go os (suc i) bs)

go-mono : ∀ os b bs i → lookupB bs i ≡ true → lookupB (go os b bs) i ≡ true
go-mono []       _ bs i eq = eq
go-mono (o ∷ os) b bs i eq = onBit (lookupB (go os (suc b) bs) b) refl
  where
  onBit : (bit : Bool) → lookupB (go os (suc b) bs) b ≡ bit →
          lookupB (go (o ∷ os) b bs) i ≡ true
  onBit bit eqb =
    subst (λ c → lookupB (markIf c b (kids (payload o)) (go os (suc b) bs)) i ≡ true)
          (sym eqb) (step bit)
    where
    step : (c : Bool) →
           lookupB (markIf c b (kids (payload o)) (go os (suc b) bs)) i ≡ true
    step false = go-mono os (suc b) bs i eq
    step true  = kids-mono b (kids (payload o)) (go os (suc b) bs) i
                   (go-mono os (suc b) bs i eq)

parent-bit : ∀ o os j bs →
  lookupB (go (o ∷ os) j bs) j ≡ lookupB (go os (suc j) bs) j
parent-bit o os j bs = onBit (lookupB (go os (suc j) bs) j) refl
  where
  onBit : (bit : Bool) → lookupB (go os (suc j) bs) j ≡ bit →
          lookupB (go (o ∷ os) j bs) j ≡ bit
  onBit bit eq =
    subst (λ c → lookupB (markIf c j (kids (payload o)) (go os (suc j) bs)) j ≡ bit)
          (sym eq) (step bit eq)
    where
    step : (c : Bool) → lookupB (go os (suc j) bs) j ≡ bit →
           lookupB (markIf c j (kids (payload o)) (go os (suc j) bs)) j ≡ bit
    step false eq' = eq'
    step true  eq' =
      trans (kids-stable j (kids (payload o)) (go os (suc j) bs) j ≤-refl) eq'

go-stable : ∀ os b bs i → b + length os ≤ i → lookupB (go os b bs) i ≡ lookupB bs i
go-stable []       _ _  _ _  = refl
go-stable (o ∷ os) b bs i le =
  trans (ifHigh (lookupB (go os (suc b) bs) b))
        (go-stable os (suc b) bs i (shift le))
  where
  shift : b + suc (length os) ≤ i → suc b + length os ≤ i
  shift le' rewrite +-suc b (length os) = le'
  ifHigh : (bit : Bool) →
           lookupB (markIf bit b (kids (payload o)) (go os (suc b) bs)) i
             ≡ lookupB (go os (suc b) bs) i
  ifHigh false = refl
  ifHigh true  =
    kids-stable b (kids (payload o)) (go os (suc b) bs) i
      (lower (≤-trans (<+suc b (length os)) le))

go-++ : ∀ xs ys b bs →
  go (xs ++ ys) b bs ≡ go xs b (go ys (b + length xs) bs)
go-++ []       ys b bs rewrite +-identityʳ b = refl
go-++ (x ∷ xs) ys b bs rewrite go-++ xs ys (suc b) bs | +-suc b (length xs) = refl

go-no : ∀ os b bs slot →
  anyKeeper slot (edgeRefs os) ≡ false →
  lookupB bs slot ≡ false →
  lookupB (go os b bs) slot ≡ false
go-no []       _ _  _    _  ez = ez
go-no (o ∷ os) b bs slot na ez =
  step (lookupB (go os (suc b) bs) b) ih hf
  where
  splitKids : anyKeeper slot (kids (payload o)) ≡ false × anyKeeper slot (edgeRefs os) ≡ false
  splitKids = ∨-false _ _ (trans (sym (any-++ slot (kids (payload o)) (edgeRefs os))) na)
  hf : anyKeeper slot (kids (payload o)) ≡ false
  hf = proj₁ splitKids
  tf : anyKeeper slot (edgeRefs os) ≡ false
  tf = proj₂ splitKids
  ih : lookupB (go os (suc b) bs) slot ≡ false
  ih = go-no os (suc b) bs slot tf ez
  step : (bit : Bool) →
         lookupB (go os (suc b) bs) slot ≡ false →
         anyKeeper slot (kids (payload o)) ≡ false →
         lookupB (markIf bit b (kids (payload o)) (go os (suc b) bs)) slot ≡ false
  step false ih' _   = ih'
  step true  ih' naK = markKids-no slot b (kids (payload o)) (go os (suc b) bs) ih' naK

------------------------------------------------------------------------
-- Seed from the live (non-edge) references.
------------------------------------------------------------------------

seedFrom : List Ref → ℕ → ℕ → List Bool
seedFrom _  _ zero    = []
seedFrom rs i (suc n) = anyKeeper i rs ∷ seedFrom rs (suc i) n

seed : List Ref → ℕ → List Bool
seed rs n = seedFrom rs zero n

seedFrom-at : ∀ rs b n i → i < n → lookupB (seedFrom rs b n) i ≡ anyKeeper (b + i) rs
seedFrom-at _  _ zero    _ ()
seedFrom-at rs b (suc n) zero    (s≤s z≤n) rewrite +-identityʳ b = refl
seedFrom-at rs b (suc n) (suc i) (s≤s lt)
  rewrite seedFrom-at rs (suc b) n i lt
        | +-suc b i = refl

seed-at : ∀ rs n i → i < n → lookupB (seed rs n) i ≡ anyKeeper i rs
seed-at rs n i lt = seedFrom-at rs zero n i lt

length-seedFrom : ∀ rs b n → length (seedFrom rs b n) ≡ n
length-seedFrom _ _ zero    = refl
length-seedFrom rs b (suc n) rewrite length-seedFrom rs (suc b) n = refl

length-seed : ∀ rs n → length (seed rs n) ≡ n
length-seed rs n = length-seedFrom rs zero n

length-go : ∀ os b bs → length (go os b bs) ≡ length bs
length-go []       _ _  = refl
length-go (o ∷ os) b bs = onBit (lookupB (go os (suc b) bs) b) refl
  where
  onBit : (bit : Bool) → lookupB (go os (suc b) bs) b ≡ bit →
          length (go (o ∷ os) b bs) ≡ length bs
  onBit bit eq =
    subst (λ c → length (markIf c b (kids (payload o)) (go os (suc b) bs)) ≡ length bs)
          (sym eq) (step bit)
    where
    step : (c : Bool) →
           length (markIf c b (kids (payload o)) (go os (suc b) bs)) ≡ length bs
    step false = length-go os (suc b) bs
    step true  rewrite length-markKids b (kids (payload o)) (go os (suc b) bs)
                     | length-go os (suc b) bs = refl

------------------------------------------------------------------------
-- Reach: a live root, message, environment, or frame, or a live edge
-- out of a reached higher index.
------------------------------------------------------------------------

data Reach (s : Sys) : ℕ → Set where
  fromLive : ∀ {r} →
             In r (liveRefs s) →
             isZeroGrade (residual r) ≡ false →
             Reach s (obj r)
  fromEdge : ∀ {j o r} →
             Reach s j →
             lookup (heap s) j ≡ just o →
             In r (kids (payload o)) →
             isZeroGrade (residual r) ≡ false →
             obj r < j →
             Reach s (obj r)

data Split (h : List Obj) (i : ℕ) (o : Obj) : Set where
  mkSplit : (pre post : List Obj) →
            h ≡ pre ++ o ∷ post →
            length pre ≡ i →
            Split h i o

getSplit : ∀ h i o → lookup h i ≡ just o → Split h i o
getSplit []       _ _ ()
getSplit (x ∷ xs) zero .x refl = mkSplit [] xs refl refl
getSplit (x ∷ xs) (suc i) o eq with getSplit xs i o eq
... | mkSplit pre post q len = mkSplit (x ∷ pre) post (cong (x ∷_) q) (cong suc len)

markVec : Sys → List Bool
markVec s = go (heap s) zero (seed (liveRefs s) (length (heap s)))

markBit : Sys → ℕ → Bool
markBit s i = lookupB (markVec s) i

child-marked : ∀ pre o post bs r →
  lookupB (go (pre ++ o ∷ post) zero bs) (length pre) ≡ true →
  In r (kids (payload o)) →
  isZeroGrade (residual r) ≡ false →
  obj r < length pre →
  obj r < length bs →
  lookupB (go (pre ++ o ∷ post) zero bs) (obj r) ≡ true
child-marked pre o post bs r hj inn z lt lenb =
  subst (λ v → lookupB v (obj r) ≡ true) (sym eq)
    (go-mono pre zero inner (obj r) inner-set)
  where
  j : ℕ
  j = length pre
  inner : List Bool
  inner = go (o ∷ post) j bs
  eq : go (pre ++ o ∷ post) zero bs ≡ go pre zero inner
  eq = go-++ pre (o ∷ post) zero bs
  seen : lookupB inner j ≡ true
  seen = trans (sym (go-stable pre zero inner j ≤-refl))
               (subst (λ v → lookupB v j ≡ true) eq hj)
  atPost : lookupB (go post (suc j) bs) j ≡ true
  atPost = trans (sym (parent-bit o post j bs)) seen
  inner-set : lookupB inner (obj r) ≡ true
  inner-set =
    subst (λ c → lookupB (markIf c j (kids (payload o)) (go post (suc j) bs)) (obj r) ≡ true)
          (sym atPost)
          (markKids-set j (kids (payload o)) (go post (suc j) bs) r inn lt z
            (under lenb (sym (length-go post (suc j) bs))))

reach→mark : ∀ s i → Reach s i → ∀ o → lookup (heap s) i ≡ just o → markBit s i ≡ true
reach→mark s .(obj r) (fromLive {r} inn z) o eq =
  go-mono (heap s) zero (seed (liveRefs s) (length (heap s))) (obj r)
    (trans (seed-at (liveRefs s) (length (heap s)) (obj r) lt) (keeper inn refl z))
  where
  lt : obj r < length (heap s)
  lt = lookup-< (heap s) (obj r) o eq
reach→mark s .(obj r) (fromEdge {j} {o = p} {r} rj lp inn z lt) o eq =
  use (getSplit (heap s) j p lp)
  where
  bs : List Bool
  bs = seed (liveRefs s) (length (heap s))
  below : obj r < length (heap s)
  below = ≤-trans lt (lower (lookup-< (heap s) j p lp))
  lenb : obj r < length bs
  lenb = under below (sym (length-seed (liveRefs s) (length (heap s))))
  use : Split (heap s) j p → markBit s (obj r) ≡ true
  use (mkSplit pre post q len) =
    subst (λ h → lookupB (go h zero bs) (obj r) ≡ true) (sym q)
      (child-marked pre p post bs r hj inn z (under lt (sym len)) lenb)
    where
    hj : lookupB (go (pre ++ p ∷ post) zero bs) (length pre) ≡ true
    hj = subst (λ h → lookupB (go h zero bs) (length pre) ≡ true) q bitAtLen
      where
      bitAtJ : lookupB (go (heap s) zero bs) j ≡ true
      bitAtJ = reach→mark s j rj p lp
      bitAtLen : lookupB (go (heap s) zero bs) (length pre) ≡ true
      bitAtLen = subst (λ n → lookupB (go (heap s) zero bs) n ≡ true) (sym len) bitAtJ

------------------------------------------------------------------------
-- Apply the marks. false clears the payload.
------------------------------------------------------------------------

apply : List Bool → List Obj → List Obj
apply _            []       = []
apply []           (_ ∷ os) = cell (nat zero) free ∷ apply [] os
apply (false ∷ bs) (_ ∷ os) = cell (nat zero) free ∷ apply bs os
apply (true  ∷ bs) (o ∷ os) = record o { status = live } ∷ apply bs os

apply-tail : ∀ b bs o os i →
  lookup (apply (b ∷ bs) (o ∷ os)) (suc i) ≡ lookup (apply bs os) i
apply-tail false _ _ _ _ = refl
apply-tail true  _ _ _ _ = refl

apply-keep : ∀ bs os i o →
  lookup os i ≡ just o →
  lookupB bs i ≡ true →
  lookup (apply bs os) i ≡ just (record o { status = live })
apply-keep []           _        _       _ _ ()
apply-keep (_ ∷ _)      []       _       _ () _
apply-keep (false ∷ _)  (_ ∷ _)  zero    _ _  ()
apply-keep (true  ∷ _)  (x ∷ _)  zero    .x refl refl = refl
apply-keep (b ∷ bs)     (x ∷ os) (suc i) o eq bt =
  trans (apply-tail b bs x os i) (apply-keep bs os i o eq bt)

apply-drop : ∀ bs os i o →
  lookup os i ≡ just o →
  lookupB bs i ≡ false →
  lookup (apply bs os) i ≡ just (cell (nat zero) free)
apply-drop []           (_ ∷ os) zero    _ _  refl = refl
apply-drop []           (_ ∷ os) (suc i) o eq bt   = apply-drop [] os i o eq bt
apply-drop (false ∷ _)  (_ ∷ _)  zero    _ _  refl = refl
apply-drop (true  ∷ _)  (_ ∷ _)  zero    _ _  ()
apply-drop (b ∷ bs)     (x ∷ os) (suc i) o eq bt =
  trans (apply-tail b bs x os i) (apply-drop bs os i o eq bt)
apply-drop (_ ∷ _)      []       _       _ () _

------------------------------------------------------------------------
-- Drop a g0 root or message. Environment slots stay, so indices do not move.
------------------------------------------------------------------------

keepRef : Bool → Ref → List Ref → List Ref
keepRef true  _ rs = rs
keepRef false r rs = r ∷ rs

filterKeep : List Ref → List Ref
filterKeep []       = []
filterKeep (r ∷ rs) = keepRef (isZeroGrade (residual r)) r (filterKeep rs)

keepMsg : Bool → Ref → List Msg → List Msg
keepMsg true  _ ms = ms
keepMsg false r ms = msg r ∷ ms

filterMsg : List Msg → List Msg
filterMsg []           = []
filterMsg (msg r ∷ ms) = keepMsg (isZeroGrade (residual r)) r (filterMsg ms)

clean : Proc → Proc
clean p = record p { roots = filterKeep (roots p) ; inbox = filterMsg (inbox p) }

collect : Sys → Sys
collect s = sys (apply (markVec s) (heap s)) (map clean (procs s))

collect-safe : ∀ s i → Reach s i → ∀ o →
  lookup (heap s) i ≡ just o →
  lookup (heap (collect s)) i ≡ just (record o { status = live })
collect-safe s i reach o eq = apply-keep (markVec s) (heap s) i o eq (reach→mark s i reach o eq)

refs-live : ∀ s → refsOf s ≡ edgeRefs (heap s) ++ liveRefs s
refs-live s = ++-assoc (edgeRefs (heap s)) (ctlRefsPs (procs s)) (refsPs (procs s))

seed-false : ∀ rs n i → i < n → anyKeeper i rs ≡ false → lookupB (seed rs n) i ≡ false
seed-false rs n i lt na rewrite seed-at rs n i lt = na

mark-false : ∀ s i o →
  lookup (heap s) i ≡ just o →
  anyKeeper i (refsOf s) ≡ false →
  markBit s i ≡ false
mark-false s i o eq nk = go-no (heap s) zero bs i (proj₁ parts) (seed-false (liveRefs s) (length (heap s)) i lt (proj₂ parts))
  where
  bs : List Bool
  bs = seed (liveRefs s) (length (heap s))
  lt : i < length (heap s)
  lt = lookup-< (heap s) i o eq
  flat : anyKeeper i (edgeRefs (heap s) ++ liveRefs s) ≡ false
  flat = trans (cong (anyKeeper i) (sym (refs-live s))) nk
  parts : anyKeeper i (edgeRefs (heap s)) ≡ false × anyKeeper i (liveRefs s) ≡ false
  parts = ∨-false _ _ (trans (sym (any-++ i (edgeRefs (heap s)) (liveRefs s))) flat)

-- No positive residual reference anywhere means the slot is not reached,
-- so collect frees it. On a heap of nats this is the v0 statement.
collect-frees-zero : ∀ s i o →
  lookup (heap s) i ≡ just o →
  anyKeeper i (refsOf s) ≡ false →
  lookup (heap (collect s)) i ≡ just (cell (nat zero) free)
collect-frees-zero s i o eq nk = apply-drop (markVec s) (heap s) i o eq (mark-false s i o eq nk)

data Collected (s : Sys) : Set where
  collected : (t : Sys) → t ≡ collect s → Collected s

collect-total : ∀ s → Collected s
collect-total s = collected (collect s) refl

------------------------------------------------------------------------
-- One scheduling step. Some process, one eval, or the collector.
------------------------------------------------------------------------

data Step : Sys → Sys → Set where
  step-deref   : ∀ {s i j t} → deref run s i j ≡ just t → Step s t
  step-send    : ∀ {s i j k t} → send s i j k ≡ just t → Step s t
  step-recv    : ∀ {s i t} → recv s i ≡ just t → Step s t
  step-alloc   : ∀ {s i g v t} → alloc s i g v ≡ just t → Step s t
  step-reuse   : ∀ {s i j g v t} → reuse s i j g v ≡ just t → Step s t
  step-eval    : ∀ {s i t} → eval1 s i ≡ just t → Step s t
  step-collect : ∀ {s} → Step s (collect s)

residual-inv-step : ∀ {s t} → Step s t → AllInv (refsOf t)
residual-inv-step _ = refs-inv _
