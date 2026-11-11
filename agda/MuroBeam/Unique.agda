------------------------------------------------------------------------
-- Grade-1 uniqueness.
--
-- `grade1-unique` is the property that a checked g1 reference is the only
-- reference to its object. It is an invariant of reachable configurations,
-- not a fact about every `Sys` one can write down. `step-preserves-grade1`
-- says every `Step` keeps it, together with the bound that every reference
-- index lies in the heap.
--
-- `send-g1-moves` says a successful send of a checked g1 root whose residual
-- is not g0 is exactly `moveTo`: the root is removed from the sender and
-- enqueued on the receiver, the heap is unchanged, and every object's
-- reference count is unchanged.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Unique where

open import Data.Bool.Base using (Bool; true; false; _∨_; _∧_)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; _≡ᵇ_; s≤s)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (run)
open import Muro.Grade using (Grade; g0; g1)
open import MuroBeam.Grade using
  ( isG1; isZeroGrade; selfKept; Kind; Kmove; Kcopy; kind; kind-g1; copy-not-g1 )
open import MuroBeam.Heap using
  ( Ref; obj; checked; residual; ref; count; hasG1; Grade1Unique; uniq-nil
  ; same-unique; Bound; bnil; bcons; bound-++
  ; bound-count0; count0-has
  ; count-++; has-++; count-snoc; has-snoc
  ; removeAt-count; removeAt-has
  ; repl; repl-count; repl-has; bound-repl; bound-remove
  ; spendRef; spendRef-obj; spendRef-checked
  ; Obj; cell; live )
open import MuroBeam.Lib using
  ( ⊥; ⊥-elim; ≤-refl; ≤-step; ≤-trans
  ; +-assoc; +-comm; +-identityʳ; +-swap; +-zero
  ; ≡ᵇ-sound; ≡ᵇ-cong
  ; ∨-assoc; ∨-comm; ∨-swap; ∨-falseʳ; ∨-trueʳ
  ; ext; ext-0
  ; lookup; update; mapCons; removeAt
  ; ++-assoc; length-++ )
open import MuroBeam.Process using
  ( Proc; roots; inbox; refsP; refsPs; refsOf
  ; Sys; sys; heap; procs; Msg; msg; mapRef; mapSys
  ; post; putRoot; putHead; putHeadOf; putTail
  ; deref; derefAt; derefSpent; rootAt; rootFrom
  ; send; sendFrom; sendTaken; dropRoot; takeRoot; dispatch
  ; moveTo; moveToOn; moveOther; moveRecv; copyTo; addMsg
  ; recv; recvAt; recvInbox; addRoot; alloc
  ; poke; length-poke; reuse; reuseFrom; reuseOk )
open import MuroBeam.Collect using
  ( Step; step-deref; step-send; step-recv; step-alloc; step-reuse; step-collect
  ; collect; walk; filterKeep; filterMsg; clean )

------------------------------------------------------------------------
-- Small algebra used by the transports below.
------------------------------------------------------------------------

true≢false : true ≡ false → ⊥
true≢false ()

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

suc-inj : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-inj refl = refl

fresh-< : ∀ n → n < suc n
fresh-< n = s≤s ≤-refl

shift-add : ∀ a b c k → a ≡ b + k → (a + c) ≡ (b + c) + k
shift-add a b c k eq =
  trans (cong (_+ c) eq)
  (trans (+-assoc b k c)
  (trans (cong (b +_) (+-comm k c))
         (sym (+-assoc b c k))))

shift-suc : ∀ a b c k → b ≡ c + k → (a + b) ≡ (a + c) + k
shift-suc a b c k eq =
  trans (cong (a +_) eq)
        (sym (+-assoc a c k))

shift-sub : ∀ a b c k → b ≡ k + a → (b + c) ≡ k + (a + c)
shift-sub a b c k eq =
  trans (cong (_+ c) eq)
        (+-assoc k a c)

or-left-zero : ∀ a a' c b → a ≡ b ∨ a' → (a ∨ c) ≡ b ∨ (a' ∨ c)
or-left-zero a a' c b eq =
  trans (cong (_∨ c) eq)
        (∨-assoc b a' c)

or-left-suc : ∀ a b c d → c ≡ b ∨ d → (a ∨ c) ≡ b ∨ (a ∨ d)
or-left-suc a b c d eq =
  trans (cong (a ∨_) eq)
        (∨-swap a b d)

or-right-zero : ∀ a a' c b → a' ≡ a ∨ b → (a' ∨ c) ≡ (a ∨ c) ∨ b
or-right-zero a a' c b eq =
  trans (cong (_∨ c) eq)
  (trans (∨-assoc a b c)
  (trans (cong (a ∨_) (∨-comm b c))
         (sym (∨-assoc a c b))))

or-right-suc : ∀ a c d b → d ≡ c ∨ b → (a ∨ d) ≡ (a ∨ c) ∨ b
or-right-suc a c d b eq =
  trans (cong (a ∨_) eq)
        (sym (∨-assoc a c b))

length-snoc : ∀ {A : Set} (xs : List A) (x : A) →
  length (xs ++ x ∷ []) ≡ suc (length xs)
length-snoc []       x = refl
length-snoc (y ∷ xs) x rewrite length-snoc xs x = refl

------------------------------------------------------------------------
-- The invariant.
------------------------------------------------------------------------

WF : Sys → Set
WF s = Bound (length (heap s)) (refsOf s) × Grade1Unique (refsOf s)

grade1-unique : ∀ s → WF s → ∀ i →
  hasG1 i (refsOf s) ≡ true → count i (refsOf s) ≡ 1
grade1-unique s (_ , u) i h = u i h

------------------------------------------------------------------------
-- Splitting a bound, and lifting an index update.
------------------------------------------------------------------------

bound-split : ∀ {n} xs ys → Bound n (xs ++ ys) → Bound n xs × Bound n ys
bound-split []       ys bd = bnil , bd
bound-split (x ∷ xs) ys (bcons lt rest) with bound-split xs ys rest
... | bx , by = bcons lt bx , by

bound-snoc : ∀ {n rs r} → Bound n rs → obj r < n → Bound n (rs ++ r ∷ [])
bound-snoc bnil          lt = bcons lt bnil
bound-snoc (bcons lt rs) lt' = bcons lt (bound-snoc rs lt')

bound-mono : ∀ {n m rs} → n ≤ m → Bound n rs → Bound m rs
bound-mono le bnil = bnil
bound-mono le (bcons lt rest) = bcons (≤-trans lt le) (bound-mono le rest)

lookup-bound : ∀ {n} i ps p →
  Bound n (refsPs ps) →
  lookup ps i ≡ just p →
  Bound n (refsP p)
lookup-bound {n} i ps p bd eq = go i ps p bd eq
  where
  go : ∀ i ps p → Bound n (refsPs ps) → lookup ps i ≡ just p → Bound n (refsP p)
  go i [] p bd ()
  go zero (q ∷ qs) .q bd refl with bound-split (refsP q) (refsPs qs) bd
  ... | bp , _ = bp
  go (suc i) (q ∷ qs) p bd eq with bound-split (refsP q) (refsPs qs) bd
  ... | _ , bqs = go i qs p bqs eq

upd-bound : ∀ {n} i ps p p' ps' →
  Bound n (refsPs ps) →
  lookup ps i ≡ just p →
  update i p' ps ≡ just ps' →
  Bound n (refsP p') →
  Bound n (refsPs ps')
upd-bound {n} i ps p p' ps' bd lk eq bp' = go i ps p ps' bd lk eq
  where
  go : ∀ i ps p ps' →
       Bound n (refsPs ps) →
       lookup ps i ≡ just p →
       update i p' ps ≡ just ps' →
       Bound n (refsPs ps')
  go i [] p ps' bd () _
  go zero (q ∷ qs) .q .(p' ∷ qs) bd refl refl with bound-split (refsP q) (refsPs qs) bd
  ... | _ , bqs = bound-++ bp' bqs
  go (suc i) (q ∷ qs) p ps' bd lk eq with bound-split (refsP q) (refsPs qs) bd
  ... | bq , bqs = step (update i p' qs) eq refl bqs
    where
    step : (m : Maybe (List Proc)) →
           mapCons q m ≡ just ps' →
           update i p' qs ≡ m →
           Bound n (refsPs qs) →
           Bound n (refsPs ps')
    step nothing () _ _
    step (just qs') refl equ bqs' = bound-++ bq (go i qs p qs' bqs' lk equ)

upd-count : ∀ i n ps p p' ps' →
  lookup ps n ≡ just p →
  update n p' ps ≡ just ps' →
  count i (refsP p') ≡ count i (refsP p) →
  count i (refsPs ps') ≡ count i (refsPs ps)
upd-count i n ps p p' ps' lk eq cq = go n ps p ps' lk eq cq
  where
  go : ∀ n ps p ps' →
       lookup ps n ≡ just p →
       update n p' ps ≡ just ps' →
       count i (refsP p') ≡ count i (refsP p) →
       count i (refsPs ps') ≡ count i (refsPs ps)
  go n [] p ps' () _ _
  go zero (q ∷ qs) .q .(p' ∷ qs) refl refl cq
    rewrite count-++ i (refsP p') (refsPs qs)
          | count-++ i (refsP q) (refsPs qs)
          | cq = refl
  go (suc n) (q ∷ qs) p ps' lk eq cq = step (update n p' qs) eq refl
    where
    step : (m : Maybe (List Proc)) →
           mapCons q m ≡ just ps' →
           update n p' qs ≡ m →
           count i (refsPs ps') ≡ count i (refsPs (q ∷ qs))
    step nothing () _
    step (just qs') refl equ
      rewrite count-++ i (refsP q) (refsPs qs')
            | count-++ i (refsP q) (refsPs qs)
            | go n qs p qs' lk equ cq = refl

upd-has : ∀ i n ps p p' ps' →
  lookup ps n ≡ just p →
  update n p' ps ≡ just ps' →
  hasG1 i (refsP p') ≡ hasG1 i (refsP p) →
  hasG1 i (refsPs ps') ≡ hasG1 i (refsPs ps)
upd-has i n ps p p' ps' lk eq hq = go n ps p ps' lk eq hq
  where
  go : ∀ n ps p ps' →
       lookup ps n ≡ just p →
       update n p' ps ≡ just ps' →
       hasG1 i (refsP p') ≡ hasG1 i (refsP p) →
       hasG1 i (refsPs ps') ≡ hasG1 i (refsPs ps)
  go n [] p ps' () _ _
  go zero (q ∷ qs) .q .(p' ∷ qs) refl refl hq
    rewrite has-++ i (refsP p') (refsPs qs)
          | has-++ i (refsP q) (refsPs qs)
          | hq = refl
  go (suc n) (q ∷ qs) p ps' lk eq hq = step (update n p' qs) eq refl
    where
    step : (m : Maybe (List Proc)) →
           mapCons q m ≡ just ps' →
           update n p' qs ≡ m →
           hasG1 i (refsPs ps') ≡ hasG1 i (refsPs (q ∷ qs))
    step nothing () _
    step (just qs') refl equ
      rewrite has-++ i (refsP q) (refsPs qs')
            | has-++ i (refsP q) (refsPs qs)
            | go n qs p qs' lk equ hq = refl

upd-add : ∀ i n ps p p' ps' k →
  lookup ps n ≡ just p →
  update n p' ps ≡ just ps' →
  count i (refsP p') ≡ count i (refsP p) + k →
  count i (refsPs ps') ≡ count i (refsPs ps) + k
upd-add i n ps p p' ps' k lk eq cq = go n ps p ps' lk eq cq
  where
  go : ∀ n ps p ps' →
       lookup ps n ≡ just p →
       update n p' ps ≡ just ps' →
       count i (refsP p') ≡ count i (refsP p) + k →
       count i (refsPs ps') ≡ count i (refsPs ps) + k
  go n [] p ps' () _ _
  go zero (q ∷ qs) .q .(p' ∷ qs) refl refl cq
    rewrite count-++ i (refsP p') (refsPs qs)
          | count-++ i (refsP q) (refsPs qs)
          = shift-add (count i (refsP p')) (count i (refsP q)) (count i (refsPs qs)) k cq
  go (suc n) (q ∷ qs) p ps' lk eq cq = step (update n p' qs) eq refl
    where
    step : (m : Maybe (List Proc)) →
           mapCons q m ≡ just ps' →
           update n p' qs ≡ m →
           count i (refsPs ps') ≡ count i (refsPs (q ∷ qs)) + k
    step nothing () _
    step (just qs') refl equ
      rewrite count-++ i (refsP q) (refsPs qs')
            | count-++ i (refsP q) (refsPs qs)
            = shift-suc (count i (refsP q)) (count i (refsPs qs')) (count i (refsPs qs)) k
                (go n qs p qs' lk equ cq)

sub-suc : ∀ a b c k → c ≡ k + b → (a + c) ≡ k + (a + b)
sub-suc a b c k eq =
  trans (cong (a +_) eq)
        (+-swap a k b)

upd-sub : ∀ i n ps p p' ps' k →
  lookup ps n ≡ just p →
  update n p' ps ≡ just ps' →
  count i (refsP p) ≡ k + count i (refsP p') →
  count i (refsPs ps) ≡ k + count i (refsPs ps')
upd-sub i n ps p p' ps' k lk eq cq = go n ps p ps' lk eq cq
  where
  go : ∀ n ps p ps' →
       lookup ps n ≡ just p →
       update n p' ps ≡ just ps' →
       count i (refsP p) ≡ k + count i (refsP p') →
       count i (refsPs ps) ≡ k + count i (refsPs ps')
  go n [] p ps' () _ _
  go zero (q ∷ qs) .q .(p' ∷ qs) refl refl cq
    rewrite count-++ i (refsP q) (refsPs qs)
          | count-++ i (refsP p') (refsPs qs)
          = shift-sub (count i (refsP p')) (count i (refsP q)) (count i (refsPs qs)) k cq
  go (suc n) (q ∷ qs) p ps' lk eq cq = step (update n p' qs) eq refl
    where
    step : (m : Maybe (List Proc)) →
           mapCons q m ≡ just ps' →
           update n p' qs ≡ m →
           count i (refsPs (q ∷ qs)) ≡ k + count i (refsPs ps')
    step nothing () _
    step (just qs') refl equ
      rewrite count-++ i (refsP q) (refsPs qs)
            | count-++ i (refsP q) (refsPs qs')
            = sub-suc (count i (refsP q)) (count i (refsPs qs')) (count i (refsPs qs)) k
                (go n qs p qs' lk equ cq)

upd-or-left : ∀ i n ps p p' ps' b →
  lookup ps n ≡ just p →
  update n p' ps ≡ just ps' →
  hasG1 i (refsP p) ≡ b ∨ hasG1 i (refsP p') →
  hasG1 i (refsPs ps) ≡ b ∨ hasG1 i (refsPs ps')
upd-or-left i n ps p p' ps' b lk eq hq = go n ps p ps' lk eq hq
  where
  go : ∀ n ps p ps' →
       lookup ps n ≡ just p →
       update n p' ps ≡ just ps' →
       hasG1 i (refsP p) ≡ b ∨ hasG1 i (refsP p') →
       hasG1 i (refsPs ps) ≡ b ∨ hasG1 i (refsPs ps')
  go n [] p ps' () _ _
  go zero (q ∷ qs) .q .(p' ∷ qs) refl refl hq
    rewrite has-++ i (refsP q) (refsPs qs)
          | has-++ i (refsP p') (refsPs qs)
          = or-left-zero (hasG1 i (refsP q)) (hasG1 i (refsP p')) (hasG1 i (refsPs qs)) b hq
  go (suc n) (q ∷ qs) p ps' lk eq hq = step (update n p' qs) eq refl
    where
    step : (m : Maybe (List Proc)) →
           mapCons q m ≡ just ps' →
           update n p' qs ≡ m →
           hasG1 i (refsPs (q ∷ qs)) ≡ b ∨ hasG1 i (refsPs ps')
    step nothing () _
    step (just qs') refl equ
      rewrite has-++ i (refsP q) (refsPs qs)
            | has-++ i (refsP q) (refsPs qs')
            = or-left-suc (hasG1 i (refsP q)) b (hasG1 i (refsPs qs)) (hasG1 i (refsPs qs'))
                (go n qs p qs' lk equ hq)

upd-or-right : ∀ i n ps p p' ps' b →
  lookup ps n ≡ just p →
  update n p' ps ≡ just ps' →
  hasG1 i (refsP p') ≡ hasG1 i (refsP p) ∨ b →
  hasG1 i (refsPs ps') ≡ hasG1 i (refsPs ps) ∨ b
upd-or-right i n ps p p' ps' b lk eq hq = go n ps p ps' lk eq hq
  where
  go : ∀ n ps p ps' →
       lookup ps n ≡ just p →
       update n p' ps ≡ just ps' →
       hasG1 i (refsP p') ≡ hasG1 i (refsP p) ∨ b →
       hasG1 i (refsPs ps') ≡ hasG1 i (refsPs ps) ∨ b
  go n [] p ps' () _ _
  go zero (q ∷ qs) .q .(p' ∷ qs) refl refl hq
    rewrite has-++ i (refsP p') (refsPs qs)
          | has-++ i (refsP q) (refsPs qs)
          = or-right-zero (hasG1 i (refsP q)) (hasG1 i (refsP p')) (hasG1 i (refsPs qs)) b hq
  go (suc n) (q ∷ qs) p ps' lk eq hq = step (update n p' qs) eq refl
    where
    step : (m : Maybe (List Proc)) →
           mapCons q m ≡ just ps' →
           update n p' qs ≡ m →
           hasG1 i (refsPs ps') ≡ hasG1 i (refsPs (q ∷ qs)) ∨ b
    step nothing () _
    step (just qs') refl equ
      rewrite has-++ i (refsP q) (refsPs qs')
            | has-++ i (refsP q) (refsPs qs)
            = or-right-suc (hasG1 i (refsP q)) (hasG1 i (refsPs qs)) (hasG1 i (refsPs qs')) b
                (go n qs p qs' lk equ hq)

------------------------------------------------------------------------
-- A proc that is not the one at index n.
------------------------------------------------------------------------

others : ℕ → List Proc → List Ref
others _ []             = []
others zero    (_ ∷ ps) = refsPs ps
others (suc n) (p ∷ ps) = refsP p ++ others n ps

lookup-count : ∀ i n ps p →
  lookup ps n ≡ just p →
  count i (refsPs ps) ≡ count i (refsP p) + count i (others n ps)
lookup-count i n ps p eq = go n ps p eq
  where
  go : ∀ n ps p → lookup ps n ≡ just p →
       count i (refsPs ps) ≡ count i (refsP p) + count i (others n ps)
  go n [] p ()
  go zero (q ∷ qs) .q refl = count-++ i (refsP q) (refsPs qs)
  go (suc n) (q ∷ qs) p eq =
    trans (count-++ i (refsP q) (refsPs qs))
    (trans (cong (count i (refsP q) +_) (go n qs p eq))
    (trans (+-swap (count i (refsP q)) (count i (refsP p)) (count i (others n qs)))
           (cong (count i (refsP p) +_) (sym (count-++ i (refsP q) (others n qs))))))

lookup-has : ∀ i n ps p →
  lookup ps n ≡ just p →
  hasG1 i (refsPs ps) ≡ hasG1 i (refsP p) ∨ hasG1 i (others n ps)
lookup-has i n ps p eq = go n ps p eq
  where
  go : ∀ n ps p → lookup ps n ≡ just p →
       hasG1 i (refsPs ps) ≡ hasG1 i (refsP p) ∨ hasG1 i (others n ps)
  go n [] p ()
  go zero (q ∷ qs) .q refl = has-++ i (refsP q) (refsPs qs)
  go (suc n) (q ∷ qs) p eq =
    trans (has-++ i (refsP q) (refsPs qs))
    (trans (cong (hasG1 i (refsP q) ∨_) (go n qs p eq))
    (trans (∨-swap (hasG1 i (refsP q)) (hasG1 i (refsP p)) (hasG1 i (others n qs)))
           (cong (hasG1 i (refsP p) ∨_) (sym (has-++ i (refsP q) (others n qs))))))

------------------------------------------------------------------------
-- Posting a message and dropping a root.
------------------------------------------------------------------------

mapRef-++ : ∀ ms ns → mapRef (ms ++ ns) ≡ mapRef ms ++ mapRef ns
mapRef-++ []             ns = refl
mapRef-++ (msg r ∷ ms) ns rewrite mapRef-++ ms ns = refl

refs-post : ∀ p r → refsP (post p r) ≡ refsP p ++ (r ∷ [])
refs-post p r =
  trans (cong (roots p ++_) (mapRef-++ (inbox p) (msg r ∷ [])))
        (sym (++-assoc (roots p) (mapRef (inbox p)) (r ∷ [])))

post-count : ∀ i p r →
  count i (refsP (post p r)) ≡ count i (refsP p) + ext (obj r ≡ᵇ i)
post-count i p r =
  trans (cong (count i) (refs-post p r))
        (count-snoc i (refsP p) r)

post-has : ∀ i p r →
  hasG1 i (refsP (post p r)) ≡
    hasG1 i (refsP p) ∨ ((obj r ≡ᵇ i) ∧ isG1 (checked r))
post-has i p r =
  trans (cong (hasG1 i) (refs-post p r))
        (has-snoc i (refsP p) r)

post-bound : ∀ {n} p r → Bound n (refsP p) → obj r < n → Bound n (refsP (post p r))
post-bound {n} p r bd olt =
  subst (Bound n) (sym (refs-post p r)) (bound-snoc bd olt)

proc-drop-count : ∀ i sp j r ys →
  removeAt j (roots sp) ≡ just (r , ys) →
  count i (refsP sp) ≡ ext (obj r ≡ᵇ i) + count i (ys ++ mapRef (inbox sp))
proc-drop-count i sp j r ys eq =
  trans (count-++ i (roots sp) (mapRef (inbox sp)))
  (trans (cong (_+ count i (mapRef (inbox sp))) (removeAt-count i j (roots sp) r ys eq))
  (trans (+-assoc (ext (obj r ≡ᵇ i)) (count i ys) (count i (mapRef (inbox sp))))
         (cong (ext (obj r ≡ᵇ i) +_) (sym (count-++ i ys (mapRef (inbox sp)))))))

proc-drop-has : ∀ i sp j r ys →
  removeAt j (roots sp) ≡ just (r , ys) →
  hasG1 i (refsP sp) ≡
    ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ∨ hasG1 i (ys ++ mapRef (inbox sp))
proc-drop-has i sp j r ys eq =
  trans (has-++ i (roots sp) (mapRef (inbox sp)))
  (trans (cong (_∨ hasG1 i (mapRef (inbox sp))) (removeAt-has i j (roots sp) r ys eq))
  (trans (∨-assoc ((obj r ≡ᵇ i) ∧ isG1 (checked r)) (hasG1 i ys) (hasG1 i (mapRef (inbox sp))))
         (cong (((obj r ≡ᵇ i) ∧ isG1 (checked r)) ∨_)
               (sym (has-++ i ys (mapRef (inbox sp)))))))

proc-drop-bound : ∀ {n} sp j r ys →
  Bound n (refsP sp) →
  removeAt j (roots sp) ≡ just (r , ys) →
  Bound n (refsP (record sp { roots = ys })) × obj r < n
proc-drop-bound sp j r ys bd eq with bound-split (roots sp) (mapRef (inbox sp)) bd
... | br , bi with bound-remove j (roots sp) r ys br eq
... | bys , olt = bound-++ bys bi , olt

self-count : ∀ i sp j r ys →
  removeAt j (roots sp) ≡ just (r , ys) →
  count i (refsP (post (record sp { roots = ys }) r)) ≡ count i (refsP sp)
self-count i sp j r ys eq =
  trans (post-count i (record sp { roots = ys }) r)
  (trans (+-comm (count i (ys ++ mapRef (inbox sp))) (ext (obj r ≡ᵇ i)))
         (sym (proc-drop-count i sp j r ys eq)))

self-has : ∀ i sp j r ys →
  removeAt j (roots sp) ≡ just (r , ys) →
  hasG1 i (refsP (post (record sp { roots = ys }) r)) ≡ hasG1 i (refsP sp)
self-has i sp j r ys eq =
  trans (post-has i (record sp { roots = ys }) r)
  (trans (∨-comm (hasG1 i (ys ++ mapRef (inbox sp))) ((obj r ≡ᵇ i) ∧ isG1 (checked r)))
         (sym (proc-drop-has i sp j r ys eq)))

------------------------------------------------------------------------
-- Replacing one root. Deref keeps the checked grade; reuse may change it.
------------------------------------------------------------------------

update→repl : ∀ {j rs r r0} →
  lookup rs j ≡ just r0 →
  update j r rs ≡ just (repl j r rs)
update→repl {j} {rs} {r} {r0} eq = go j rs eq
  where
  go : ∀ j rs → lookup rs j ≡ just r0 → update j r rs ≡ just (repl j r rs)
  go j [] ()
  go zero (.r0 ∷ xs) refl = refl
  go (suc j) (x ∷ xs) eq rewrite go j xs eq = refl

repl-has-miss : ∀ i n xs r r0 →
  lookup xs n ≡ just r0 →
  obj r ≡ obj r0 →
  (obj r0 ≡ᵇ i) ≡ false →
  hasG1 i (repl n r xs) ≡ hasG1 i xs
repl-has-miss i n xs r r0 eq eo em = go n xs eq
  where
  go : ∀ n xs → lookup xs n ≡ just r0 → hasG1 i (repl n r xs) ≡ hasG1 i xs
  go n [] ()
  go zero (.r0 ∷ xs) refl rewrite ≡ᵇ-cong (obj r) (obj r0) i eo | em = refl
  go (suc n) (x ∷ xs) eq rewrite go n xs eq = refl



put-count : ∀ k i j ps p r0 r' ps' →
  lookup ps i ≡ just p →
  lookup (roots p) j ≡ just r0 →
  obj r' ≡ obj r0 →
  putRoot ps i j r' ≡ just ps' →
  count k (refsPs ps') ≡ count k (refsPs ps)
put-count k i j ps p r0 r' ps' lk lr eo eq = go i ps p ps' lk lr eq
  where
  swapped : ∀ q qs →
    lookup (roots q) j ≡ just r0 →
    count k (refsPs (record q { roots = repl j r' (roots q) } ∷ qs)) ≡
    count k (refsPs (q ∷ qs))
  swapped q qs lr' =
    trans (count-++ k (repl j r' (roots q) ++ mapRef (inbox q)) (refsPs qs))
    (trans (cong (_+ count k (refsPs qs))
                 (trans (count-++ k (repl j r' (roots q)) (mapRef (inbox q)))
                        (cong (_+ count k (mapRef (inbox q)))
                              (repl-count k j (roots q) r' r0 lr' eo))))
    (trans (sym (cong (_+ count k (refsPs qs))
                       (count-++ k (roots q) (mapRef (inbox q)))))
           (sym (count-++ k (refsP q) (refsPs qs)))))
  go : ∀ i ps p ps' →
       lookup ps i ≡ just p →
       lookup (roots p) j ≡ just r0 →
       putRoot ps i j r' ≡ just ps' →
       count k (refsPs ps') ≡ count k (refsPs ps)
  go i [] p ps' () _ _
  go zero (q ∷ qs) .q ps' refl lr' eq' = head (update j r' (roots q)) eq' refl
    where
    head : (m : Maybe (List Ref)) →
           putHead q j r' qs ≡ just ps' →
           update j r' (roots q) ≡ m →
           count k (refsPs ps') ≡ count k (refsPs (q ∷ qs))
    head nothing e eu =
      ⊥-elim (nothing≢just (trans (sym (cong (putHeadOf q qs) eu)) e))
    head (just rs) e eu =
      trans (cong (λ ps0 → count k (refsPs ps0)) peq)
      (trans (cong (λ zs → count k (refsPs (record q { roots = zs } ∷ qs))) rs≡)
             (swapped q qs lr'))
      where
      rs≡ : rs ≡ repl j r' (roots q)
      rs≡ = just-inj (trans (sym eu) (update→repl lr'))
      peq : ps' ≡ (record q { roots = rs } ∷ qs)
      peq = sym (just-inj (trans (sym (cong (putHeadOf q qs) eu)) e))
  go (suc i) (q ∷ qs) p ps' lk' lr' eq' = via (putRoot qs i j r') eq' refl
    where
    via : (m : Maybe (List Proc)) →
          putTail q m ≡ just ps' →
          putRoot qs i j r' ≡ m →
          count k (refsPs ps') ≡ count k (refsPs (q ∷ qs))
    via nothing () _
    via (just qs') refl equ
      rewrite count-++ k (refsP q) (refsPs qs')
            | count-++ k (refsP q) (refsPs qs)
            | go i qs p qs' lk' lr' equ = refl

put-has : ∀ k i j ps p r0 r' ps' →
  lookup ps i ≡ just p →
  lookup (roots p) j ≡ just r0 →
  obj r' ≡ obj r0 →
  checked r' ≡ checked r0 →
  putRoot ps i j r' ≡ just ps' →
  hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps)
put-has k i j ps p r0 r' ps' lk lr eo ec eq = go i ps p ps' lk lr eq
  where
  swapped : ∀ q qs →
    lookup (roots q) j ≡ just r0 →
    hasG1 k (refsPs (record q { roots = repl j r' (roots q) } ∷ qs)) ≡
    hasG1 k (refsPs (q ∷ qs))
  swapped q qs lr' =
    trans (has-++ k (repl j r' (roots q) ++ mapRef (inbox q)) (refsPs qs))
    (trans (cong (_∨ hasG1 k (refsPs qs))
                 (trans (has-++ k (repl j r' (roots q)) (mapRef (inbox q)))
                        (cong (_∨ hasG1 k (mapRef (inbox q)))
                              (repl-has k j (roots q) r' r0 lr' eo ec))))
    (trans (sym (cong (_∨ hasG1 k (refsPs qs))
                       (has-++ k (roots q) (mapRef (inbox q)))))
           (sym (has-++ k (refsP q) (refsPs qs)))))
  go : ∀ i ps p ps' →
       lookup ps i ≡ just p →
       lookup (roots p) j ≡ just r0 →
       putRoot ps i j r' ≡ just ps' →
       hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps)
  go i [] p ps' () _ _
  go zero (q ∷ qs) .q ps' refl lr' eq' = head (update j r' (roots q)) eq' refl
    where
    head : (m : Maybe (List Ref)) →
           putHead q j r' qs ≡ just ps' →
           update j r' (roots q) ≡ m →
           hasG1 k (refsPs ps') ≡ hasG1 k (refsPs (q ∷ qs))
    head nothing e eu =
      ⊥-elim (nothing≢just (trans (sym (cong (putHeadOf q qs) eu)) e))
    head (just rs) e eu =
      trans (cong (λ ps0 → hasG1 k (refsPs ps0)) peq)
      (trans (cong (λ zs → hasG1 k (refsPs (record q { roots = zs } ∷ qs))) rs≡)
             (swapped q qs lr'))
      where
      rs≡ : rs ≡ repl j r' (roots q)
      rs≡ = just-inj (trans (sym eu) (update→repl lr'))
      peq : ps' ≡ (record q { roots = rs } ∷ qs)
      peq = sym (just-inj (trans (sym (cong (putHeadOf q qs) eu)) e))
  go (suc i) (q ∷ qs) p ps' lk' lr' eq' = via (putRoot qs i j r') eq' refl
    where
    via : (m : Maybe (List Proc)) →
          putTail q m ≡ just ps' →
          putRoot qs i j r' ≡ m →
          hasG1 k (refsPs ps') ≡ hasG1 k (refsPs (q ∷ qs))
    via nothing () _
    via (just qs') refl equ
      rewrite has-++ k (refsP q) (refsPs qs')
            | has-++ k (refsP q) (refsPs qs)
            | go i qs p qs' lk' lr' equ = refl

put-has-miss : ∀ k i j ps p r0 r' ps' →
  lookup ps i ≡ just p →
  lookup (roots p) j ≡ just r0 →
  obj r' ≡ obj r0 →
  (obj r0 ≡ᵇ k) ≡ false →
  putRoot ps i j r' ≡ just ps' →
  hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps)
put-has-miss k i j ps p r0 r' ps' lk lr eo em eq = go i ps p ps' lk lr eq
  where
  swapped : ∀ q qs →
    lookup (roots q) j ≡ just r0 →
    hasG1 k (refsPs (record q { roots = repl j r' (roots q) } ∷ qs)) ≡
    hasG1 k (refsPs (q ∷ qs))
  swapped q qs lr' =
    trans (has-++ k (repl j r' (roots q) ++ mapRef (inbox q)) (refsPs qs))
    (trans (cong (_∨ hasG1 k (refsPs qs))
                 (trans (has-++ k (repl j r' (roots q)) (mapRef (inbox q)))
                        (cong (_∨ hasG1 k (mapRef (inbox q)))
                              (repl-has-miss k j (roots q) r' r0 lr' eo em))))
    (trans (sym (cong (_∨ hasG1 k (refsPs qs))
                       (has-++ k (roots q) (mapRef (inbox q)))))
           (sym (has-++ k (refsP q) (refsPs qs)))))
  go : ∀ i ps p ps' →
       lookup ps i ≡ just p →
       lookup (roots p) j ≡ just r0 →
       putRoot ps i j r' ≡ just ps' →
       hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps)
  go i [] p ps' () _ _
  go zero (q ∷ qs) .q ps' refl lr' eq' = head (update j r' (roots q)) eq' refl
    where
    head : (m : Maybe (List Ref)) →
           putHead q j r' qs ≡ just ps' →
           update j r' (roots q) ≡ m →
           hasG1 k (refsPs ps') ≡ hasG1 k (refsPs (q ∷ qs))
    head nothing e eu =
      ⊥-elim (nothing≢just (trans (sym (cong (putHeadOf q qs) eu)) e))
    head (just rs) e eu =
      trans (cong (λ ps0 → hasG1 k (refsPs ps0)) peq)
      (trans (cong (λ zs → hasG1 k (refsPs (record q { roots = zs } ∷ qs))) rs≡)
             (swapped q qs lr'))
      where
      rs≡ : rs ≡ repl j r' (roots q)
      rs≡ = just-inj (trans (sym eu) (update→repl lr'))
      peq : ps' ≡ (record q { roots = rs } ∷ qs)
      peq = sym (just-inj (trans (sym (cong (putHeadOf q qs) eu)) e))
  go (suc i) (q ∷ qs) p ps' lk' lr' eq' = via (putRoot qs i j r') eq' refl
    where
    via : (m : Maybe (List Proc)) →
          putTail q m ≡ just ps' →
          putRoot qs i j r' ≡ m →
          hasG1 k (refsPs ps') ≡ hasG1 k (refsPs (q ∷ qs))
    via nothing () _
    via (just qs') refl equ
      rewrite has-++ k (refsP q) (refsPs qs')
            | has-++ k (refsP q) (refsPs qs)
            | go i qs p qs' lk' lr' equ = refl

put-bound : ∀ {n} i j ps p r0 r' ps' →
  Bound n (refsPs ps) →
  lookup ps i ≡ just p →
  lookup (roots p) j ≡ just r0 →
  obj r' ≡ obj r0 →
  putRoot ps i j r' ≡ just ps' →
  Bound n (refsPs ps')
put-bound {n} i j ps p r0 r' ps' bd lk lr eo eq = go i ps p ps' bd lk lr eq
  where
  swapped : ∀ q qs →
    lookup (roots q) j ≡ just r0 →
    Bound n (refsPs (q ∷ qs)) →
    Bound n (refsPs (record q { roots = repl j r' (roots q) } ∷ qs))
  swapped q qs lr' bd' with bound-split (refsP q) (refsPs qs) bd'
  ... | bq , bqs with bound-split (roots q) (mapRef (inbox q)) bq
  ... | br , bi =
    bound-++ (bound-++ (bound-repl j (roots q) r' r0 br lr' eo) bi) bqs
  go : ∀ i ps p ps' →
       Bound n (refsPs ps) →
       lookup ps i ≡ just p →
       lookup (roots p) j ≡ just r0 →
       putRoot ps i j r' ≡ just ps' →
       Bound n (refsPs ps')
  go i [] p ps' bd' () _ _
  go zero (q ∷ qs) .q ps' bd' refl lr' eq' = head (update j r' (roots q)) eq' refl
    where
    head : (m : Maybe (List Ref)) →
           putHead q j r' qs ≡ just ps' →
           update j r' (roots q) ≡ m →
           Bound n (refsPs ps')
    head nothing e eu =
      ⊥-elim (nothing≢just (trans (sym (cong (putHeadOf q qs) eu)) e))
    head (just rs) e eu =
      subst (λ ps0 → Bound n (refsPs ps0)) (just-inj reduced)
      (subst (λ zs → Bound n (refsPs (record q { roots = zs } ∷ qs))) (sym rs≡)
             (swapped q qs lr' bd'))
      where
      rs≡ : rs ≡ repl j r' (roots q)
      rs≡ = just-inj (trans (sym eu) (update→repl lr'))
      reduced : putHeadOf q qs (just rs) ≡ just ps'
      reduced = trans (sym (cong (putHeadOf q qs) eu)) e
  go (suc i) (q ∷ qs) p ps' bd' lk' lr' eq' = via (putRoot qs i j r') eq' refl
    where
    via : (m : Maybe (List Proc)) →
          putTail q m ≡ just ps' →
          putRoot qs i j r' ≡ m →
          Bound n (refsPs ps')
    via nothing () _
    via (just qs') refl equ with bound-split (refsP q) (refsPs qs) bd'
    ... | bq , bqs = bound-++ bq (go i qs p qs' bqs lk' lr' equ)

root-lookup : ∀ ps i j r →
  rootFrom (lookup ps i) j ≡ just r →
  Σ Proc (λ p → lookup ps i ≡ just p × lookup (roots p) j ≡ just r)
root-lookup ps i j r eq = via (lookup ps i) eq refl
  where
  via : (m : Maybe Proc) →
        rootFrom m j ≡ just r →
        lookup ps i ≡ m →
        Σ Proc (λ p → lookup ps i ≡ just p × lookup (roots p) j ≡ just r)
  via nothing () _
  via (just p) eq lk = p , (lk , eq)

------------------------------------------------------------------------
-- Collect keeps every g1 that still has a residual, and drops no live
-- unique reference's only copy.
------------------------------------------------------------------------

count-filter-0 : ∀ i rs → count i rs ≡ 0 → count i (filterKeep rs) ≡ 0
count-filter-0 i []       refl = refl
count-filter-0 i (r ∷ rs) eq with +-zero (ext (obj r ≡ᵇ i)) (count i rs) eq
... | eqa , eqr with isZeroGrade (residual r)
...   | true  = count-filter-0 i rs eqr
...   | false rewrite ext-0 (obj r ≡ᵇ i) eqa | count-filter-0 i rs eqr = refl

has-mono : ∀ i rs → hasG1 i (filterKeep rs) ≡ true → hasG1 i rs ≡ true
has-mono i [] ()
has-mono i (r ∷ rs) hf with isZeroGrade (residual r)
... | true rewrite has-mono i rs hf = ∨-trueʳ ((obj r ≡ᵇ i) ∧ isG1 (checked r))
... | false with obj r ≡ᵇ i
...    | false = has-mono i rs hf
...    | true with isG1 (checked r)
...       | true  = refl
...       | false = has-mono i rs hf

tail-unique : ∀ r rs → Grade1Unique (r ∷ rs) → Grade1Unique rs
tail-unique r rs u i h = go (obj r ≡ᵇ i) refl
  where
  go : (b : Bool) → (obj r ≡ᵇ i) ≡ b → count i rs ≡ 1
  go false eb = subst (λ n → n ≡ 1) (count-tail eb) (u i (has-tail eb h))
    where
    count-tail : (obj r ≡ᵇ i) ≡ false → count i (r ∷ rs) ≡ count i rs
    count-tail eq rewrite eq = refl
    has-tail : (obj r ≡ᵇ i) ≡ false → hasG1 i rs ≡ true → hasG1 i (r ∷ rs) ≡ true
    has-tail eq hf rewrite eq = hf
  go true eb =
    ⊥-elim (true≢false (trans (sym h) (count0-has i rs (peel eb))))
    where
    hasAll : hasG1 i (r ∷ rs) ≡ true
    hasAll rewrite h = ∨-trueʳ ((obj r ≡ᵇ i) ∧ isG1 (checked r))
    count-one : (obj r ≡ᵇ i) ≡ true → count i (r ∷ rs) ≡ suc (count i rs)
    count-one eq rewrite eq = refl
    peel : (obj r ≡ᵇ i) ≡ true → count i rs ≡ 0
    peel eq = suc-inj (subst (λ n → n ≡ 1) (count-one eq) (u i hasAll))

mutual
  filter-unique : ∀ rs → Grade1Unique rs → Grade1Unique (filterKeep rs)
  filter-unique []       u = u
  filter-unique (r ∷ rs) u = go (isZeroGrade (residual r)) refl
    where
    go : (z : Bool) → isZeroGrade (residual r) ≡ z → Grade1Unique (filterKeep (r ∷ rs))
    go true ez =
      subst Grade1Unique (sym (drop ez)) (filter-unique rs (tail-unique r rs u))
      where
      drop : isZeroGrade (residual r) ≡ true → filterKeep (r ∷ rs) ≡ filterKeep rs
      drop eq rewrite eq = refl
    go false ez =
      subst Grade1Unique (sym (keep ez)) (kept-unique r rs u ez)
      where
      keep : isZeroGrade (residual r) ≡ false →
             filterKeep (r ∷ rs) ≡ r ∷ filterKeep rs
      keep eq rewrite eq = refl

  kept-unique : ∀ r rs →
    Grade1Unique (r ∷ rs) →
    isZeroGrade (residual r) ≡ false →
    Grade1Unique (r ∷ filterKeep rs)
  kept-unique r rs u eqz i h = go (obj r ≡ᵇ i) refl
    where
    go : (b : Bool) → (obj r ≡ᵇ i) ≡ b → count i (r ∷ filterKeep rs) ≡ 1
    go false eb =
      subst (λ n → n ≡ 1) (sym (count-drop eb))
        (filter-unique rs (tail-unique r rs u) i (has-drop eb h))
      where
      count-drop : (obj r ≡ᵇ i) ≡ false →
                   count i (r ∷ filterKeep rs) ≡ count i (filterKeep rs)
      count-drop eq rewrite eq = refl
      has-drop : (obj r ≡ᵇ i) ≡ false →
                 hasG1 i (r ∷ filterKeep rs) ≡ true →
                 hasG1 i (filterKeep rs) ≡ true
      has-drop eq hf rewrite eq = hf
    go true eb = onG (isG1 (checked r)) refl
      where
      onG : (g : Bool) → isG1 (checked r) ≡ g → count i (r ∷ filterKeep rs) ≡ 1
      onG true eg =
        subst (λ n → n ≡ 1) (count-head eb)
          (cong suc (count-filter-0 i rs (peel eb eg)))
        where
        count-head : (obj r ≡ᵇ i) ≡ true →
                     suc (count i (filterKeep rs)) ≡ count i (r ∷ filterKeep rs)
        count-head eq rewrite eq = refl
        count-one : (obj r ≡ᵇ i) ≡ true → count i (r ∷ rs) ≡ suc (count i rs)
        count-one eq rewrite eq = refl
        hasCons : (obj r ≡ᵇ i) ≡ true → isG1 (checked r) ≡ true →
                  hasG1 i (r ∷ rs) ≡ true
        hasCons eq eg' rewrite eq | eg' = refl
        peel : (obj r ≡ᵇ i) ≡ true → isG1 (checked r) ≡ true → count i rs ≡ 0
        peel eq eg' = suc-inj (subst (λ n → n ≡ 1) (count-one eq) (u i (hasCons eq eg')))
      onG false eg =
        ⊥-elim (true≢false (trans (sym (has-flat eb eg h))
          (count0-has i (filterKeep rs)
            (count-filter-0 i rs (old eb eg (has-mono i rs (has-flat eb eg h)))))))
        where
        has-flat : (obj r ≡ᵇ i) ≡ true → isG1 (checked r) ≡ false →
                   hasG1 i (r ∷ filterKeep rs) ≡ true →
                   hasG1 i (filterKeep rs) ≡ true
        has-flat eq eg' hf rewrite eq | eg' = hf
        count-one : (obj r ≡ᵇ i) ≡ true → count i (r ∷ rs) ≡ suc (count i rs)
        count-one eq rewrite eq = refl
        hasOld : (obj r ≡ᵇ i) ≡ true → isG1 (checked r) ≡ false →
                 hasG1 i rs ≡ true → hasG1 i (r ∷ rs) ≡ true
        hasOld eq eg' hf rewrite eq | eg' = hf
        old : (obj r ≡ᵇ i) ≡ true → isG1 (checked r) ≡ false →
              hasG1 i rs ≡ true → count i rs ≡ 0
        old eq eg' hf =
          suc-inj (subst (λ n → n ≡ 1) (count-one eq) (u i (hasOld eq eg' hf)))

bound-filter : ∀ {n} rs → Bound n rs → Bound n (filterKeep rs)
bound-filter []       bnil = bnil
bound-filter (r ∷ rs) (bcons lt rest) with isZeroGrade (residual r)
... | true  = bound-filter rs rest
... | false = bcons lt (bound-filter rs rest)

filter-++ : ∀ xs ys → filterKeep (xs ++ ys) ≡ filterKeep xs ++ filterKeep ys
filter-++ []       ys = refl
filter-++ (r ∷ xs) ys with isZeroGrade (residual r)
... | true  = filter-++ xs ys
... | false rewrite filter-++ xs ys = refl

filter-msg : ∀ ms → mapRef (filterMsg ms) ≡ filterKeep (mapRef ms)
filter-msg []           = refl
filter-msg (msg r ∷ ms) with isZeroGrade (residual r)
... | true  = filter-msg ms
... | false rewrite filter-msg ms = refl

clean-refs : ∀ p → refsP (clean p) ≡ filterKeep (refsP p)
clean-refs p =
  trans (cong (filterKeep (roots p) ++_) (filter-msg (inbox p)))
        (sym (filter-++ (roots p) (mapRef (inbox p))))

refs-cleaned : ∀ ps → refsPs (map clean ps) ≡ filterKeep (refsPs ps)
refs-cleaned []       = refl
refs-cleaned (p ∷ ps) =
  trans (cong (refsP (clean p) ++_) (refs-cleaned ps))
  (trans (cong (_++ filterKeep (refsPs ps)) (clean-refs p))
         (sym (filter-++ (refsP p) (refsPs ps))))

length-walk : ∀ rs n os → length (walk rs n os) ≡ length os
length-walk rs n []       = refl
length-walk rs n (_ ∷ os) rewrite length-walk rs (suc n) os = refl

collect-wf : ∀ s → WF s → WF (collect s)
collect-wf (sys h ps) (bd , uq) =
  subst (λ n → Bound n (refsPs (map clean ps)))
        (sym (length-walk (refsPs ps) zero h))
        (subst (Bound (length h)) (sym (refs-cleaned ps)) (bound-filter (refsPs ps) bd))
  , subst Grade1Unique (sym (refs-cleaned ps)) (filter-unique (refsPs ps) uq)

------------------------------------------------------------------------
-- Dereference replaces a root with the spent root. Object and checked
-- grade stay, so the multiset of (object, checked grade) stays.
------------------------------------------------------------------------

deref-wf : ∀ h ps i j t →
  deref run (sys h ps) i j ≡ just t →
  WF (sys h ps) →
  WF t
deref-wf h ps i j t eq (bd , uq) = root (rootAt (sys h ps) i j) eq refl
  where
  root : (m : Maybe Ref) →
         derefAt (sys h ps) i j m ≡ just t →
         rootAt (sys h ps) i j ≡ m →
         WF t
  root nothing () _
  root (just r) eq rk = spent (spendRef r) eq refl rk
    where
    spent : (m : Maybe Ref) →
            derefSpent h ps i j r m ≡ just t →
            spendRef r ≡ m →
            rootAt (sys h ps) i j ≡ just r →
            WF t
    spent nothing () _ _
    spent (just r') eq es rk = via (putRoot ps i j r') eq refl
      where
      via : (m : Maybe (List Proc)) →
            mapSys h m ≡ just t →
            putRoot ps i j r' ≡ m →
            WF t
      via nothing () _
      via (just ps') refl ep =
        let p = proj₁ (root-lookup ps i j r rk)
            lk = proj₁ (proj₂ (root-lookup ps i j r rk))
            lr = proj₂ (proj₂ (root-lookup ps i j r rk))
            eo = spendRef-obj r r' es
            ec = spendRef-checked r r' es
            cq = λ k → put-count k i j ps p r r' ps' lk lr eo ep
            hq = λ k → put-has k i j ps p r r' ps' lk lr eo ec ep
        in put-bound i j ps p r r' ps' bd lk lr eo ep , same-unique {rs = refsPs ps} {rs' = refsPs ps'} cq hq uq

------------------------------------------------------------------------
-- Receive moves a message into roots. The reference list is unchanged.
------------------------------------------------------------------------

recv-refs : ∀ p r ms →
  inbox p ≡ msg r ∷ ms →
  refsP (record p { roots = roots p ++ r ∷ [] ; inbox = ms }) ≡ refsP p
recv-refs p r ms eq rewrite eq = ++-assoc (roots p) (r ∷ []) (mapRef ms)

recv-wf : ∀ h ps i t →
  recv (sys h ps) i ≡ just t →
  WF (sys h ps) →
  WF t
recv-wf h ps i t eq (bd , uq) = at (lookup ps i) eq refl
  where
  at : (m : Maybe Proc) →
       recvAt h ps i m ≡ just t →
       lookup ps i ≡ m →
       WF t
  at nothing () _
  at (just p) eq lk rewrite lk = fromInbox (inbox p) eq refl
    where
    fromInbox : (ms : List Msg) →
                recvInbox h ps i p ms ≡ just t →
                inbox p ≡ ms →
                WF t
    fromInbox [] () _
    fromInbox (msg r ∷ ms) eq em = upd (update i p' ps) eq refl
      where
      p' : Proc
      p' = record p { roots = roots p ++ r ∷ [] ; inbox = ms }
      same : refsP p' ≡ refsP p
      same = recv-refs p r ms em
      upd : (m : Maybe (List Proc)) →
            mapSys h m ≡ just t →
            update i p' ps ≡ m →
            WF t
      upd nothing () _
      upd (just ps') refl eu =
        let cq = λ k → upd-count k i ps p p' ps' lk eu (cong (count k) same)
            hq = λ k → upd-has k i ps p p' ps' lk eu (cong (hasG1 k) same)
            bp = subst (Bound (length h)) (sym same) (lookup-bound i ps p bd lk)
        in upd-bound i ps p p' ps' bd lk eu bp , same-unique {rs = refsPs ps} {rs' = refsPs ps'} cq hq uq

------------------------------------------------------------------------
-- Allocation appends a fresh cell. Its index is outside the old bound.
------------------------------------------------------------------------

snoc-root-count : ∀ i p r →
  count i (refsP (record p { roots = roots p ++ r ∷ [] })) ≡
  count i (refsP p) + ext (obj r ≡ᵇ i)
snoc-root-count i p r =
  trans (count-++ i (roots p ++ r ∷ []) (mapRef (inbox p)))
  (trans (cong (_+ count i (mapRef (inbox p))) (count-snoc i (roots p) r))
  (trans (+-assoc (count i (roots p)) (ext (obj r ≡ᵇ i)) (count i (mapRef (inbox p))))
  (trans (cong (count i (roots p) +_) (+-comm (ext (obj r ≡ᵇ i)) (count i (mapRef (inbox p)))))
  (trans (sym (+-assoc (count i (roots p)) (count i (mapRef (inbox p))) (ext (obj r ≡ᵇ i))))
         (cong (_+ ext (obj r ≡ᵇ i)) (sym (count-++ i (roots p) (mapRef (inbox p)))))))))

snoc-root-has : ∀ i p r →
  hasG1 i (refsP (record p { roots = roots p ++ r ∷ [] })) ≡
    hasG1 i (refsP p) ∨ ((obj r ≡ᵇ i) ∧ isG1 (checked r))
snoc-root-has i p r =
  trans (has-++ i (roots p ++ r ∷ []) (mapRef (inbox p)))
  (trans (cong (_∨ hasG1 i (mapRef (inbox p))) (has-snoc i (roots p) r))
  (trans (∨-assoc (hasG1 i (roots p)) ((obj r ≡ᵇ i) ∧ isG1 (checked r)) (hasG1 i (mapRef (inbox p))))
  (trans (cong (hasG1 i (roots p) ∨_) (∨-comm ((obj r ≡ᵇ i) ∧ isG1 (checked r)) (hasG1 i (mapRef (inbox p)))))
  (trans (sym (∨-assoc (hasG1 i (roots p)) (hasG1 i (mapRef (inbox p))) ((obj r ≡ᵇ i) ∧ isG1 (checked r))))
         (cong (_∨ ((obj r ≡ᵇ i) ∧ isG1 (checked r)))
               (sym (has-++ i (roots p) (mapRef (inbox p)))))))))

snoc-root-bound : ∀ {n} p r →
  Bound n (refsP p) →
  obj r < n →
  Bound n (refsP (record p { roots = roots p ++ r ∷ [] }))
snoc-root-bound p r bd olt with bound-split (roots p) (mapRef (inbox p)) bd
... | br , bi = bound-++ (bound-snoc br olt) bi

alloc-wf : ∀ h ps i g v t →
  alloc (sys h ps) i g v ≡ just t →
  WF (sys h ps) →
  WF t
alloc-wf h ps i g v t eq (bd , uq) = at (lookup ps i) eq refl
  where
  r : Ref
  r = ref (length h) g g (selfKept g)
  at : (m : Maybe Proc) →
       mapSys (h ++ cell v live ∷ []) (addRoot ps i r) ≡ just t →
       lookup ps i ≡ m →
       WF t
  at nothing eq lk rewrite lk with eq
  ... | ()
  at (just p) eq lk rewrite lk = upd (update i p' ps) eq refl
    where
    p' : Proc
    p' = record p { roots = roots p ++ r ∷ [] }
    upd : (m : Maybe (List Proc)) →
          mapSys (h ++ cell v live ∷ []) m ≡ just t →
          update i p' ps ≡ m →
          WF t
    upd nothing () _
    upd (just ps') refl eu =
      let n = length h
          bd' = bound-mono (≤-step ≤-refl) bd
          bp  = snoc-root-bound p r (bound-mono (≤-step ≤-refl) (lookup-bound i ps p bd lk)) (fresh-< n)
          bdT = upd-bound i ps p p' ps' bd' lk eu bp
          len = length-snoc h (cell v live)
      in subst (λ n → Bound n (refsPs ps')) (sym len) bdT
       , alloc-unique
      where
      alloc-unique : Grade1Unique (refsPs ps')
      alloc-unique k hf = go (length h ≡ᵇ k) refl
        where
        go : (b : Bool) → (length h ≡ᵇ k) ≡ b → count k (refsPs ps') ≡ 1
        go false eb =
          trans (trans (cq) (cong (count k (refsPs ps) +_) (ext0 eb)))
                (trans (+-identityʳ (count k (refsPs ps))) (uq k (hz eb)))
          where
          ext0 : (length h ≡ᵇ k) ≡ false → ext (obj r ≡ᵇ k) ≡ 0
          ext0 eq rewrite eq = refl
          bit : (length h ≡ᵇ k) ≡ false → ((obj r ≡ᵇ k) ∧ isG1 (checked r)) ≡ false
          bit eq rewrite eq = refl
          has-eq : (length h ≡ᵇ k) ≡ false → hasG1 k (refsP p') ≡ hasG1 k (refsP p)
          has-eq eq =
            trans (snoc-root-has k p r)
            (trans (cong (hasG1 k (refsP p) ∨_) (bit eq))
                   (∨-falseʳ (hasG1 k (refsP p))))
          cq : count k (refsPs ps') ≡ count k (refsPs ps) + ext (obj r ≡ᵇ k)
          cq = upd-add k i ps p p' ps' (ext (obj r ≡ᵇ k)) lk eu (snoc-root-count k p r)
          hz : (length h ≡ᵇ k) ≡ false → hasG1 k (refsPs ps) ≡ true
          hz eq = trans (sym (upd-has k i ps p p' ps' lk eu (has-eq eq))) hf
        go true eb =
          trans cq (trans (cong (_+ ext (obj r ≡ᵇ k)) z) (one eb))
          where
          cq : count k (refsPs ps') ≡ count k (refsPs ps) + ext (obj r ≡ᵇ k)
          cq = upd-add k i ps p p' ps' (ext (obj r ≡ᵇ k)) lk eu (snoc-root-count k p r)
          z : count k (refsPs ps) ≡ 0
          z = subst (λ n → count n (refsPs ps) ≡ 0) (≡ᵇ-sound (length h) k eb)
                    (bound-count0 bd (length h) ≤-refl)
          one : (length h ≡ᵇ k) ≡ true → zero + ext (obj r ≡ᵇ k) ≡ 1
          one eq rewrite eq = refl

------------------------------------------------------------------------
-- Reuse overwrites one spent g1 root in place. The object index is
-- unchanged, and the runtime gate says that index occurs once.
------------------------------------------------------------------------

reuse-wf : ∀ h ps i j g v t →
  reuse (sys h ps) i j g v ≡ just t →
  WF (sys h ps) →
  WF t
reuse-wf h ps i j g v t eq (bd , uq) = from (rootAt (sys h ps) i j) eq refl
  where
  from : (m : Maybe Ref) →
         reuse (sys h ps) i j g v ≡ just t →
         rootAt (sys h ps) i j ≡ m →
         WF t
  from nothing e rk =
    ⊥-elim (nothing≢just (trans (sym (cong (reuseFrom (sys h ps) i j g v) rk)) e))
  from (just r) e rk rewrite rk =
    gates (isG1 (checked r)) (isZeroGrade (residual r))
          (count (obj r) (refsPs ps) ≡ᵇ 1) e refl refl refl
    where
    no1 : ∀ b c → reuseOk (sys h ps) i j g v r false b c ≡ nothing
    no1 _ _ = refl
    no2 : ∀ c → reuseOk (sys h ps) i j g v r true false c ≡ nothing
    no2 _ = refl
    no3 : reuseOk (sys h ps) i j g v r true true false ≡ nothing
    no3 = refl
    gates : (a b c : Bool) →
            reuseOk (sys h ps) i j g v r a b c ≡ just t →
            isG1 (checked r) ≡ a →
            isZeroGrade (residual r) ≡ b →
            (count (obj r) (refsPs ps) ≡ᵇ 1) ≡ c →
            WF t
    gates false b c eG _ _ _ =
      ⊥-elim (nothing≢just (trans (sym (no1 b c)) eG))
    gates true false c eG _ _ _ =
      ⊥-elim (nothing≢just (trans (sym (no2 c)) eG))
    gates true true false eG _ _ _ =
      ⊥-elim (nothing≢just (trans (sym no3) eG))
    gates true true true eG _ _ ec = via (putRoot ps i j r') eG refl
      where
      r' : Ref
      r' = ref (obj r) g g (selfKept g)
      via : (m : Maybe (List Proc)) →
            mapSys (poke h (obj r) v) m ≡ just t →
            putRoot ps i j r' ≡ m →
            WF t
      via nothing () _
      via (just ps') refl ep =
        let p  = proj₁ (root-lookup ps i j r rk)
            lk = proj₁ (proj₂ (root-lookup ps i j r rk))
            lr = proj₂ (proj₂ (root-lookup ps i j r rk))
            bd' = put-bound i j ps p r r' ps' bd lk lr refl ep
        in subst (λ n → Bound n (refsPs ps')) (sym (length-poke h (obj r) v)) bd'
         , reused p lk lr
        where
        reused : (p : Proc) →
                 lookup ps i ≡ just p →
                 lookup (roots p) j ≡ just r →
                 Grade1Unique (refsPs ps')
        reused p lk lr k hf with obj r ≡ᵇ k in eb
        ... | false =
          trans (put-count k i j ps p r r' ps' lk lr refl ep)
                (uq k (trans (sym (put-has-miss k i j ps p r r' ps' lk lr refl eb ep)) hf))
        ... | true =
          trans (put-count k i j ps p r r' ps' lk lr refl ep)
                (trans (cong (λ n → count n (refsPs ps)) (sym (≡ᵇ-sound (obj r) k eb)))
                       (≡ᵇ-sound (count (obj r) (refsPs ps)) 1 ec))

reuse-in-place : ∀ h ps i j g v t r →
  rootAt (sys h ps) i j ≡ just r →
  reuse (sys h ps) i j g v ≡ just t →
  isG1 (checked r) ≡ true
  × isZeroGrade (residual r) ≡ true
  × count (obj r) (refsPs ps) ≡ 1
reuse-in-place h ps i j g v t r rk eq rewrite rk =
  gates (isG1 (checked r)) (isZeroGrade (residual r))
        (count (obj r) (refsPs ps) ≡ᵇ 1) eq refl refl refl
  where
  no1 : ∀ b c → reuseOk (sys h ps) i j g v r false b c ≡ nothing
  no1 _ _ = refl
  no2 : ∀ c → reuseOk (sys h ps) i j g v r true false c ≡ nothing
  no2 _ = refl
  no3 : reuseOk (sys h ps) i j g v r true true false ≡ nothing
  no3 = refl
  gates : (a b c : Bool) →
          reuseOk (sys h ps) i j g v r a b c ≡ just t →
          isG1 (checked r) ≡ a →
          isZeroGrade (residual r) ≡ b →
          (count (obj r) (refsPs ps) ≡ᵇ 1) ≡ c →
          isG1 (checked r) ≡ true
          × isZeroGrade (residual r) ≡ true
          × count (obj r) (refsPs ps) ≡ 1
  gates false b c e _ _ _ =
    ⊥-elim (nothing≢just (trans (sym (no1 b c)) e))
  gates true false c e _ _ _ =
    ⊥-elim (nothing≢just (trans (sym (no2 c)) e))
  gates true true false e _ _ _ =
    ⊥-elim (nothing≢just (trans (sym no3) e))
  gates true true true _ ea eb ec =
    ea , eb , ≡ᵇ-sound (count (obj r) (refsPs ps)) 1 ec

------------------------------------------------------------------------
-- Copying adds an alias. The copied grade is not g1, so a g1 object
-- cannot be the one that was copied: its count does not grow.
------------------------------------------------------------------------

∧-falseʳ : ∀ b → (b ∧ false) ≡ false
∧-falseʳ true  = refl
∧-falseʳ false = refl

suc-split : ∀ a b → suc a + b ≡ suc zero → a ≡ zero × b ≡ zero
suc-split a b eq = +-zero a b (suc-inj eq)

post-has-copy : ∀ i p r →
  isG1 (checked r) ≡ false →
  hasG1 i (refsP (post p r)) ≡ hasG1 i (refsP p)
post-has-copy i p r ng =
  trans (post-has i p r)
  (trans (cong (hasG1 i (refsP p) ∨_)
               (trans (cong ((obj r ≡ᵇ i) ∧_) ng) (∧-falseʳ (obj r ≡ᵇ i))))
         (∨-falseʳ (hasG1 i (refsP p))))

alias-ext : ∀ k sp sj r ys ps si →
  lookup ps si ≡ just sp →
  removeAt sj (roots sp) ≡ just (r , ys) →
  isG1 (checked r) ≡ false →
  Grade1Unique (refsPs ps) →
  hasG1 k (refsPs ps) ≡ true →
  ext (obj r ≡ᵇ k) ≡ 0
alias-ext k sp sj r ys ps si lk rm ng uq hf = contra (obj r ≡ᵇ k) refl
  where
  rest : List Ref
  rest = ys ++ mapRef (inbox sp)
  contra : (b : Bool) → (obj r ≡ᵇ k) ≡ b → ext (obj r ≡ᵇ k) ≡ 0
  contra false eb rewrite eb = refl
  contra true  eb = ⊥-elim (true≢false (trans (sym hf) gone))
    where
    ext1 : ext (obj r ≡ᵇ k) ≡ 1
    ext1 rewrite eb = refl
    cSp : count k (refsP sp) ≡ suc (count k rest)
    cSp = trans (proc-drop-count k sp sj r ys rm) (cong (_+ count k rest) ext1)
    eq1 : suc (count k rest) + count k (others si ps) ≡ suc zero
    eq1 = trans (sym (cong (_+ count k (others si ps)) cSp))
                (trans (sym (lookup-count k si ps sp lk)) (uq k hf))
    zR : count k rest ≡ zero
    zR = proj₁ (suc-split (count k rest) (count k (others si ps)) eq1)
    zO : count k (others si ps) ≡ zero
    zO = proj₂ (suc-split (count k rest) (count k (others si ps)) eq1)
    hRest : hasG1 k rest ≡ false
    hRest = count0-has k rest zR
    hOth : hasG1 k (others si ps) ≡ false
    hOth = count0-has k (others si ps) zO
    flat : ((obj r ≡ᵇ k) ∧ isG1 (checked r)) ≡ false
    flat = trans (cong (_∧ isG1 (checked r)) eb) ng
    hSp : hasG1 k (refsP sp) ≡ false
    hSp = trans (proc-drop-has k sp sj r ys rm)
                (trans (cong (_∨ hasG1 k rest) flat) hRest)
    gone : hasG1 k (refsPs ps) ≡ false
    gone = trans (lookup-has k si ps sp lk)
           (trans (cong (hasG1 k (refsP sp) ∨_) hOth)
           (trans (∨-falseʳ (hasG1 k (refsP sp))) hSp))

------------------------------------------------------------------------
-- Send. A move preserves every count. A copy preserves g1 counts
-- because the extra alias is not itself g1.
------------------------------------------------------------------------

send-wf : ∀ h ps si sj ri t →
  send (sys h ps) si sj ri ≡ just t →
  WF (sys h ps) →
  WF t
send-wf h ps si sj ri t eq (bd , uq) = from (lookup ps si) eq refl
  where
  from : (m : Maybe Proc) →
         sendFrom m si sj ri h ps ≡ just t →
         lookup ps si ≡ m →
         WF t
  from nothing () _
  from (just sp) eS lk = rooted (removeAt sj (roots sp)) eS refl
    where
    rooted : (m : Maybe (Ref × List Ref)) →
             sendTaken (dropRoot sp m) si ri h ps ≡ just t →
             removeAt sj (roots sp) ≡ m →
             WF t
    rooted nothing () _
    rooted (just (r , ys)) eS rm =
      class (isZeroGrade (residual r)) (kind (checked r)) eS refl refl
      where
      sp' : Proc
      sp' = record sp { roots = ys }
      class : (z : Bool) (kd : Maybe Kind) →
              dispatch z kd r sp' si ri h ps ≡ just t →
              isZeroGrade (residual r) ≡ z →
              kind (checked r) ≡ kd →
              WF t
      class true  _        () _ _
      class false nothing  () _ _
      class false (just Kcopy) eS _ ek = copied (lookup ps ri) eS refl
        where
        ng : isG1 (checked r) ≡ false
        ng = copy-not-g1 (checked r) ek
        copied : (m : Maybe Proc) →
                 mapSys h (addMsg ps ri r) ≡ just t →
                 lookup ps ri ≡ m →
                 WF t
        copied nothing e2 lk2 rewrite lk2 with e2
        ... | ()
        copied (just rp) e2 lk2 rewrite lk2 = updated (update ri (post rp r) ps) e2 refl
          where
          updated : (m : Maybe (List Proc)) →
                    mapSys h m ≡ just t →
                    update ri (post rp r) ps ≡ m →
                    WF t
          updated nothing () _
          updated (just ps') refl eu =
            let _ , olt = proc-drop-bound sp sj r ys (lookup-bound si ps sp bd lk) rm
                brp = lookup-bound ri ps rp bd lk2
                bp  = post-bound rp r brp olt
                bd' = upd-bound ri ps rp (post rp r) ps' bd lk2 eu bp
                cq  = λ k → upd-add k ri ps rp (post rp r) ps'
                              (ext (obj r ≡ᵇ k)) lk2 eu (post-count k rp r)
                hq  = λ k → upd-has k ri ps rp (post rp r) ps' lk2 eu
                              (post-has-copy k rp r ng)
                uq' : Grade1Unique (refsPs ps')
                uq' k hf =
                  let old = trans (sym (hq k)) hf in
                  trans (cq k)
                  (trans (cong (count k (refsPs ps) +_) (alias-ext k sp sj r ys ps si lk rm ng uq old))
                  (trans (+-identityʳ (count k (refsPs ps)))
                         (uq k old)))
            in bd' , uq'
      class false (just Kmove) eS _ _ = moved (si ≡ᵇ ri) eS refl
        where
        moved : (b : Bool) →
                moveTo r sp' si ri h ps ≡ just t →
                (si ≡ᵇ ri) ≡ b →
                WF t
        moved true eM eb rewrite eb = via (update si (post sp' r) ps) eM refl
          where
          via : (m : Maybe (List Proc)) →
                mapSys h m ≡ just t →
                update si (post sp' r) ps ≡ m →
                WF t
          via nothing () _
          via (just ps') refl eu =
            let cq = λ k → upd-count k si ps sp (post sp' r) ps' lk eu
                             (self-count k sp sj r ys rm)
                hq = λ k → upd-has k si ps sp (post sp' r) ps' lk eu
                             (self-has k sp sj r ys rm)
                db , olt = proc-drop-bound sp sj r ys (lookup-bound si ps sp bd lk) rm
                bp = post-bound sp' r db olt
            in upd-bound si ps sp (post sp' r) ps' bd lk eu bp , same-unique {rs = refsPs ps} {rs' = refsPs ps'} cq hq uq
        moved false eM eb rewrite eb = step1 (update si sp' ps) eM refl
          where
          step1 : (m : Maybe (List Proc)) →
                  moveOther r si ri h ps m ≡ just t →
                  update si sp' ps ≡ m →
                  WF t
          step1 nothing () _
          step1 (just ps1) e1 eu1 = step2 (lookup ps1 ri) e1 refl
            where
            step2 : (m : Maybe Proc) →
                    moveRecv r ri h ps1 m ≡ just t →
                    lookup ps1 ri ≡ m →
                    WF t
            step2 nothing () _
            step2 (just rp) e2 lr = step3 (update ri (post rp r) ps1) e2 refl
              where
              step3 : (m : Maybe (List Proc)) →
                      mapSys h m ≡ just t →
                      update ri (post rp r) ps1 ≡ m →
                      WF t
              step3 nothing () _
              step3 (just ps') refl eu2 =
                let cq = λ k →
                      let c1 = upd-sub k si ps sp sp' ps1 (ext (obj r ≡ᵇ k)) lk eu1
                                 (proc-drop-count k sp sj r ys rm)
                          c2 = upd-add k ri ps1 rp (post rp r) ps' (ext (obj r ≡ᵇ k)) lr eu2
                                 (post-count k rp r)
                      in trans c2 (trans (+-comm (count k (refsPs ps1)) (ext (obj r ≡ᵇ k))) (sym c1))
                    hq = λ k →
                      let h1 = upd-or-left k si ps sp sp' ps1
                                 ((obj r ≡ᵇ k) ∧ isG1 (checked r)) lk eu1
                                 (proc-drop-has k sp sj r ys rm)
                          h2 = upd-or-right k ri ps1 rp (post rp r) ps'
                                 ((obj r ≡ᵇ k) ∧ isG1 (checked r)) lr eu2
                                 (post-has k rp r)
                      in trans h2
                         (trans (∨-comm (hasG1 k (refsPs ps1)) ((obj r ≡ᵇ k) ∧ isG1 (checked r)))
                                (sym h1))
                    db , olt = proc-drop-bound sp sj r ys (lookup-bound si ps sp bd lk) rm
                    bd1 = upd-bound si ps sp sp' ps1 bd lk eu1 db
                    brp = lookup-bound ri ps1 rp bd1 lr
                    bp  = post-bound rp r brp olt
                in upd-bound ri ps1 rp (post rp r) ps' bd1 lr eu2 bp , same-unique {rs = refsPs ps} {rs' = refsPs ps'} cq hq uq


------------------------------------------------------------------------
-- A successful g1 send is exactly a move. Counts stay, the heap stays.
------------------------------------------------------------------------

-- Unfolding `send` by `rewrite` on `send-g1-moves` itself leaves the
-- constraint solver with unsolved metas. Each equation is its own
-- top-level clause, and the boolean test is `subst`, not a nested rewrite.
abstract
  send-g1-red : ∀ h ps si sj ri t r ys sp →
    lookup ps si ≡ just sp →
    removeAt sj (roots sp) ≡ just (r , ys) →
    checked r ≡ g1 →
    isZeroGrade (residual r) ≡ false →
    send (sys h ps) si sj ri ≡ just t →
    moveTo r (record sp { roots = ys }) si ri h ps ≡ just t
  send-g1-red h ps si sj ri t r ys sp lk rm cg nz eq
    rewrite lk | rm | cg | nz = eq

keep-on : ∀ h ps si sj ri t r ys sp b →
  lookup ps si ≡ just sp →
  removeAt sj (roots sp) ≡ just (r , ys) →
  (si ≡ᵇ ri) ≡ b →
  moveTo r (record sp { roots = ys }) si ri h ps ≡ just t →
  heap t ≡ h
  × (∀ k → count k (refsOf t) ≡ count k (refsPs ps))
keep-on h ps si sj ri t r ys sp true lk rm eb eq =
  via (update si (post sp' r) ps) (as true eb) refl
  where
  sp' : Proc
  sp' = record sp { roots = ys }
  as : (b : Bool) → (si ≡ᵇ ri) ≡ b → moveToOn r sp' si ri h ps b ≡ just t
  as b eb' = subst (λ c → moveToOn r sp' si ri h ps c ≡ just t) eb' eq
  via : (m : Maybe (List Proc)) →
        mapSys h m ≡ just t →
        update si (post sp' r) ps ≡ m →
        heap t ≡ h
        × (∀ k → count k (refsOf t) ≡ count k (refsPs ps))
  via nothing () _
  via (just ps') refl eu =
    refl
    , (λ k → upd-count k si ps sp (post sp' r) ps' lk eu
               (self-count k sp sj r ys rm))
keep-on h ps si sj ri t r ys sp false lk rm eb eq =
  step1 (update si sp' ps) (as false eb) refl
  where
  sp' : Proc
  sp' = record sp { roots = ys }
  as : (b : Bool) → (si ≡ᵇ ri) ≡ b → moveToOn r sp' si ri h ps b ≡ just t
  as b eb' = subst (λ c → moveToOn r sp' si ri h ps c ≡ just t) eb' eq
  step1 : (m : Maybe (List Proc)) →
          moveOther r si ri h ps m ≡ just t →
          update si sp' ps ≡ m →
          heap t ≡ h
          × (∀ k → count k (refsOf t) ≡ count k (refsPs ps))
  step1 nothing () _
  step1 (just ps1) e1 eu1 = step2 (lookup ps1 ri) e1 refl
    where
    step2 : (m : Maybe Proc) →
            moveRecv r ri h ps1 m ≡ just t →
            lookup ps1 ri ≡ m →
            heap t ≡ h
            × (∀ k → count k (refsOf t) ≡ count k (refsPs ps))
    step2 nothing () _
    step2 (just rp) e2 lr = step3 (update ri (post rp r) ps1) e2 refl
      where
      step3 : (m : Maybe (List Proc)) →
              mapSys h m ≡ just t →
              update ri (post rp r) ps1 ≡ m →
              heap t ≡ h
              × (∀ k → count k (refsOf t) ≡ count k (refsPs ps))
      step3 nothing () _
      step3 (just ps') refl eu2 =
        refl
        , (λ k →
            let c1 = upd-sub k si ps sp sp' ps1 (ext (obj r ≡ᵇ k)) lk eu1
                       (proc-drop-count k sp sj r ys rm)
                c2 = upd-add k ri ps1 rp (post rp r) ps' (ext (obj r ≡ᵇ k)) lr eu2
                       (post-count k rp r)
            in trans c2 (trans (+-comm (count k (refsPs ps1)) (ext (obj r ≡ᵇ k))) (sym c1)))

send-g1-keep : ∀ h ps si sj ri t r ys sp →
  lookup ps si ≡ just sp →
  removeAt sj (roots sp) ≡ just (r , ys) →
  checked r ≡ g1 →
  isZeroGrade (residual r) ≡ false →
  send (sys h ps) si sj ri ≡ just t →
  heap t ≡ h
  × (∀ k → count k (refsOf t) ≡ count k (refsPs ps))
send-g1-keep h ps si sj ri t r ys sp lk rm cg nz eq =
  keep-on h ps si sj ri t r ys sp (si ≡ᵇ ri) lk rm refl
    (send-g1-red h ps si sj ri t r ys sp lk rm cg nz eq)

send-g1-moves : ∀ h ps si sj ri t r ys sp →
  lookup ps si ≡ just sp →
  removeAt sj (roots sp) ≡ just (r , ys) →
  checked r ≡ g1 →
  isZeroGrade (residual r) ≡ false →
  send (sys h ps) si sj ri ≡ just t →
  heap t ≡ h
  × (∀ k → count k (refsOf t) ≡ count k (refsPs ps))
  × moveTo r (record sp { roots = ys }) si ri h ps ≡ just t
send-g1-moves h ps si sj ri t r ys sp lk rm cg nz eq =
  proj₁ kept , proj₂ kept , send-g1-red h ps si sj ri t r ys sp lk rm cg nz eq
  where
  kept : heap t ≡ h × (∀ k → count k (refsOf t) ≡ count k (refsPs ps))
  kept = send-g1-keep h ps si sj ri t r ys sp lk rm cg nz eq

------------------------------------------------------------------------
-- Every step preserves the bound and grade-1 uniqueness.
------------------------------------------------------------------------

step-preserves-grade1 : ∀ {s t} → Step s t → WF s → WF t
step-preserves-grade1 {t = t} step wf = go _ step wf
  where
  go : ∀ s → Step s t → WF s → WF t
  go (sys h ps) (step-deref {i = i} {j = j} eq) wf =
    deref-wf h ps i j t eq wf
  go (sys h ps) (step-send {i = i} {j = j} {k = k} eq) wf =
    send-wf h ps i j k t eq wf
  go (sys h ps) (step-recv {i = i} eq) wf =
    recv-wf h ps i t eq wf
  go (sys h ps) (step-alloc {i = i} {g = g} {v = v} eq) wf =
    alloc-wf h ps i g v t eq wf
  go (sys h ps) (step-reuse {i = i} {j = j} {g = g} {v = v} eq) wf =
    reuse-wf h ps i j g v t eq wf
  go s step-collect wf = collect-wf s wf

