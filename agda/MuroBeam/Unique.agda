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

open import Data.Bool.Base using (Bool; true; false; not; _∨_; _∧_)
open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; _≡ᵇ_; s≤s; z≤n)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (run)
open import Muro.Grade using
  ( Grade; g0; g1; gω; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch )
open import MuroBeam.Grade using
  ( isG1; isZeroGrade; selfKept; Kind; Kmove; Kcopy; kind; kind-g1; copy-not-g1
  ; spend ; Spent )
  renaming (spent to spentK)
open import MuroBeam.Heap using
  ( Ref; obj; checked; residual; ref; count; hasG1; Grade1Unique; uniq-nil
  ; same-unique; Bound; bnil; bcons; bound-++
  ; bound-count0; count0-has
  ; count-++; has-++; count-snoc; has-snoc
  ; removeAt-count; removeAt-has
  ; repl; repl-count; repl-has; bound-repl; bound-remove
  ; spendRef; spendRef-obj; spendRef-checked; applySpend
  ; Obj; cell; live; payload; edgeRefs; edgeRefs-++; nat; kids
  ; Val; suc↑; clo )
  renaming (kept to refKept)
open import MuroBeam.Lib using
  ( ⊥; ⊥-elim; ≤-refl; ≤-step; ≤-trans; ≤-antisym; ≤-subst
  ; +-assoc; +-comm; +-identityʳ; +-swap; +-zero; +-mono; k≤n+k
  ; ≡ᵇ-sound; ≡ᵇ-cong; ≡ᵇ-refl
  ; ∨-assoc; ∨-comm; ∨-swap; ∨-falseʳ; ∨-trueʳ; ∨-false; ∧-split
  ; ext; ext-0; ext-1
  ; lookup; update; mapCons; removeAt
  ; ++-assoc; ++-identityʳ; length-++
  ; +-suc; m≤m+k; ≤-+ˡ; ≤-+ʳ )
open import MuroBeam.Process using
  ( Proc; roots; inbox; refsP; refsPs; refsOf
  ; Sys; sys; heap; procs; Msg; msg; mapRef; mapSys
  ; post; putRoot; putHead; putHeadOf; putTail
  ; deref; derefAt; derefSpent; rootAt; rootFrom
  ; send; sendFrom; sendTaken; dropRoot; takeRoot; dispatch
  ; moveTo; moveToOn; moveOther; moveRecv; copyTo; addMsg
  ; recv; recvAt; recvInbox; addRoot; alloc
  ; poke; length-poke; reuse; reuseFrom; reuseOk
  ; preOf; ctlRefsPs; ctlEq-putRoot; ctlEq-update; eval1
  ; ctl; Ctl; idle; ev; rv; pr
  ; Frame; ar; fn; su; mt; saved; ctlRefs; framesRefs
  ; setProc; install; pass; snoc; freshRef; regrade
  ; anyG1; badG1; predComp; payloadAt; setPayload
  ; evalHere; evalTm; evalRet; useVar; beta; onMatch )
  renaming (bd to frameBd)
open import MuroBeam.Collect using
  ( Step; step-deref; step-send; step-recv; step-alloc; step-reuse; step-collect
  ; step-eval
  ; collect; apply; markVec; filterKeep; filterMsg; clean )

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

-- A g1 mark is at least one reference.
has-count : ∀ i rs → hasG1 i rs ≡ true → suc zero ≤ count i rs
has-count i [] ()
has-count i (r ∷ rs) hf with (obj r ≡ᵇ i) ∧ isG1 (checked r) in eq
... | false = ≤-trans (has-count i rs hf) (k≤n+k (ext (obj r ≡ᵇ i)) (count i rs))
... | true  = subst (λ n → suc zero ≤ n) (sym (head eq)) (s≤s z≤n)
  where
  head : ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ≡ true →
         count i (r ∷ rs) ≡ suc (count i rs)
  head e = cong (λ b → ext b + count i rs) (proj₁ (∧-split e))

has-right : ∀ i xs ys → hasG1 i ys ≡ true → hasG1 i (xs ++ ys) ≡ true
has-right i xs ys hy rewrite has-++ i xs ys | hy = ∨-trueʳ (hasG1 i xs)

has-left : ∀ i xs ys → hasG1 i xs ≡ true → hasG1 i (xs ++ ys) ≡ true
has-left i xs ys hx rewrite has-++ i xs ys | hx = refl

-- Uniqueness of a concatenation restricts to its suffix.
sfxUnique : ∀ pre rs → Grade1Unique (pre ++ rs) → Grade1Unique rs
sfxUnique pre rs u i hy =
  sym (≤-antisym (has-count i rs hy) upper)
  where
  total : count i (pre ++ rs) ≡ 1
  total = u i (has-right i pre rs hy)
  under : count i rs ≤ count i pre + count i rs
  under = k≤n+k (count i pre) (count i rs)
  upper : count i rs ≤ 1
  upper = ≤-subst (subst (λ n → count i rs ≤ n) (sym (count-++ i pre rs)) under) total

-- Counts and grades agree, so uniqueness agrees.
count-join : ∀ i xs xs' ys ys' →
  xs' ≡ xs → count i ys' ≡ count i ys →
  count i (xs' ++ ys') ≡ count i (xs ++ ys)
count-join i xs .xs ys ys' refl eq =
  trans (count-++ i xs ys')
        (trans (cong (count i xs +_) eq) (sym (count-++ i xs ys)))

has-join : ∀ i xs xs' ys ys' →
  xs' ≡ xs → hasG1 i ys' ≡ hasG1 i ys →
  hasG1 i (xs' ++ ys') ≡ hasG1 i (xs ++ ys)
has-join i xs .xs ys ys' refl eq =
  trans (has-++ i xs ys')
        (trans (cong (hasG1 i xs ∨_) eq) (sym (has-++ i xs ys)))

-- Both halves may change, as long as each count (or mark) is preserved.
count-add : ∀ i xs xs' ys ys' →
  count i xs' ≡ count i xs →
  count i ys' ≡ count i ys →
  count i (xs' ++ ys') ≡ count i (xs ++ ys)
count-add i xs xs' ys ys' ex ey =
  trans (count-++ i xs' ys')
        (trans (cong (_+ count i ys') ex)
               (trans (cong (count i xs +_) ey) (sym (count-++ i xs ys))))

has-add : ∀ i xs xs' ys ys' →
  hasG1 i xs' ≡ hasG1 i xs →
  hasG1 i ys' ≡ hasG1 i ys →
  hasG1 i (xs' ++ ys') ≡ hasG1 i (xs ++ ys)
has-add i xs xs' ys ys' ex ey =
  trans (has-++ i xs' ys')
        (trans (cong (_∨ hasG1 i ys') ex)
               (trans (cong (hasG1 i xs ∨_) ey) (sym (has-++ i xs ys))))

+-cancelʳ : ∀ a b c → a + c ≡ b + c → a ≡ b
+-cancelʳ a b zero eq rewrite +-identityʳ a | +-identityʳ b = eq
+-cancelʳ a b (suc c) eq =
  +-cancelʳ a b c (suc-inj (trans (sym (+-suc a c)) (trans eq (+-suc b c))))

+-right : ∀ x k c → (x + k) + c ≡ (x + c) + k
+-right x k c =
  trans (+-assoc x k c)
        (trans (cong (x +_) (+-comm k c)) (sym (+-assoc x c k)))

-- Defined here: `sealMove` needs it, and the later copy is the same function.
bound-split : ∀ {n} xs ys → Bound n (xs ++ ys) → Bound n xs × Bound n ys
bound-split []       ys bd = bnil , bd
bound-split (x ∷ xs) ys (bcons lt rest) with bound-split xs ys rest
... | bx , by = bcons lt bx , by

-- Heap and control stay. The process-ref list is rearranged.
sealMove : ∀ h ps ps' →
  ctlRefsPs ps' ≡ ctlRefsPs ps →
  (∀ k → count k (refsPs ps') ≡ count k (refsPs ps)) →
  (∀ k → hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps)) →
  Bound (length h) (refsPs ps') →
  Bound (length h) (refsOf (sys h ps)) →
  Grade1Unique (refsOf (sys h ps)) →
  WF (sys h ps')
sealMove h ps ps' ceq cq hq bSuf bdF uqF =
  bound-++ bPre bSuf
  , same-unique {rs = refsOf (sys h ps)} {rs' = refsOf (sys h ps')}
      (λ k → count-join k (preOf h ps) (preOf h ps') (refsPs ps) (refsPs ps') preEq (cq k))
      (λ k → has-join k (preOf h ps) (preOf h ps') (refsPs ps) (refsPs ps') preEq (hq k))
      uqF
  where
  preEq : preOf h ps' ≡ preOf h ps
  preEq = cong (edgeRefs h ++_) ceq
  bPre : Bound (length h) (preOf h ps')
  bPre = subst (Bound (length h)) (sym preEq)
           (proj₁ (bound-split (preOf h ps) (refsPs ps) bdF))

-- Dropping references cannot create a second g1 alias.
thin-unique : ∀ new old →
  (∀ i → count i new ≤ count i old) →
  (∀ i → hasG1 i new ≡ true → hasG1 i old ≡ true) →
  Grade1Unique old → Grade1Unique new
thin-unique new old le hs u i hn =
  sym (≤-antisym (has-count i new hn) (≤-subst (le i) (u i (hs i hn))))

-- Adding references that miss every live g1 object.
grow-unique : ∀ new old (extra : ℕ → ℕ) →
  (∀ i → count i new ≡ count i old + extra i) →
  (∀ i → hasG1 i new ≡ hasG1 i old) →
  (∀ i → hasG1 i old ≡ true → extra i ≡ 0) →
  Grade1Unique old → Grade1Unique new
grow-unique new old extra cq hq zx u i hn =
  trans (cq i)
        (trans (cong (count i old +_) (zx i oldHas))
               (trans (+-identityʳ (count i old)) (u i oldHas)))
  where
  oldHas : hasG1 i old ≡ true
  oldHas = trans (sym (hq i)) hn

≤-count++ : ∀ i xs ys zs →
  count i ys ≤ count i zs →
  count i (xs ++ ys) ≤ count i (xs ++ zs)
≤-count++ i xs ys zs le =
  subst (λ n → n ≤ count i (xs ++ zs)) (sym (count-++ i xs ys))
        (subst (λ n → count i xs + count i ys ≤ n) (sym (count-++ i xs zs))
               (+-mono ≤-refl le))

≤-cat : ∀ i a b c d →
  count i a ≤ count i c → count i b ≤ count i d →
  count i (a ++ b) ≤ count i (c ++ d)
≤-cat i a b c d leab lecd =
  subst (λ n → count i (a ++ b) ≤ n) (sym (count-++ i c d))
        (subst (λ n → n ≤ count i c + count i d) (sym (count-++ i a b))
               (+-mono leab lecd))

------------------------------------------------------------------------
-- Splitting a bound, and lifting an index update.
------------------------------------------------------------------------

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
...    | true with isG1 (checked r) in g1eq
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

ctl-clean : ∀ ps → ctlRefsPs (map clean ps) ≡ ctlRefsPs ps
ctl-clean []       = refl
ctl-clean (p ∷ ps) rewrite ctl-clean ps = refl

length-apply : ∀ bs os → length (apply bs os) ≡ length os
length-apply _            []       = refl
length-apply []           (_ ∷ os) rewrite length-apply [] os = refl
length-apply (false ∷ bs) (_ ∷ os) rewrite length-apply bs os = refl
length-apply (true  ∷ bs) (_ ∷ os) rewrite length-apply bs os = refl

bound-edge : ∀ {n} bs os → Bound n (edgeRefs os) → Bound n (edgeRefs (apply bs os))
bound-edge _            []       bnil = bnil
bound-edge []           (o ∷ os) bd =
  bound-edge [] os (proj₂ (bound-split (kids (payload o)) (edgeRefs os) bd))
bound-edge (false ∷ bs) (o ∷ os) bd =
  bound-edge bs os (proj₂ (bound-split (kids (payload o)) (edgeRefs os) bd))
bound-edge (true  ∷ bs) (o ∷ os) bd =
  let bk , br = bound-split (kids (payload o)) (edgeRefs os) bd
  in bound-++ bk (bound-edge bs os br)

count-edge : ∀ bs os i → count i (edgeRefs (apply bs os)) ≤ count i (edgeRefs os)
count-edge _            []       i = ≤-refl
count-edge []           (o ∷ os) i =
  ≤-trans (count-edge [] os i) (dropped (kids (payload o)) (edgeRefs os))
  where
  dropped : ∀ xs ys → count i ys ≤ count i (xs ++ ys)
  dropped xs ys =
    subst (λ n → count i ys ≤ n) (sym (count-++ i xs ys))
          (k≤n+k (count i xs) (count i ys))
count-edge (false ∷ bs) (o ∷ os) i =
  ≤-trans (count-edge bs os i) (dropped (kids (payload o)) (edgeRefs os))
  where
  dropped : ∀ xs ys → count i ys ≤ count i (xs ++ ys)
  dropped xs ys =
    subst (λ n → count i ys ≤ n) (sym (count-++ i xs ys))
          (k≤n+k (count i xs) (count i ys))
count-edge (true  ∷ bs) (o ∷ os) i =
  ≤-count++ i (kids (payload o)) (edgeRefs (apply bs os)) (edgeRefs os) (count-edge bs os i)

has-edge : ∀ bs os i →
  hasG1 i (edgeRefs (apply bs os)) ≡ true → hasG1 i (edgeRefs os) ≡ true
has-edge _            []       i ()
has-edge []           (o ∷ os) i hf = has-right i (kids (payload o)) (edgeRefs os) (has-edge [] os i hf)
has-edge (false ∷ bs) (o ∷ os) i hf = has-right i (kids (payload o)) (edgeRefs os) (has-edge bs os i hf)
has-edge (true  ∷ bs) (o ∷ os) i hf = body (hasG1 i (kids (payload o))) refl
  where
  body : (b : Bool) → hasG1 i (kids (payload o)) ≡ b → hasG1 i (edgeRefs (o ∷ os)) ≡ true
  body true  eb = has-left i (kids (payload o)) (edgeRefs os) eb
  body false eb =
    has-right i (kids (payload o)) (edgeRefs os)
      (has-edge bs os i
        (trans (sym (cong (λ b → b ∨ hasG1 i (edgeRefs (apply bs os))) eb))
               (trans (sym (has-++ i (kids (payload o)) (edgeRefs (apply bs os)))) hf)))

count-filter : ∀ i rs → count i (filterKeep rs) ≤ count i rs
count-filter i []       = ≤-refl
count-filter i (r ∷ rs) = step (isZeroGrade (residual r)) refl
  where
  step : (z : Bool) → isZeroGrade (residual r) ≡ z →
         count i (filterKeep (r ∷ rs)) ≤ count i (r ∷ rs)
  step true ez rewrite ez =
    ≤-trans (count-filter i rs) (subst (λ n → count i rs ≤ n) (sym (count-++ i (r ∷ []) rs))
                                      (k≤n+k (count i (r ∷ [])) (count i rs)))
  step false ez rewrite ez = +-mono ≤-refl (count-filter i rs)

has-filter : ∀ i rs → hasG1 i (filterKeep rs) ≡ true → hasG1 i rs ≡ true
has-filter i [] ()
has-filter i (r ∷ rs) hf = step (isZeroGrade (residual r)) refl
  where
  step : (z : Bool) → isZeroGrade (residual r) ≡ z → hasG1 i (r ∷ rs) ≡ true
  step true ez rewrite ez = has-right i (r ∷ []) rs (has-filter i rs hf)
  step false ez rewrite ez = keep (hasG1 i (r ∷ []) ) refl hf
    where
    bit = (obj r ≡ᵇ i) ∧ isG1 (checked r)
    keep : (b : Bool) → hasG1 i (r ∷ []) ≡ b →
           hasG1 i (r ∷ filterKeep rs) ≡ true → hasG1 i (r ∷ rs) ≡ true
    keep true  eb _ =
      cong (_∨ hasG1 i rs) (trans (sym (∨-falseʳ bit)) eb)
    keep false eb hk =
      has-right i (r ∷ []) rs
        (has-filter i rs
          (trans (sym (cong (λ b → b ∨ hasG1 i (filterKeep rs))
                            (trans (sym (∨-falseʳ bit)) eb)))
                 hk))

has-cat : ∀ i a b c d →
  (hasG1 i a ≡ true → hasG1 i c ≡ true) →
  (hasG1 i b ≡ true → hasG1 i d ≡ true) →
  hasG1 i (a ++ b) ≡ true →
  hasG1 i (c ++ d) ≡ true
has-cat i a b c d ha hb hf = body (hasG1 i a) refl hf
  where
  body : (p : Bool) → hasG1 i a ≡ p → hasG1 i (a ++ b) ≡ true → hasG1 i (c ++ d) ≡ true
  body true  ep _  = has-left i c d (ha ep)
  body false ep hk =
    has-right i c d
      (hb (trans (sym (cong (λ p → p ∨ hasG1 i b) ep))
                 (trans (sym (has-++ i a b)) hk)))

collect-wf : ∀ s → WF s → WF (collect s)
collect-wf (sys h ps) (bdF , uqF) =
  subst (λ n → Bound n (refsOf (collect (sys h ps)))) (sym (length-apply bs h)) bHere
  , thin-unique (refsOf (collect (sys h ps))) (refsOf (sys h ps)) leAll hasAll uqF
  where
  bs  = markVec (sys h ps)
  h'  = apply bs h
  ps' = map clean ps
  pre  = preOf h ps
  pre' = preOf h' ps'
  bPre : Bound (length h) pre
  bPre = proj₁ (bound-split pre (refsPs ps) bdF)
  bEdge : Bound (length h) (edgeRefs h)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bCtl  : Bound (length h) (ctlRefsPs ps)
  bCtl = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs : Bound (length h) (refsPs ps)
  bRs = proj₂ (bound-split pre (refsPs ps) bdF)
  ceq : ctlRefsPs ps' ≡ ctlRefsPs ps
  ceq = ctl-clean ps
  rsEq : refsPs ps' ≡ filterKeep (refsPs ps)
  rsEq = refs-cleaned ps
  bHere : Bound (length h) (refsOf (collect (sys h ps)))
  bHere =
    bound-++ (bound-++ (bound-edge bs h bEdge) (subst (Bound (length h)) (sym ceq) bCtl))
             (subst (Bound (length h)) (sym rsEq) (bound-filter (refsPs ps) bRs))
  lePre : ∀ i → count i pre' ≤ count i pre
  lePre i =
    subst (λ c → count i (edgeRefs h' ++ ctlRefsPs ps') ≤ count i (edgeRefs h ++ c)) ceq
          (≤-cat i (edgeRefs h') (ctlRefsPs ps') (edgeRefs h) (ctlRefsPs ps')
                 (count-edge bs h i) ≤-refl)
  leRs : ∀ i → count i (refsPs ps') ≤ count i (refsPs ps)
  leRs i = subst (λ r → count i r ≤ count i (refsPs ps)) (sym rsEq) (count-filter i (refsPs ps))
  leAll : ∀ i → count i (refsOf (collect (sys h ps))) ≤ count i (refsOf (sys h ps))
  leAll i = ≤-cat i pre' (refsPs ps') pre (refsPs ps) (lePre i) (leRs i)
  hasPre : ∀ i → hasG1 i pre' ≡ true → hasG1 i pre ≡ true
  hasPre i hf =
    has-cat i (edgeRefs h') (ctlRefsPs ps') (edgeRefs h) (ctlRefsPs ps)
            (has-edge bs h i)
            (λ hctl → subst (λ c → hasG1 i c ≡ true) ceq hctl)
            hf
  hasRs : ∀ i → hasG1 i (refsPs ps') ≡ true → hasG1 i (refsPs ps) ≡ true
  hasRs i hf = has-filter i (refsPs ps) (subst (λ r → hasG1 i r ≡ true) rsEq hf)
  hasAll : ∀ i → hasG1 i (refsOf (collect (sys h ps))) ≡ true → hasG1 i (refsOf (sys h ps)) ≡ true
  hasAll i = has-cat i pre' (refsPs ps') pre (refsPs ps) (hasPre i) (hasRs i)

------------------------------------------------------------------------
-- Dereference replaces a root with the spent root. Object and checked
-- grade stay, so the multiset of (object, checked grade) stays.
------------------------------------------------------------------------

deref-wf : ∀ h ps i j t →
  deref run (sys h ps) i j ≡ just t →
  WF (sys h ps) →
  WF t
deref-wf h ps i j t eq (bdF , uqF) = root (rootAt (sys h ps) i j) eq refl
  where
  bd = proj₂ (bound-split (preOf h ps) (refsPs ps) bdF)
  uq = sfxUnique (preOf h ps) (refsPs ps) uqF
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
        in sealMove h ps ps' (ctlEq-putRoot ps i j r' ps' ep) cq hq
             (put-bound i j ps p r r' ps' bd lk lr eo ep) bdF uqF

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
recv-wf h ps i t eq (bdF , uqF) = at (lookup ps i) eq refl
  where
  bd = proj₂ (bound-split (preOf h ps) (refsPs ps) bdF)
  uq = sfxUnique (preOf h ps) (refsPs ps) uqF
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
        in sealMove h ps ps'
             (ctlEq-update i ps p' ps' eu
               (λ p₁ eqp → cong ctl (just-inj (trans (sym lk) eqp)))) cq hq
             (upd-bound i ps p p' ps' bd lk eu bp) bdF uqF

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
alloc-wf h ps i g v t eq (bdF , uqF) = at (lookup ps i) eq refl
  where
  bd = proj₂ (bound-split (preOf h ps) (refsPs ps) bdF)
  uq = sfxUnique (preOf h ps) (refsPs ps) uqF
  r : Ref
  r = ref (length h) g g (selfKept g)
  at : (m : Maybe Proc) →
       mapSys (h ++ cell (nat v) live ∷ []) (addRoot ps i r) ≡ just t →
       lookup ps i ≡ m →
       WF t
  at nothing eq lk rewrite lk with eq
  ... | ()
  at (just p) eq lk rewrite lk = upd (update i p' ps) eq refl
    where
    p' : Proc
    p' = record p { roots = roots p ++ r ∷ [] }
    upd : (m : Maybe (List Proc)) →
          mapSys (h ++ cell (nat v) live ∷ []) m ≡ just t →
          update i p' ps ≡ m →
          WF t
    upd nothing () _
    upd (just ps') refl eu =
      subst (λ n → Bound n (refsOf (sys h' ps'))) (sym len) bSuc , fullU
      where
      n = length h
      h' = h ++ cell (nat v) live ∷ []
      len = length-snoc h (cell (nat v) live)
      ceq = ctlEq-update i ps p' ps' eu
              (λ p₁ eqp → cong ctl (just-inj (trans (sym lk) eqp)))
      eEdge : edgeRefs h' ≡ edgeRefs h
      eEdge = trans (edgeRefs-++ h (cell (nat v) live ∷ [])) (++-identityʳ (edgeRefs h))
      preEq : preOf h' ps' ≡ preOf h ps
      preEq = trans (cong (_++ ctlRefsPs ps') eEdge) (cong (edgeRefs h ++_) ceq)
      bdT = upd-bound i ps p p' ps' (bound-mono (≤-step ≤-refl) bd) lk eu
              (snoc-root-bound p r (bound-mono (≤-step ≤-refl) (lookup-bound i ps p bd lk)) (fresh-< n))
      bSuc : Bound (suc n) (refsOf (sys h' ps'))
      bSuc = bound-++ (subst (Bound (suc n)) (sym preEq)
                        (bound-mono (≤-step ≤-refl)
                          (proj₁ (bound-split (preOf h ps) (refsPs ps) bdF))))
                     bdT
      ext0 : ∀ {k} → (n ≡ᵇ k) ≡ false → ext (obj r ≡ᵇ k) ≡ 0
      ext0 eq rewrite eq = refl
      bit : ∀ {k} → (n ≡ᵇ k) ≡ false → ((obj r ≡ᵇ k) ∧ isG1 (checked r)) ≡ false
      bit eq rewrite eq = refl
      hasEq : ∀ k → (n ≡ᵇ k) ≡ false → hasG1 k (refsP p') ≡ hasG1 k (refsP p)
      hasEq k eq =
        trans (snoc-root-has k p r)
              (trans (cong (hasG1 k (refsP p) ∨_) (bit eq)) (∨-falseʳ (hasG1 k (refsP p))))
      cq : ∀ k → count k (refsPs ps') ≡ count k (refsPs ps) + ext (obj r ≡ᵇ k)
      cq k = upd-add k i ps p p' ps' (ext (obj r ≡ᵇ k)) lk eu (snoc-root-count k p r)
      fullU : Grade1Unique (refsOf (sys h' ps'))
      fullU k hf = go (n ≡ᵇ k) refl
        where
        go : (b : Bool) → (n ≡ᵇ k) ≡ b → count k (refsOf (sys h' ps')) ≡ 1
        go false eb =
          trans cNew (uqF k hOld)
          where
          cSuf : count k (refsPs ps') ≡ count k (refsPs ps)
          cSuf = trans (cq k) (trans (cong (count k (refsPs ps) +_) (ext0 eb)) (+-identityʳ _))
          cNew : count k (refsOf (sys h' ps')) ≡ count k (refsOf (sys h ps))
          cNew = count-join k (preOf h ps) (preOf h' ps') (refsPs ps) (refsPs ps') preEq cSuf
          hSuf : hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps)
          hSuf = upd-has k i ps p p' ps' lk eu (hasEq k eb)
          hOld : hasG1 k (refsOf (sys h ps)) ≡ true
          hOld = trans (sym (has-join k (preOf h ps) (preOf h' ps') (refsPs ps) (refsPs ps') preEq hSuf)) hf
        go true eb =
          trans (cNew) (one eb)
          where
          zFull : count k (refsOf (sys h ps)) ≡ 0
          zFull = subst (λ j → count j (refsOf (sys h ps)) ≡ 0) (≡ᵇ-sound n k eb)
                        (bound-count0 bdF n ≤-refl)
          cSuf : count k (refsPs ps') ≡ suc zero
          cSuf = trans (cq k) (trans (cong (_+ ext (obj r ≡ᵇ k))
                                          (proj₂ (parts zFull))) (one' eb))
            where
            parts : count k (preOf h ps ++ refsPs ps) ≡ 0 →
                    count k (preOf h ps) ≡ 0 × count k (refsPs ps) ≡ 0
            parts eq0 = +-zero (count k (preOf h ps)) (count k (refsPs ps))
                          (trans (sym (count-++ k (preOf h ps) (refsPs ps))) eq0)
            one' : (n ≡ᵇ k) ≡ true → zero + ext (obj r ≡ᵇ k) ≡ suc zero
            one' eq rewrite eq = refl
          cPre : count k (preOf h' ps') ≡ 0
          cPre = trans (cong (λ xs → count k xs) preEq) (proj₁ (parts zFull))
            where
            parts : count k (preOf h ps ++ refsPs ps) ≡ 0 →
                    count k (preOf h ps) ≡ 0 × count k (refsPs ps) ≡ 0
            parts eq0 = +-zero (count k (preOf h ps)) (count k (refsPs ps))
                          (trans (sym (count-++ k (preOf h ps) (refsPs ps))) eq0)
          cNew : count k (refsOf (sys h' ps')) ≡ suc zero
          cNew = trans (count-++ k (preOf h' ps') (refsPs ps'))
                       (trans (cong (_+ count k (refsPs ps')) cPre) cSuf)
          one : (n ≡ᵇ k) ≡ true → suc zero ≡ 1
          one _ = refl

------------------------------------------------------------------------
-- Reuse overwrites one spent g1 root in place. The object index is
-- unchanged, and the runtime gate says that index occurs once.
------------------------------------------------------------------------

count-poke : ∀ h k v i → count i (edgeRefs (poke h k v)) ≤ count i (edgeRefs h)
count-poke []             _       _ i = ≤-refl
count-poke (o ∷ hs)       zero    _ i =
  subst (λ n → count i (edgeRefs hs) ≤ n)
        (sym (count-++ i (kids (payload o)) (edgeRefs hs)))
        (k≤n+k (count i (kids (payload o))) (count i (edgeRefs hs)))
count-poke (o ∷ hs)       (suc k) v i =
  ≤-count++ i (kids (payload o)) (edgeRefs (poke hs k v)) (edgeRefs hs) (count-poke hs k v i)

has-poke : ∀ h k v i → hasG1 i (edgeRefs (poke h k v)) ≡ true → hasG1 i (edgeRefs h) ≡ true
has-poke []       _       _ i ()
has-poke (o ∷ hs) zero    _ i hf = has-right i (kids (payload o)) (edgeRefs hs) hf
has-poke (o ∷ hs) (suc k) v i hf =
  has-cat i (kids (payload o)) (edgeRefs (poke hs k v)) (kids (payload o)) (edgeRefs hs)
          (λ hk → hk) (has-poke hs k v i) hf

bound-poke : ∀ {n} h k v → Bound n (edgeRefs h) → Bound n (edgeRefs (poke h k v))
bound-poke []       _       _ bnil = bnil
bound-poke (o ∷ hs) zero    _ bd = proj₂ (bound-split (kids (payload o)) (edgeRefs hs) bd)
bound-poke (o ∷ hs) (suc k) v bd =
  let bk , br = bound-split (kids (payload o)) (edgeRefs hs) bd
  in bound-++ bk (bound-poke hs k v br)

lookup-has-g1 : ∀ j xs r i →
  lookup xs j ≡ just r → obj r ≡ i → isG1 (checked r) ≡ true →
  hasG1 i xs ≡ true
lookup-has-g1 zero    (_ ∷ _) r i refl oi g rewrite oi | g | ≡ᵇ-refl i = refl
lookup-has-g1 (suc j) (_ ∷ xs) r i eq oi g rewrite lookup-has-g1 j xs r i eq oi g = ∨-trueʳ _

reuse-wf : ∀ h ps i j g v t →
  reuse (sys h ps) i j g v ≡ just t →
  WF (sys h ps) →
  WF t
reuse-wf h ps i j g v t eq (bdF , uqF) = from (rootAt (sys h ps) i j) eq refl
  where
  bd = proj₂ (bound-split (preOf h ps) (refsPs ps) bdF)
  uq = sfxUnique (preOf h ps) (refsPs ps) uqF
  from : (m : Maybe Ref) →
         reuse (sys h ps) i j g v ≡ just t →
         rootAt (sys h ps) i j ≡ m →
         WF t
  from nothing e rk =
    ⊥-elim (nothing≢just (trans (sym (cong (reuseFrom (sys h ps) i j g v) rk)) e))
  from (just r) e rk rewrite rk =
    gates (isG1 (checked r)) (isZeroGrade (residual r))
          (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) e refl refl refl
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
            (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) ≡ c →
            WF t
    gates false b c eG _ _ _ =
      ⊥-elim (nothing≢just (trans (sym (no1 b c)) eG))
    gates true false c eG _ _ _ =
      ⊥-elim (nothing≢just (trans (sym (no2 c)) eG))
    gates true true false eG _ _ _ =
      ⊥-elim (nothing≢just (trans (sym no3) eG))
    gates true true true eG eg _ ec = via (putRoot ps i j r') eG refl
      where
      r' : Ref
      r' = ref (obj r) g g (selfKept g)
      via : (m : Maybe (List Proc)) →
            mapSys (poke h (obj r) v) m ≡ just t →
            putRoot ps i j r' ≡ m →
            WF t
      via nothing () _
      via (just ps') refl ep =
        subst (λ n → Bound n (refsOf (sys (poke h (obj r) v) ps')))
              (sym (length-poke h (obj r) v)) bHere
        , thin-unique (refsOf (sys (poke h (obj r) v) ps')) (refsOf (sys h ps)) leAll hasAll uqF
        where
        p  = proj₁ (root-lookup ps i j r rk)
        lk = proj₁ (proj₂ (root-lookup ps i j r rk))
        lr = proj₂ (proj₂ (root-lookup ps i j r rk))
        h2 = poke h (obj r) v
        ceq = ctlEq-putRoot ps i j r' ps' ep
        bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps)
                        (proj₁ (bound-split (preOf h ps) (refsPs ps) bdF)))
        bCtl  = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps)
                        (proj₁ (bound-split (preOf h ps) (refsPs ps) bdF)))
        bHere =
          bound-++ (bound-++ (bound-poke h (obj r) v bEdge)
                             (subst (Bound (length h)) (sym ceq) bCtl))
                   (put-bound i j ps p r r' ps' bd lk lr refl ep)
        cSuf : ∀ k → count k (refsPs ps') ≡ count k (refsPs ps)
        cSuf k = put-count k i j ps p r r' ps' lk lr refl ep
        leAll : ∀ q → count q (refsOf (sys h2 ps')) ≤ count q (refsOf (sys h ps))
        leAll q =
          ≤-cat q (preOf h2 ps') (refsPs ps') (preOf h ps) (refsPs ps)
            (subst (λ c → count q (edgeRefs h2 ++ ctlRefsPs ps') ≤ count q (edgeRefs h ++ c)) ceq
                   (≤-cat q (edgeRefs h2) (ctlRefsPs ps') (edgeRefs h) (ctlRefsPs ps')
                          (count-poke h (obj r) v q) ≤-refl))
            (subst (λ n → n ≤ count q (refsPs ps)) (sym (cSuf q)) ≤-refl)
        hasRs : ∀ q → hasG1 q (refsPs ps') ≡ true → hasG1 q (refsPs ps) ≡ true
        hasRs q hf = on (obj r ≡ᵇ q) refl
          where
          on : (b : Bool) → (obj r ≡ᵇ q) ≡ b → hasG1 q (refsPs ps) ≡ true
          on false eb = trans (sym (put-has-miss q i j ps p r r' ps' lk lr refl eb ep)) hf
          on true  eb =
            trans (lookup-has q i ps p lk)
                  (cong (λ h → h ∨ hasG1 q (others i ps))
                        (has-left q (roots p) (mapRef (inbox p))
                          (lookup-has-g1 j (roots p) r q lr (≡ᵇ-sound (obj r) q eb) eg)))
        hasAll : ∀ q → hasG1 q (refsOf (sys h2 ps')) ≡ true → hasG1 q (refsOf (sys h ps)) ≡ true
        hasAll q hf =
          has-cat q (preOf h2 ps') (refsPs ps') (preOf h ps) (refsPs ps)
            (λ hp → has-cat q (edgeRefs h2) (ctlRefsPs ps') (edgeRefs h) (ctlRefsPs ps)
                      (has-poke h (obj r) v q)
                      (λ hc → subst (λ c → hasG1 q c ≡ true) ceq hc)
                      hp)
            (hasRs q) hf

reuse-in-place : ∀ h ps i j g v t r →
  rootAt (sys h ps) i j ≡ just r →
  reuse (sys h ps) i j g v ≡ just t →
  isG1 (checked r) ≡ true
  × isZeroGrade (residual r) ≡ true
  × count (obj r) (refsOf (sys h ps)) ≡ 1
reuse-in-place h ps i j g v t r rk eq rewrite rk =
  gates (isG1 (checked r)) (isZeroGrade (residual r))
        (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) eq refl refl refl
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
          (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) ≡ c →
          isG1 (checked r) ≡ true
          × isZeroGrade (residual r) ≡ true
          × count (obj r) (refsOf (sys h ps)) ≡ 1
  gates false b c e _ _ _ =
    ⊥-elim (nothing≢just (trans (sym (no1 b c)) e))
  gates true false c e _ _ _ =
    ⊥-elim (nothing≢just (trans (sym (no2 c)) e))
  gates true true false e _ _ _ =
    ⊥-elim (nothing≢just (trans (sym no3) e))
  gates true true true _ ea eb ec =
    ea , eb , ≡ᵇ-sound (count (obj r) (refsOf (sys h ps))) 1 ec

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

-- The copied root is not g1. Under uniqueness of the whole reference
-- list it cannot point at a live g1 object, so the extra alias is 0
-- whenever a g1 mark is present.
copy-ext-full : ∀ k h ps sp si sj r ys →
  lookup ps si ≡ just sp →
  removeAt sj (roots sp) ≡ just (r , ys) →
  isG1 (checked r) ≡ false →
  Grade1Unique (refsOf (sys h ps)) →
  hasG1 k (refsOf (sys h ps)) ≡ true →
  ext (obj r ≡ᵇ k) ≡ 0
copy-ext-full k h ps sp si sj r ys lk rm ng uq hf = contra (obj r ≡ᵇ k) refl
  where
  rest = ys ++ mapRef (inbox sp)
  oth  = others si ps
  pre  = preOf h ps
  contra : (b : Bool) → (obj r ≡ᵇ k) ≡ b → ext (obj r ≡ᵇ k) ≡ 0
  contra false eb rewrite eb = refl
  contra true  eb = ⊥-elim (true≢false (trans (sym hf) gone))
    where
    ext1 : ext (obj r ≡ᵇ k) ≡ 1
    ext1 rewrite eb = refl
    cSp : count k (refsP sp) ≡ suc (count k rest)
    cSp = trans (proc-drop-count k sp sj r ys rm) (cong (_+ count k rest) ext1)
    cPs : count k (refsPs ps) ≡ suc (count k rest + count k oth)
    cPs = trans (lookup-count k si ps sp lk)
                (trans (cong (_+ count k oth) cSp) refl)
    eq1 : count k pre + count k (refsPs ps) ≡ 1
    eq1 = trans (sym (count-++ k pre (refsPs ps))) (uq k hf)
    shifted : suc (count k pre + (count k rest + count k oth)) ≡ suc zero
    shifted =
      trans (sym (+-suc (count k pre) (count k rest + count k oth)))
            (trans (cong (count k pre +_) (sym cPs)) eq1)
    zPre : count k pre ≡ zero
    zPre = proj₁ (+-zero (count k pre) (count k rest + count k oth) (suc-inj shifted))
    zOut : count k rest + count k oth ≡ zero
    zOut = proj₂ (+-zero (count k pre) (count k rest + count k oth) (suc-inj shifted))
    zRest : count k rest ≡ zero
    zRest = proj₁ (+-zero (count k rest) (count k oth) zOut)
    zOth : count k oth ≡ zero
    zOth = proj₂ (+-zero (count k rest) (count k oth) zOut)
    flat : ((obj r ≡ᵇ k) ∧ isG1 (checked r)) ≡ false
    flat = trans (cong (_∧ isG1 (checked r)) eb) ng
    hSp : hasG1 k (refsP sp) ≡ false
    hSp = trans (proc-drop-has k sp sj r ys rm)
                (trans (cong (_∨ hasG1 k rest) flat) (count0-has k rest zRest))
    hPs : hasG1 k (refsPs ps) ≡ false
    hPs = trans (lookup-has k si ps sp lk)
                (trans (cong (hasG1 k (refsP sp) ∨_) (count0-has k oth zOth))
                       (trans (∨-falseʳ (hasG1 k (refsP sp))) hSp))
    gone : hasG1 k (refsOf (sys h ps)) ≡ false
    gone = trans (has-++ k pre (refsPs ps))
                 (trans (cong (_∨ hasG1 k (refsPs ps)) (count0-has k pre zPre)) hPs)

------------------------------------------------------------------------
-- Send. A move preserves every count. A copy preserves g1 counts
-- because the extra alias is not itself g1.
------------------------------------------------------------------------

send-wf : ∀ h ps si sj ri t →
  send (sys h ps) si sj ri ≡ just t →
  WF (sys h ps) →
  WF t
send-wf h ps si sj ri t eq (bdF , uqF) = from (lookup ps si) eq refl
  where
  bd = proj₂ (bound-split (preOf h ps) (refsPs ps) bdF)
  uq = sfxUnique (preOf h ps) (refsPs ps) uqF
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
                ceq = ctlEq-update ri ps (post rp r) ps' eu
                        (λ p₁ eqp → cong ctl (just-inj (trans (sym lk2) eqp)))
                preEq = cong (edgeRefs h ++_) ceq
                bPre = subst (Bound (length h)) (sym preEq)
                         (proj₁ (bound-split (preOf h ps) (refsPs ps) bdF))
                uq' : Grade1Unique (refsOf (sys h ps'))
                uq' k hf =
                  let hold = trans (sym (has-add k (preOf h ps) (preOf h ps') (refsPs ps) (refsPs ps')
                                          (cong (hasG1 k) preEq) (hq k))) hf
                      zext = copy-ext-full k h ps sp si sj r ys lk rm ng uqF hold
                      cEq  = trans (cq k) (trans (cong (count k (refsPs ps) +_) zext)
                                           (+-identityʳ (count k (refsPs ps))))
                  in trans (count-add k (preOf h ps) (preOf h ps') (refsPs ps) (refsPs ps')
                             (cong (count k) preEq) cEq)
                           (uqF k hold)
            in bound-++ bPre bd' , uq'
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
                db = proj₁ (proc-drop-bound sp sj r ys (lookup-bound si ps sp bd lk) rm)
                olt = proj₂ (proc-drop-bound sp sj r ys (lookup-bound si ps sp bd lk) rm)
                bp = post-bound sp' r db olt
                hyp = λ p eqp → cong ctl (just-inj (trans (sym lk) eqp))
            in sealMove h ps ps' (ctlEq-update si ps (post sp' r) ps' eu hyp)
                 cq hq (upd-bound si ps sp (post sp' r) ps' bd lk eu bp) bdF uqF
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
                    db = proj₁ (proc-drop-bound sp sj r ys (lookup-bound si ps sp bd lk) rm)
                    olt = proj₂ (proc-drop-bound sp sj r ys (lookup-bound si ps sp bd lk) rm)
                    bd1 = upd-bound si ps sp sp' ps1 bd lk eu1 db
                    brp = lookup-bound ri ps1 rp bd1 lr
                    bp  = post-bound rp r brp olt
                    ceq = trans (ctlEq-update ri ps1 (post rp r) ps' eu2
                                  (λ p eqp → cong ctl (just-inj (trans (sym lr) eqp))))
                                (ctlEq-update si ps sp' ps1 eu1
                                  (λ p eqp → cong ctl (just-inj (trans (sym lk) eqp))))
                in sealMove h ps ps' ceq cq hq
                     (upd-bound ri ps1 rp (post rp r) ps' bd1 lr eu2 bp) bdF uqF


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
  × (∀ k → count k (refsOf t) ≡ count k (refsOf (sys h ps)))
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
        × (∀ k → count k (refsOf t) ≡ count k (refsOf (sys h ps)))
  via nothing () _
  via (just ps') refl eu =
    refl
    , (λ k →
         let ceq = ctlEq-update si ps (post sp' r) ps' eu
                     (λ p eqp → cong ctl (just-inj (trans (sym lk) eqp)))
             cSuf = upd-count k si ps sp (post sp' r) ps' lk eu
                      (self-count k sp sj r ys rm)
         in count-add k (preOf h ps) (preOf h ps') (refsPs ps) (refsPs ps')
              (cong (count k) (cong (edgeRefs h ++_) ceq)) cSuf)
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
          × (∀ k → count k (refsOf t) ≡ count k (refsOf (sys h ps)))
  step1 nothing () _
  step1 (just ps1) e1 eu1 = step2 (lookup ps1 ri) e1 refl
    where
    step2 : (m : Maybe Proc) →
            moveRecv r ri h ps1 m ≡ just t →
            lookup ps1 ri ≡ m →
            heap t ≡ h
            × (∀ k → count k (refsOf t) ≡ count k (refsOf (sys h ps)))
    step2 nothing () _
    step2 (just rp) e2 lr = step3 (update ri (post rp r) ps1) e2 refl
      where
      step3 : (m : Maybe (List Proc)) →
              mapSys h m ≡ just t →
              update ri (post rp r) ps1 ≡ m →
              heap t ≡ h
              × (∀ k → count k (refsOf t) ≡ count k (refsOf (sys h ps)))
      step3 nothing () _
      step3 (just ps') refl eu2 =
        refl
        , (λ k →
            let c1 = upd-sub k si ps sp sp' ps1 (ext (obj r ≡ᵇ k)) lk eu1
                       (proc-drop-count k sp sj r ys rm)
                c2 = upd-add k ri ps1 rp (post rp r) ps' (ext (obj r ≡ᵇ k)) lr eu2
                       (post-count k rp r)
                cSuf = trans c2 (trans (+-comm (count k (refsPs ps1)) (ext (obj r ≡ᵇ k))) (sym c1))
                ceq = trans (ctlEq-update ri ps1 (post rp r) ps' eu2
                              (λ p eqp → cong ctl (just-inj (trans (sym lr) eqp))))
                            (ctlEq-update si ps sp' ps1 eu1
                              (λ p eqp → cong ctl (just-inj (trans (sym lk) eqp))))
            in count-add k (preOf h ps) (preOf h ps') (refsPs ps) (refsPs ps')
                 (cong (count k) (cong (edgeRefs h ++_) ceq)) cSuf)

send-g1-keep : ∀ h ps si sj ri t r ys sp →
  lookup ps si ≡ just sp →
  removeAt sj (roots sp) ≡ just (r , ys) →
  checked r ≡ g1 →
  isZeroGrade (residual r) ≡ false →
  send (sys h ps) si sj ri ≡ just t →
  heap t ≡ h
  × (∀ k → count k (refsOf t) ≡ count k (refsOf (sys h ps)))
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
  × (∀ k → count k (refsOf t) ≡ count k (refsOf (sys h ps)))
  × moveTo r (record sp { roots = ys }) si ri h ps ≡ just t
send-g1-moves h ps si sj ri t r ys sp lk rm cg nz eq =
  proj₁ kept , proj₂ kept , send-g1-red h ps si sj ri t r ys sp lk rm cg nz eq
  where
  kept : heap t ≡ h × (∀ k → count k (refsOf t) ≡ count k (refsOf (sys h ps)))
  kept = send-g1-keep h ps si sj ri t r ys sp lk rm cg nz eq

------------------------------------------------------------------------
-- Evaluation. Control and heap edges change; roots and mailboxes do not.
-- Counting is proved once for a replacement, a rotation, a fresh cell,
-- a non-g1 copy, and a regrade.
------------------------------------------------------------------------

not-true : ∀ b → not b ≡ true → b ≡ false
not-true false refl = refl
not-true true ()

pass-ok : ∀ {A : Set} {x : A} b (m : Maybe A) → pass b m ≡ just x → b ≡ true × m ≡ just x
pass-ok true (just x) refl = refl , refl
pass-ok true nothing ()
pass-ok false _ ()

bad-ok : ∀ c n → (isG1 c ∧ not (n ≡ᵇ 1)) ≡ false → isG1 c ≡ true → (n ≡ᵇ 1) ≡ true
bad-ok c n eq g1 rewrite g1 = go (n ≡ᵇ 1) refl
  where
  go : (b : Bool) → (n ≡ᵇ 1) ≡ b → (n ≡ᵇ 1) ≡ true
  go true  eb = eb
  go false eb rewrite eb = ⊥-elim (true≢false eq)

has→any : ∀ i rs → hasG1 i rs ≡ true → anyG1 rs ≡ true
has→any i [] ()
has→any i (r ∷ rs) hf = step ((obj r ≡ᵇ i) ∧ isG1 (checked r)) refl
  where
  step : (b : Bool) → ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ≡ b → anyG1 (r ∷ rs) ≡ true
  step true  eb = cong (_∨ anyG1 rs) (proj₂ (∧-split eb))
  step false eb =
    trans (cong (isG1 (checked r) ∨_)
            (has→any i rs
              (trans (sym (cong (λ b → b ∨ hasG1 i rs) eb)) hf)))
          (∨-trueʳ (isG1 (checked r)))

any-has : ∀ i rs → anyG1 rs ≡ false → hasG1 i rs ≡ false
any-has i []       _  = refl
any-has i (r ∷ rs) ng = step (isG1 (checked r)) refl
  where
  step : (b : Bool) → isG1 (checked r) ≡ b → hasG1 i (r ∷ rs) ≡ false
  step true  eb rewrite eb = ⊥-elim (true≢false ng)
  step false eb rewrite eb | ∧-falseʳ (obj r ≡ᵇ i) = any-has i rs ng

≤1 : ∀ n → suc zero ≤ n → Σ ℕ (λ m → n ≡ suc m)
≤1 (suc m) (s≤s z≤n) = m , refl
≤1 zero ()

has-skip : ∀ i ys xs zs → hasG1 i xs ≡ false →
  hasG1 i (ys ++ xs ++ zs) ≡ hasG1 i (ys ++ zs)
has-skip i ys xs zs ez =
  trans (has-++ i ys (xs ++ zs))
        (trans (cong (hasG1 i ys ∨_) (trans (has-++ i xs zs) (cong (_∨ hasG1 i zs) ez)))
               (sym (has-++ i ys zs)))

count3 : ∀ i ys xs zs →
  count i (ys ++ xs ++ zs) ≡ count i (ys ++ zs) + count i xs
count3 i ys xs zs =
  trans (count-++ i ys (xs ++ zs))
        (trans (cong (count i ys +_) (count-++ i xs zs))
               (trans (sym (+-assoc (count i ys) (count i xs) (count i zs)))
                      (trans (+-right (count i ys) (count i xs) (count i zs))
                             (cong (_+ count i xs) (sym (count-++ i ys zs))))))

-- A non-g1 segment of a unique list contributes nothing to a live g1 object.
sub-miss : ∀ i xs ys zs →
  anyG1 xs ≡ false →
  Grade1Unique (ys ++ xs ++ zs) →
  hasG1 i (ys ++ xs ++ zs) ≡ true →
  count i xs ≡ 0
sub-miss i xs ys zs ng u hf = no (hasG1 i xs) refl
  where
  no : (b : Bool) → hasG1 i xs ≡ b → count i xs ≡ 0
  no true  eb = ⊥-elim (true≢false (trans (sym (has→any i xs eb)) ng))
  no false eb =
    let hOut = trans (sym (has-skip i ys xs zs eb)) hf
        cOut = has-count i (ys ++ zs) hOut
        m = proj₁ (≤1 (count i (ys ++ zs)) cOut)
        em = proj₂ (≤1 (count i (ys ++ zs)) cOut)
        tot = u i hf
        sumEq = trans (cong (_+ count i xs) (sym em))
                      (trans (sym (count3 i ys xs zs)) tot)
    in proj₂ (+-zero m (count i xs) (suc-inj sumEq))

data Both (ps ps' : List Proc) (p : Proc) (c : Ctl) : Set where
  both : (L R : List Ref) →
         ctlRefsPs ps ≡ L ++ ctlRefs (ctl p) ++ R →
         ctlRefsPs ps' ≡ L ++ ctlRefs c ++ R →
         refsPs ps' ≡ refsPs ps →
         Both ps ps' p c

set-both : ∀ i ps p c ps' →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  Both ps ps' p c
set-both _ [] _ _ _ () _
set-both zero (p ∷ ps) .p c .(record p { ctl = c } ∷ ps) refl refl =
  both [] (ctlRefsPs ps) refl refl refl
set-both (suc i) (q ∷ ps) p c ps' lk eq = tail (setProc ps i c) eq refl
  where
  tail : (m : Maybe (List Proc)) → mapCons q m ≡ just ps' → setProc ps i c ≡ m →
         Both (q ∷ ps) ps' p c
  tail nothing () _
  tail (just qs) refl eqs =
    let ih = set-both i ps p c qs lk eqs
    in go ih
    where
    go : Both ps qs p c → Both (q ∷ ps) (q ∷ qs) p c
    go (both L R e1 e2 rq) =
      both (ctlRefs (ctl q) ++ L) R
        (trans (cong (ctlRefs (ctl q) ++_) e1)
               (sym (++-assoc (ctlRefs (ctl q)) L (ctlRefs (ctl p) ++ R))))
        (trans (cong (ctlRefs (ctl q) ++_) e2)
               (sym (++-assoc (ctlRefs (ctl q)) L (ctlRefs c ++ R))))
        (cong (refsP q ++_) rq)

set-refsPs : ∀ i ps c ps' → setProc ps i c ≡ just ps' → refsPs ps' ≡ refsPs ps
set-refsPs _ [] _ _ ()
set-refsPs zero (p ∷ ps) c .(record p { ctl = c } ∷ ps) refl = refl
set-refsPs (suc i) (p ∷ ps) c ps' eq = tail (setProc ps i c) eq refl
  where
  tail : (m : Maybe (List Proc)) → mapCons p m ≡ just ps' → setProc ps i c ≡ m →
         refsPs ps' ≡ refsPs (p ∷ ps)
  tail nothing () _
  tail (just qs) refl eqs rewrite set-refsPs i ps c qs eqs = refl

ctl-bound-at : ∀ {n} i ps p →
  lookup ps i ≡ just p →
  Bound n (ctlRefsPs ps) →
  Bound n (ctlRefs (ctl p))
ctl-bound-at _ [] _ () _
ctl-bound-at zero (p ∷ ps) .p refl bd =
  proj₁ (bound-split (ctlRefs (ctl p)) (ctlRefsPs ps) bd)
ctl-bound-at (suc i) (q ∷ ps) p lk bd =
  ctl-bound-at i ps p lk (proj₂ (bound-split (ctlRefs (ctl q)) (ctlRefsPs ps) bd))

set-ctl-bound : ∀ {n} i ps p c ps' →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  Bound n (ctlRefsPs ps) →
  Bound n (ctlRefs c) →
  Bound n (ctlRefsPs ps')
set-ctl-bound _ [] _ _ _ () _ _ _
set-ctl-bound zero (p ∷ ps) .p c .(record p { ctl = c } ∷ ps) refl refl bd bc =
  bound-++ bc (proj₂ (bound-split (ctlRefs (ctl p)) (ctlRefsPs ps) bd))
set-ctl-bound (suc i) (q ∷ ps) p c ps' lk eq bd bc = tail (setProc ps i c) eq refl
  where
  tail : (m : Maybe (List Proc)) → mapCons q m ≡ just ps' → setProc ps i c ≡ m →
         Bound _ (ctlRefsPs ps')
  tail nothing () _
  tail (just qs) refl eqs =
    let hd , tl = bound-split (ctlRefs (ctl q)) (ctlRefsPs ps) bd
    in bound-++ hd (set-ctl-bound i ps p c qs lk eqs tl bc)

lift-count : ∀ k i ps p c ps' →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  count k (ctlRefs c) ≡ count k (ctlRefs (ctl p)) →
  count k (ctlRefsPs ps') ≡ count k (ctlRefsPs ps)
lift-count k zero (p ∷ ps) .p c .(record p { ctl = c } ∷ ps) refl refl eq =
  trans (count-++ k (ctlRefs c) (ctlRefsPs ps))
        (trans (cong (_+ count k (ctlRefsPs ps)) eq)
               (sym (count-++ k (ctlRefs (ctl p)) (ctlRefsPs ps))))
lift-count k (suc i) (q ∷ ps) p c ps' lk eq eqc = tail (setProc ps i c) eq refl
  where
  tail : (m : Maybe (List Proc)) → mapCons q m ≡ just ps' → setProc ps i c ≡ m →
         count k (ctlRefsPs ps') ≡ count k (ctlRefsPs (q ∷ ps))
  tail nothing () _
  tail (just qs) refl eqs =
    trans (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
          (trans (cong (count k (ctlRefs (ctl q)) +_) (lift-count k i ps p c qs lk eqs eqc))
                 (sym (count-++ k (ctlRefs (ctl q)) (ctlRefsPs ps))))

lift-plus : ∀ k i ps p c ps' n →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  count k (ctlRefs c) ≡ count k (ctlRefs (ctl p)) + n →
  count k (ctlRefsPs ps') ≡ count k (ctlRefsPs ps) + n
lift-plus k zero (p ∷ ps) .p c .(record p { ctl = c } ∷ ps) n refl refl eq =
  trans (count-++ k (ctlRefs c) (ctlRefsPs ps))
        (trans (cong (_+ count k (ctlRefsPs ps)) eq)
               (trans (+-right (count k (ctlRefs (ctl p))) n (count k (ctlRefsPs ps)))
                      (cong (_+ n) (sym (count-++ k (ctlRefs (ctl p)) (ctlRefsPs ps))))))
lift-plus k (suc i) (q ∷ ps) p c ps' n lk eq eqc = tail (setProc ps i c) eq refl
  where
  tail : (m : Maybe (List Proc)) → mapCons q m ≡ just ps' → setProc ps i c ≡ m →
         count k (ctlRefsPs ps') ≡ count k (ctlRefsPs (q ∷ ps)) + n
  tail nothing () _
  tail (just qs) refl eqs =
    trans (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
          (trans (cong (count k (ctlRefs (ctl q)) +_) (lift-plus k i ps p c qs n lk eqs eqc))
                 (trans (sym (+-assoc (count k (ctlRefs (ctl q))) (count k (ctlRefsPs ps)) n))
                        (cong (_+ n) (sym (count-++ k (ctlRefs (ctl q)) (ctlRefsPs ps))))))

lift-has : ∀ k i ps p c ps' →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  hasG1 k (ctlRefs c) ≡ hasG1 k (ctlRefs (ctl p)) →
  hasG1 k (ctlRefsPs ps') ≡ hasG1 k (ctlRefsPs ps)
lift-has k zero (p ∷ ps) .p c .(record p { ctl = c } ∷ ps) refl refl eq =
  trans (has-++ k (ctlRefs c) (ctlRefsPs ps))
        (trans (cong (_∨ hasG1 k (ctlRefsPs ps)) eq)
               (sym (has-++ k (ctlRefs (ctl p)) (ctlRefsPs ps))))
lift-has k (suc i) (q ∷ ps) p c ps' lk eq eqc = tail (setProc ps i c) eq refl
  where
  tail : (m : Maybe (List Proc)) → mapCons q m ≡ just ps' → setProc ps i c ≡ m →
         hasG1 k (ctlRefsPs ps') ≡ hasG1 k (ctlRefsPs (q ∷ ps))
  tail nothing () _
  tail (just qs) refl eqs =
    trans (has-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
          (trans (cong (hasG1 k (ctlRefs (ctl q)) ∨_) (lift-has k i ps p c qs lk eqs eqc))
                 (sym (has-++ k (ctlRefs (ctl q)) (ctlRefsPs ps))))

refs-count : ∀ k h ps →
  count k (refsOf (sys h ps)) ≡
  count k (edgeRefs h) + count k (ctlRefsPs ps) + count k (refsPs ps)
refs-count k h ps =
  trans (count-++ k (preOf h ps) (refsPs ps))
        (cong (_+ count k (refsPs ps)) (count-++ k (edgeRefs h) (ctlRefsPs ps)))

refs-has : ∀ k h ps →
  hasG1 k (refsOf (sys h ps)) ≡
  (hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs ps)) ∨ hasG1 k (refsPs ps)
refs-has k h ps =
  trans (has-++ k (preOf h ps) (refsPs ps))
        (cong (_∨ hasG1 k (refsPs ps)) (has-++ k (edgeRefs h) (ctlRefsPs ps)))

same-ctl : ∀ h ps ps' →
  WF (sys h ps) →
  refsPs ps' ≡ refsPs ps →
  (∀ k → count k (ctlRefsPs ps') ≡ count k (ctlRefsPs ps)) →
  (∀ k → hasG1 k (ctlRefsPs ps') ≡ hasG1 k (ctlRefsPs ps)) →
  Bound (length h) (ctlRefsPs ps') →
  WF (sys h ps')
same-ctl h ps ps' (bdF , uqF) rq cq hq bc =
  bound-++ (bound-++ bEdge bc) (subst (Bound (length h)) (sym rq) bRs)
  , same-unique {rs = refsOf (sys h ps)} {rs' = refsOf (sys h ps')}
      (λ k → cEq k) (λ k → hEq k) uqF
  where
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bdF)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bdF)
  cEq : ∀ k → count k (refsOf (sys h ps')) ≡ count k (refsOf (sys h ps))
  cEq k =
    trans (refs-count k h ps')
          (trans (cong (λ n → count k (edgeRefs h) + n + count k (refsPs ps')) (cq k))
                 (trans (cong (λ rs → count k (edgeRefs h) + count k (ctlRefsPs ps) + count k rs) rq)
                        (sym (refs-count k h ps))))
  hEq : ∀ k → hasG1 k (refsOf (sys h ps')) ≡ hasG1 k (refsOf (sys h ps))
  hEq k =
    trans (refs-has k h ps')
          (trans (cong (λ n → (hasG1 k (edgeRefs h) ∨ n) ∨ hasG1 k (refsPs ps')) (hq k))
                 (trans (cong (λ rs → (hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs ps)) ∨ hasG1 k rs) rq)
                        (sym (refs-has k h ps))))

rot-count : ∀ i r xs ys →
  count i (r ∷ xs ++ ys) ≡ count i (xs ++ (r ∷ ys))
rot-count i r xs ys =
  trans (cong (ext (obj r ≡ᵇ i) +_) (count-++ i xs ys))
        (trans (sym (+-assoc (ext (obj r ≡ᵇ i)) (count i xs) (count i ys)))
               (trans (cong (_+ count i ys) (+-comm (ext (obj r ≡ᵇ i)) (count i xs)))
                      (trans (+-assoc (count i xs) (ext (obj r ≡ᵇ i)) (count i ys))
                             (sym (count-++ i xs (r ∷ ys))))))

rot-has : ∀ i r xs ys →
  hasG1 i (r ∷ xs ++ ys) ≡ hasG1 i (xs ++ (r ∷ ys))
rot-has i r xs ys =
  trans (cong (((obj r ≡ᵇ i) ∧ isG1 (checked r)) ∨_) (has-++ i xs ys))
        (trans (sym (∨-assoc ((obj r ≡ᵇ i) ∧ isG1 (checked r)) (hasG1 i xs) (hasG1 i ys)))
               (trans (cong (_∨ hasG1 i ys) (∨-comm ((obj r ≡ᵇ i) ∧ isG1 (checked r)) (hasG1 i xs)))
                      (trans (∨-assoc (hasG1 i xs) ((obj r ≡ᵇ i) ∧ isG1 (checked r)) (hasG1 i ys))
                             (sym (has-++ i xs (r ∷ ys))))))

rot-bound : ∀ {n} r xs ys → Bound n (r ∷ xs ++ ys) → Bound n (xs ++ (r ∷ ys))
rot-bound r []       ys bd = bd
rot-bound r (x ∷ xs) ys (bcons or (bcons ox rest)) =
  bcons ox (rot-bound r xs ys (bcons or rest))

edge-nat : ∀ h n → edgeRefs (snoc h (nat n)) ≡ edgeRefs h
edge-nat h n =
  trans (edgeRefs-++ h (cell (nat n) live ∷ [])) (++-identityʳ (edgeRefs h))

edge-suc : ∀ h r → edgeRefs (snoc h (suc↑ r)) ≡ edgeRefs h ++ (r ∷ [])
edge-suc h r = edgeRefs-++ h (cell (suc↑ r) live ∷ [])

edge-clo : ∀ h env tm → edgeRefs (snoc h (clo env tm)) ≡ edgeRefs h ++ env
edge-clo h env tm =
  trans (edgeRefs-++ h (cell (clo env tm) live ∷ []))
        (cong (edgeRefs h ++_) (++-identityʳ env))

data EdgeAt (h : List Obj) (k : ℕ) (v : Val) : Set where
  eat : (L R : List Ref) →
        edgeRefs h ≡ L ++ kids v ++ R →
        edgeRefs (setPayload h k (nat zero)) ≡ L ++ R →
        EdgeAt h k v

edge-at : ∀ h k v → payloadAt h k ≡ just v → EdgeAt h k v
edge-at [] _ _ ()
edge-at (o ∷ os) zero ._ refl = eat [] (edgeRefs os) refl refl
edge-at (o ∷ os) (suc k) v eq with edge-at os k v eq
... | eat L R e1 e2 =
  eat (kids (payload o) ++ L) R
    (trans (cong (kids (payload o) ++_) e1)
           (sym (++-assoc (kids (payload o)) L (kids v ++ R))))
    (trans (cong (kids (payload o) ++_) e2)
           (sym (++-assoc (kids (payload o)) L R)))

repl-swap : ∀ k n xs a b →
  lookup xs n ≡ just a →
  count k (repl n b xs) + ext (obj a ≡ᵇ k) ≡ count k xs + ext (obj b ≡ᵇ k)
repl-swap k zero (a ∷ xs) .a b refl =
  let A = ext (obj a ≡ᵇ k)
      B = ext (obj b ≡ᵇ k)
      C = count k xs
      lhs = trans (+-right B C A) (cong (_+ C) (+-comm B A))
      rhs = +-right A C B
  in trans lhs (sym rhs)
repl-swap k (suc n) (x ∷ xs) a b eq =
  trans (+-assoc (ext (obj x ≡ᵇ k)) (count k (repl n b xs)) (ext (obj a ≡ᵇ k)))
        (trans (cong (ext (obj x ≡ᵇ k) +_) (repl-swap k n xs a b eq))
               (sym (+-assoc (ext (obj x ≡ᵇ k)) (count k xs) (ext (obj b ≡ᵇ k)))))

repl-move-has : ∀ k n xs a b →
  lookup xs n ≡ just a →
  isG1 (checked b) ≡ false →
  hasG1 k (a ∷ repl n b xs) ≡ hasG1 k xs
repl-move-has k zero (.a ∷ xs) a b refl ng rewrite ng | ∧-falseʳ (obj b ≡ᵇ k) = refl
repl-move-has k (suc n) (x ∷ xs) a b eq ng =
  trans (∨-swap ((obj a ≡ᵇ k) ∧ isG1 (checked a))
                ((obj x ≡ᵇ k) ∧ isG1 (checked x))
                (hasG1 k (repl n b xs)))
        (cong (((obj x ≡ᵇ k) ∧ isG1 (checked x)) ∨_) (repl-move-has k n xs a b eq ng))

-- Same heap and the same multiset of control references.
xfer-set : ∀ h ps i p c ps' →
  WF (sys h ps) →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  (∀ k → count k (ctlRefs c) ≡ count k (ctlRefs (ctl p))) →
  (∀ k → hasG1 k (ctlRefs c) ≡ hasG1 k (ctlRefs (ctl p))) →
  Bound (length h) (ctlRefs c) →
  WF (sys h ps')
xfer-set h ps i p c ps' wf lk es cq hq bc =
  same-ctl h ps ps' wf (set-refsPs i ps c ps' es)
    (λ k → lift-count k i ps p c ps' lk es (cq k))
    (λ k → lift-has k i ps p c ps' lk es (hq k))
    (set-ctl-bound i ps p c ps' lk es
       (proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps)
                 (proj₁ (bound-split (preOf h ps) (refsPs ps) (proj₁ wf)))))
       bc)

fresh-zero : ∀ k n rs → Bound n rs → hasG1 k rs ≡ true → ext (n ≡ᵇ k) ≡ 0
fresh-zero k n rs bd hf = no (n ≡ᵇ k) refl
  where
  no : (b : Bool) → (n ≡ᵇ k) ≡ b → ext (n ≡ᵇ k) ≡ 0
  no false eb rewrite eb = refl
  no true  eb =
    ⊥-elim (true≢false
      (trans (sym hf)
             (count0-has k rs
               (subst (λ j → count j rs ≡ 0) (≡ᵇ-sound n k eb) (bound-count0 bd n ≤-refl)))))

-- Evaluation preserves the multiset of references up to a fresh cell,
-- a dropped focus, or a regrade. Counting is done on the concatenated
-- reference list, once per kind of rearrangement.

has-nong1 : ∀ i r rs → isG1 (checked r) ≡ false → hasG1 i (r ∷ rs) ≡ hasG1 i rs
has-nong1 i r rs ng rewrite ng | ∧-falseʳ (obj r ≡ᵇ i) = refl

bit-eq : ∀ i a b → obj a ≡ obj b → checked a ≡ checked b →
         ((obj a ≡ᵇ i) ∧ isG1 (checked a)) ≡ ((obj b ≡ᵇ i) ∧ isG1 (checked b))
bit-eq i a b eo ec rewrite eo | ec = refl

cons-ext : ∀ q a b xs → obj a ≡ obj b →
           count q (a ∷ xs) ≡ ext (obj b ≡ᵇ q) + count q xs
cons-ext q a b xs eq rewrite eq = refl

repl-tail-count : ∀ i n xs r r0 ys →
  lookup xs n ≡ just r0 → obj r ≡ obj r0 →
  count i (repl n r xs ++ ys) ≡ count i (xs ++ ys)
repl-tail-count i n xs r r0 ys lk eo =
  trans (count-++ i (repl n r xs) ys)
        (trans (cong (_+ count i ys) (repl-count i n xs r r0 lk eo))
               (sym (count-++ i xs ys)))

repl-tail-has : ∀ i n xs r r0 ys →
  lookup xs n ≡ just r0 → obj r ≡ obj r0 → checked r ≡ checked r0 →
  hasG1 i (repl n r xs ++ ys) ≡ hasG1 i (xs ++ ys)
repl-tail-has i n xs r r0 ys lk eo ec =
  trans (has-++ i (repl n r xs) ys)
        (trans (cong (_∨ hasG1 i ys) (repl-has i n xs r r0 lk eo ec))
               (sym (has-++ i xs ys)))

data Focus (k : ℕ) (a : Ref) (xs : List Ref) : Set where
  focused : (rest : List Ref) →
            count k xs ≡ ext (obj a ≡ᵇ k) + count k rest →
            hasG1 k xs ≡ ((obj a ≡ᵇ k) ∧ isG1 (checked a)) ∨ hasG1 k rest →
            Focus k a xs

focus-at : ∀ k n xs a → lookup xs n ≡ just a → Focus k a xs
focus-at k zero (a ∷ xs) .a refl = focused xs refl refl
focus-at k (suc n) (x ∷ xs) a eq with focus-at k n xs a eq
... | focused rest cq hq =
  focused (x ∷ rest)
    (trans (cong (ext (obj x ≡ᵇ k) +_) cq)
           (+-swap (ext (obj x ≡ᵇ k)) (ext (obj a ≡ᵇ k)) (count k rest)))
    (trans (cong (((obj x ≡ᵇ k) ∧ isG1 (checked x)) ∨_) hq)
           (∨-swap ((obj x ≡ᵇ k) ∧ isG1 (checked x))
                   ((obj a ≡ᵇ k) ∧ isG1 (checked a))
                   (hasG1 k rest)))

nong1-ext : ∀ k ys xs zs n a →
  lookup xs n ≡ just a →
  isG1 (checked a) ≡ false →
  Grade1Unique (ys ++ xs ++ zs) →
  hasG1 k (ys ++ xs ++ zs) ≡ true →
  ext (obj a ≡ᵇ k) ≡ 0
nong1-ext k ys xs zs n a lk ng u hf = no (obj a ≡ᵇ k) refl
  where
  no : (b : Bool) → (obj a ≡ᵇ k) ≡ b → ext (obj a ≡ᵇ k) ≡ 0
  no false eb rewrite eb = refl
  no true eb with focus-at k n xs a lk
  ... | focused rest cq hq = ⊥-elim (true≢false (trans (sym hf) (gone rest cq hq)))
    where
    gone : ∀ rest →
           count k xs ≡ ext (obj a ≡ᵇ k) + count k rest →
           hasG1 k xs ≡ ((obj a ≡ᵇ k) ∧ isG1 (checked a)) ∨ hasG1 k rest →
           hasG1 k (ys ++ xs ++ zs) ≡ false
    gone rest cq hq =
      trans (has-++ k ys (xs ++ zs))
      (trans (cong (hasG1 k ys ∨_) (has-++ k xs zs))
      (trans (cong (λ b → hasG1 k ys ∨ (b ∨ hasG1 k zs)) hXs)
      (trans (cong (λ b → hasG1 k ys ∨ (false ∨ b)) hZs)
             (cong (λ b → b ∨ (false ∨ false)) hYs))))
      where
      ext1 : ext (obj a ≡ᵇ k) ≡ 1
      ext1 rewrite eb = refl
      cXs : count k xs ≡ suc (count k rest)
      cXs = trans cq (cong (_+ count k rest) ext1)
      cAll : count k (ys ++ xs ++ zs) ≡ count k ys + (count k xs + count k zs)
      cAll = trans (count-++ k ys (xs ++ zs))
                   (cong (count k ys +_) (count-++ k xs zs))
      shifted : count k (ys ++ xs ++ zs) ≡
                suc (count k ys + (count k rest + count k zs))
      shifted =
        trans cAll
        (trans (cong (λ n → count k ys + (n + count k zs)) cXs)
               (+-suc (count k ys) (count k rest + count k zs)))
      zSum : count k ys + (count k rest + count k zs) ≡ 0
      zSum = suc-inj (trans (sym shifted) (u k hf))
      zY : count k ys ≡ 0
      zY = proj₁ (+-zero (count k ys) (count k rest + count k zs) zSum)
      zTail : count k rest + count k zs ≡ 0
      zTail = proj₂ (+-zero (count k ys) (count k rest + count k zs) zSum)
      zR : count k rest ≡ 0
      zR = proj₁ (+-zero (count k rest) (count k zs) zTail)
      zZ : count k zs ≡ 0
      zZ = proj₂ (+-zero (count k rest) (count k zs) zTail)
      flat : ((obj a ≡ᵇ k) ∧ isG1 (checked a)) ≡ false
      flat rewrite eb | ng = refl
      hXs : hasG1 k xs ≡ false
      hXs = trans hq (trans (cong (_∨ hasG1 k rest) flat)
                            (cong (false ∨_) (count0-has k rest zR)))
      hYs : hasG1 k ys ≡ false
      hYs = count0-has k ys zY
      hZs : hasG1 k zs ≡ false
      hZs = count0-has k zs zZ

regroup : ∀ (e L env fr R rs : List Ref) →
  (e ++ (L ++ ((env ++ fr) ++ R))) ++ rs ≡
  (e ++ L) ++ env ++ (fr ++ (R ++ rs))
regroup e L env fr R rs =
  trans (++-assoc e seg rs)
  (trans (cong (e ++_) (++-assoc L mid rs))
  (trans (sym (++-assoc e L (mid ++ rs)))
         (cong ((e ++ L) ++_)
           (trans (++-assoc (env ++ fr) R rs)
                  (++-assoc env fr (R ++ rs))))))
  where
  mid = (env ++ fr) ++ R
  seg = L ++ mid

data SplitCtl (ps : List Proc) (p : Proc) : Set where
  spl : (L R : List Ref) →
        ctlRefsPs ps ≡ L ++ ctlRefs (ctl p) ++ R →
        SplitCtl ps p

split-ctl : ∀ i ps p → lookup ps i ≡ just p → SplitCtl ps p
split-ctl _ [] _ ()
split-ctl zero (p ∷ ps) .p refl = spl [] (ctlRefsPs ps) refl
split-ctl (suc i) (q ∷ ps) p lk with split-ctl i ps p lk
... | spl L R eq =
  spl (ctlRefs (ctl q) ++ L) R
    (trans (cong (ctlRefs (ctl q) ++_) eq)
           (sym (++-assoc (ctlRefs (ctl q)) L (ctlRefs (ctl p) ++ R))))

plus2 : ∀ E C R de dc →
  ((E + de) + (C + dc)) + R ≡ ((E + C) + R) + (de + dc)
plus2 E C R de dc = trans (cong (_+ R) step) (+-right (E + C) (de + dc) R)
  where
  step : (E + de) + (C + dc) ≡ (E + C) + (de + dc)
  step =
    trans (sym (+-assoc (E + de) C dc))
    (trans (cong (_+ dc) (+-assoc E de C))
    (trans (cong (λ x → (E + x) + dc) (+-comm de C))
    (trans (cong (_+ dc) (sym (+-assoc E C de)))
           (+-assoc (E + C) de dc))))

count-shift : ∀ k h h' ps ps' de dc →
  count k (edgeRefs h') ≡ count k (edgeRefs h) + de →
  count k (ctlRefsPs ps') ≡ count k (ctlRefsPs ps) + dc →
  count k (refsPs ps') ≡ count k (refsPs ps) →
  count k (refsOf (sys h' ps')) ≡ count k (refsOf (sys h ps)) + (de + dc)
count-shift k h h' ps ps' de dc ee ce re =
  trans (refs-count k h' ps')
  (trans (cong (λ e → (e + count k (ctlRefsPs ps')) + count k (refsPs ps')) ee)
  (trans (cong (λ c → ((count k (edgeRefs h) + de) + c) + count k (refsPs ps')) ce)
  (trans (cong (λ r → ((count k (edgeRefs h) + de) + (count k (ctlRefsPs ps) + dc)) + r) re)
         (trans (plus2 (count k (edgeRefs h)) (count k (ctlRefsPs ps)) (count k (refsPs ps)) de dc)
                (cong (_+ (de + dc)) (sym (refs-count k h ps)))))))

has-stable : ∀ k h h' ps ps' →
  hasG1 k (edgeRefs h') ≡ hasG1 k (edgeRefs h) →
  hasG1 k (ctlRefsPs ps') ≡ hasG1 k (ctlRefsPs ps) →
  hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps) →
  hasG1 k (refsOf (sys h' ps')) ≡ hasG1 k (refsOf (sys h ps))
has-stable k h h' ps ps' he hc hr =
  trans (refs-has k h' ps')
  (trans (cong (λ e → (e ∨ hasG1 k (ctlRefsPs ps')) ∨ hasG1 k (refsPs ps')) he)
  (trans (cong (λ c → (hasG1 k (edgeRefs h) ∨ c) ∨ hasG1 k (refsPs ps')) hc)
  (trans (cong (λ b → (hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs ps)) ∨ b) hr)
         (sym (refs-has k h ps)))))

from-sum : ∀ n e → n + e ≡ suc zero → suc zero ≤ n → n ≡ suc zero
from-sum n e eq ge = body (≤1 n ge)
  where
  body : Σ ℕ (λ m → n ≡ suc m) → n ≡ suc zero
  body (m , en) =
    trans en (cong suc (proj₁ (+-zero m e
      (suc-inj (subst (λ x → x + e ≡ suc zero) en eq)))))

le-from-plus : ∀ {a b c} → a + b ≡ c → a ≤ c
le-from-plus {a} {b} eq = subst (λ n → a ≤ n) eq (m≤m+k a b)

sum0 : ∀ a b → a ≡ 0 → b ≡ 0 → a + b ≡ 0
sum0 a b ea eb rewrite ea | eb = refl

count-ge-seg : ∀ i ys xs zs → count i xs ≤ count i (ys ++ xs ++ zs)
count-ge-seg i ys xs zs =
  subst (λ n → count i xs ≤ n) (sym (count3 i ys xs zs))
        (k≤n+k (count i (ys ++ zs)) (count i xs))

sub-zero : ∀ i ys xs zs → count i (ys ++ xs ++ zs) ≡ 0 → count i xs ≡ 0
sub-zero i ys xs zs eq =
  proj₂ (+-zero (count i (ys ++ zs)) (count i xs)
           (trans (sym (count3 i ys xs zs)) eq))

squeeze3 : ∀ a b c → (a + b) + c ≡ suc zero → suc zero ≤ b →
           a ≡ 0 × b ≡ suc zero × c ≡ 0
squeeze3 a b c eq ge = body (≤1 b ge)
  where
  body : Σ ℕ (λ m → b ≡ suc m) → a ≡ 0 × b ≡ suc zero × c ≡ 0
  body (m , eb) =
    let step = subst (λ x → (a + x) + c ≡ suc zero) eb eq
        flat = suc-inj (trans (sym (cong (_+ c) (+-suc a m))) step)
        zam = proj₁ (+-zero (a + m) c flat)
        zc = proj₂ (+-zero (a + m) c flat)
        za = proj₁ (+-zero a m zam)
        zm = proj₂ (+-zero a m zam)
    in za , trans eb (cong suc zm) , zc

count-insert : ∀ i xs y ys →
  count i (xs ++ (y ∷ ys)) ≡ count i (xs ++ ys) + ext (obj y ≡ᵇ i)
count-insert i xs y ys =
  trans (count-++ i xs (y ∷ ys))
  (trans (cong (count i xs +_) (+-comm (ext (obj y ≡ᵇ i)) (count i ys)))
  (trans (sym (+-assoc (count i xs) (count i ys) (ext (obj y ≡ᵇ i))))
         (cong (_+ ext (obj y ≡ᵇ i)) (sym (count-++ i xs ys)))))

insert-has : ∀ i xs z ys →
  hasG1 i (xs ++ ys) ≡ true → hasG1 i (xs ++ (z ∷ ys)) ≡ true
insert-has i xs z ys hf = body (hasG1 i xs) refl hf
  where
  bit = (obj z ≡ᵇ i) ∧ isG1 (checked z)
  body : (b : Bool) → hasG1 i xs ≡ b → hasG1 i (xs ++ ys) ≡ true →
         hasG1 i (xs ++ (z ∷ ys)) ≡ true
  body true eb _ =
    trans (has-++ i xs (z ∷ ys))
          (cong (_∨ hasG1 i (z ∷ ys)) eb)
  body false eb hk =
    trans (has-++ i xs (z ∷ ys))
    (trans (cong (λ b → b ∨ hasG1 i (z ∷ ys)) eb)
           (subst (λ b → (bit ∨ b) ≡ true) (sym ysHas) (∨-trueʳ bit)))
    where
    ysHas = trans (sym (cong (λ b → b ∨ hasG1 i ys) eb))
                  (trans (sym (has-++ i xs ys)) hk)

new-is-tail : ∀ q r xs ys →
  ((obj r ≡ᵇ q) ∧ isG1 (checked r)) ≡ false →
  hasG1 q xs ≡ false →
  hasG1 q (r ∷ xs ++ ys) ≡ true →
  hasG1 q ys ≡ true
new-is-tail q r xs ys bf ez hf =
  let bit = (obj r ≡ᵇ q) ∧ isG1 (checked r)
      step1 = trans (sym (cong (λ b → bit ∨ b) (has-++ q xs ys))) hf
      step2 = trans (sym (cong (λ b → b ∨ (hasG1 q xs ∨ hasG1 q ys)) bf)) step1
  in trans (sym (cong (λ b → b ∨ hasG1 q ys) ez)) step2

drop-head-le : ∀ i r xs → count i xs ≤ count i (r ∷ xs)
drop-head-le i r xs = k≤n+k (ext (obj r ≡ᵇ i)) (count i xs)

drop-head-has : ∀ i r xs → hasG1 i xs ≡ true → hasG1 i (r ∷ xs) ≡ true
drop-head-has i r xs = has-right i (r ∷ []) xs

bound-uncons : ∀ {n r xs} → Bound n (r ∷ xs) → Bound n xs
bound-uncons (bcons _ rest) = rest

drop-mid-le : ∀ i r xs ys → count i (r ∷ ys) ≤ count i (r ∷ xs ++ ys)
drop-mid-le i r xs ys =
  subst (λ n → count i (r ∷ ys) ≤ n)
        (sym (cong (ext (obj r ≡ᵇ i) +_) (count-++ i xs ys)))
        (≤-+ˡ (ext (obj r ≡ᵇ i)) (k≤n+k (count i xs) (count i ys)))

drop-mid-has : ∀ i r xs ys →
  hasG1 i (r ∷ ys) ≡ true → hasG1 i (r ∷ xs ++ ys) ≡ true
drop-mid-has i r xs ys hf = body ((obj r ≡ᵇ i) ∧ isG1 (checked r)) refl hf
  where
  body : (b : Bool) → ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ≡ b →
         ((obj r ≡ᵇ i) ∧ isG1 (checked r)) ∨ hasG1 i ys ≡ true →
         hasG1 i (r ∷ xs ++ ys) ≡ true
  body true eb _ =
    cong (λ b → b ∨ hasG1 i (xs ++ ys)) eb
  body false eb hk =
    trans (cong (λ b → b ∨ hasG1 i (xs ++ ys)) eb)
          (has-right i xs ys
            (trans (sym (cong (λ b → b ∨ hasG1 i ys) eb)) hk))

drop-mid-bound : ∀ {n} r xs ys → Bound n (r ∷ xs ++ ys) → Bound n (r ∷ ys)
drop-mid-bound r xs ys (bcons lt rest) =
  bcons lt (proj₂ (bound-split xs ys rest))

lift-le : ∀ k i ps p c ps' →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  count k (ctlRefs c) ≤ count k (ctlRefs (ctl p)) →
  count k (ctlRefsPs ps') ≤ count k (ctlRefsPs ps)
lift-le k zero (p ∷ ps) .p c .(record p { ctl = c } ∷ ps) refl refl le =
  subst (λ n → n ≤ count k (ctlRefs (ctl p) ++ ctlRefsPs ps))
        (sym (count-++ k (ctlRefs c) (ctlRefsPs ps)))
        (subst (λ n → count k (ctlRefs c) + count k (ctlRefsPs ps) ≤ n)
               (sym (count-++ k (ctlRefs (ctl p)) (ctlRefsPs ps)))
               (≤-+ʳ (count k (ctlRefsPs ps)) le))
lift-le k (suc i) (q ∷ ps) p c ps' lk eq le = tail (setProc ps i c) eq refl
  where
  tail : (m : Maybe (List Proc)) → mapCons q m ≡ just ps' → setProc ps i c ≡ m →
         count k (ctlRefsPs ps') ≤ count k (ctlRefsPs (q ∷ ps))
  tail nothing () _
  tail (just qs) refl eqs =
    subst (λ n → n ≤ count k (ctlRefs (ctl q) ++ ctlRefsPs ps))
          (sym (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs)))
          (subst (λ n → count k (ctlRefs (ctl q)) + count k (ctlRefsPs qs) ≤ n)
                 (sym (count-++ k (ctlRefs (ctl q)) (ctlRefsPs ps)))
                 (≤-+ˡ (count k (ctlRefs (ctl q)))
                       (lift-le k i ps p c qs lk eqs le)))

lift-has-imp : ∀ k i ps p c ps' →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  (hasG1 k (ctlRefs c) ≡ true → hasG1 k (ctlRefs (ctl p)) ≡ true) →
  hasG1 k (ctlRefsPs ps') ≡ true →
  hasG1 k (ctlRefsPs ps) ≡ true
lift-has-imp k zero (p ∷ ps) .p c .(record p { ctl = c } ∷ ps) refl refl imp hf =
  has-cat k (ctlRefs c) (ctlRefsPs ps) (ctlRefs (ctl p)) (ctlRefsPs ps) imp (λ z → z) hf
lift-has-imp k (suc i) (q ∷ ps) p c ps' lk eq imp hf = tail (setProc ps i c) eq refl hf
  where
  tail : (m : Maybe (List Proc)) → mapCons q m ≡ just ps' → setProc ps i c ≡ m →
         hasG1 k (ctlRefsPs ps') ≡ true → hasG1 k (ctlRefsPs (q ∷ ps)) ≡ true
  tail nothing () _ _
  tail (just qs) refl eqs hf' =
    has-cat k (ctlRefs (ctl q)) (ctlRefsPs qs)
            (ctlRefs (ctl q)) (ctlRefsPs ps)
            (λ z → z) (lift-has-imp k i ps p c qs lk eqs imp) hf'

lift-swap : ∀ k i ps p c ps' n m →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  count k (ctlRefs c) + n ≡ count k (ctlRefs (ctl p)) + m →
  count k (ctlRefsPs ps') + n ≡ count k (ctlRefsPs ps) + m
lift-swap k zero (p ∷ ps) .p c .(record p { ctl = c } ∷ ps) n m refl refl eq =
  trans (cong (_+ n) (count-++ k (ctlRefs c) (ctlRefsPs ps)))
  (trans (+-right (count k (ctlRefs c)) (count k (ctlRefsPs ps)) n)
  (trans (cong (_+ count k (ctlRefsPs ps)) eq)
  (trans (sym (+-right (count k (ctlRefs (ctl p))) (count k (ctlRefsPs ps)) m))
         (cong (_+ m) (sym (count-++ k (ctlRefs (ctl p)) (ctlRefsPs ps)))))))
lift-swap k (suc i) (q ∷ ps) p c ps' n m lk eq eqc = tail (setProc ps i c) eq refl
  where
  tail : (m' : Maybe (List Proc)) → mapCons q m' ≡ just ps' → setProc ps i c ≡ m' →
         count k (ctlRefsPs ps') + n ≡ count k (ctlRefsPs (q ∷ ps)) + m
  tail nothing () _
  tail (just qs) refl eqs =
    trans (cong (_+ n) (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs)))
    (trans (+-assoc (count k (ctlRefs (ctl q))) (count k (ctlRefsPs qs)) n)
    (trans (cong (count k (ctlRefs (ctl q)) +_)
                 (lift-swap k i ps p c qs n m lk eqs eqc))
    (trans (sym (+-assoc (count k (ctlRefs (ctl q))) (count k (ctlRefsPs ps)) m))
           (cong (_+ m) (sym (count-++ k (ctlRefs (ctl q)) (ctlRefsPs ps)))))))

shift-count : ∀ E C C' R n m →
  C' + n ≡ C + m →
  ((E + C') + R) + n ≡ ((E + C) + R) + m
shift-count E C C' R n m eq =
  trans (+-right (E + C') R n)
  (trans (cong (_+ R) (+-assoc E C' n))
  (trans (cong (λ z → (E + z) + R) eq)
  (trans (cong (_+ R) (sym (+-assoc E C m)))
         (sym (+-right (E + C) R m)))))

move-edge : ∀ E E' C R X →
  E' + X ≡ E →
  ((E' + C) + R) + X ≡ (E + C) + R
move-edge E E' C R X eq =
  trans (+-right (E' + C) R X)
  (trans (cong (_+ R) (+-assoc E' C X))
  (trans (cong (λ z → (E' + z) + R) (+-comm C X))
  (trans (cong (_+ R) (sym (+-assoc E' X C)))
         (cong (λ z → (z + C) + R) eq))))

drop-move : ∀ E E' C C' R X F →
  E' + X ≡ E →
  C' + F ≡ C + X →
  ((E' + C') + R) + F ≡ (E + C) + R
drop-move E E' C C' R X F eEq cEq =
  trans (shift-count E' C C' R F X cEq) (move-edge E E' C R X eEq)

gain-fresh : ∀ E X C C' R B →
  C' + X ≡ C + B →
  ((E + X) + C') + R ≡ ((E + C) + R) + B
gain-fresh E X C C' R B eq = trans (cong (_+ R) step) (+-right (E + C) B R)
  where
  step : (E + X) + C' ≡ (E + C) + B
  step =
    trans (+-assoc E X C')
    (trans (cong (E +_) (+-comm X C'))
    (trans (cong (E +_) eq)
           (sym (+-assoc E C B))))

shuffle : ∀ A N E T F →
  (A + (N + (E + T))) + F ≡ (A + (E + (F + T))) + N
shuffle A N E T F = trans (stepL A N E T F) (sym (stepR A N E T F))
  where
  stepL : ∀ A N E T F → (A + (N + (E + T))) + F ≡ (((A + E) + T) + F) + N
  stepL A N E T F =
    trans (cong (_+ F) (sym (+-assoc A N (E + T))))
    (trans (cong (_+ F) (sym (+-assoc (A + N) E T)))
    (trans (cong (λ z → (z + T) + F) (+-assoc A N E))
    (trans (cong (λ z → ((A + z) + T) + F) (+-comm N E))
    (trans (cong (λ z → (z + T) + F) (sym (+-assoc A E N)))
    (trans (+-right ((A + E) + N) T F)
    (trans (cong (_+ T) (+-assoc (A + E) N F))
    (trans (cong (λ z → ((A + E) + z) + T) (+-comm N F))
    (trans (cong (_+ T) (sym (+-assoc (A + E) F N)))
    (trans (+-right ((A + E) + F) N T)
           (cong (_+ N) (sym (+-right (A + E) T F))))))))))))
  stepR : ∀ A N E T F → (A + (E + (F + T))) + N ≡ (((A + E) + T) + F) + N
  stepR A N E T F =
    trans (cong (_+ N) (sym (+-assoc A E (F + T))))
    (trans (cong (_+ N) (sym (+-assoc (A + E) F T)))
           (cong (_+ N) (+-right (A + E) F T)))

beta-local : ∀ q ra rg rf envC env fr →
  obj rg ≡ obj ra →
  count q (rg ∷ envC ++ (env ++ fr)) + ext (obj rf ≡ᵇ q) ≡
  count q (ra ∷ env ++ (rf ∷ fr)) + count q envC
beta-local q ra rg rf envC env fr eo =
  trans (cong (_+ F) newC)
  (trans (shuffle A N E T F)
         (sym (cong (_+ N) oldC)))
  where
  A = ext (obj ra ≡ᵇ q)
  N = count q envC
  E = count q env
  T = count q fr
  F = ext (obj rf ≡ᵇ q)
  newC : count q (rg ∷ envC ++ (env ++ fr)) ≡ A + (N + (E + T))
  newC =
    trans (cons-ext q rg ra (envC ++ (env ++ fr)) eo)
    (trans (cong (A +_) (count-++ q envC (env ++ fr)))
           (cong (λ z → A + (N + z)) (count-++ q env fr)))
  oldC : count q (ra ∷ env ++ (rf ∷ fr)) ≡ A + (E + (F + T))
  oldC = cong (A +_) (count-++ q env (rf ∷ fr))

move-count : ∀ q n xs a a' b ys →
  lookup xs n ≡ just a →
  obj a' ≡ obj a →
  count q (a' ∷ repl n b xs ++ ys) ≡ count q (xs ++ ys) + ext (obj b ≡ᵇ q)
move-count q n xs a a' b ys lk eo =
  trans (cong (ext (obj a' ≡ᵇ q) +_) (count-++ q (repl n b xs) ys))
  (trans (cong (λ o → ext (o ≡ᵇ q) + (count q (repl n b xs) + count q ys)) eo)
  (trans (sym (+-assoc (ext (obj a ≡ᵇ q)) (count q (repl n b xs)) (count q ys)))
  (trans (cong (_+ count q ys) (+-comm (ext (obj a ≡ᵇ q)) (count q (repl n b xs))))
  (trans (cong (_+ count q ys) (repl-swap q n xs a b lk))
  (trans (+-right (count q xs) (ext (obj b ≡ᵇ q)) (count q ys))
         (cong (_+ ext (obj b ≡ᵇ q)) (sym (count-++ q xs ys))))))))

move-has : ∀ q n xs a a' b ys →
  lookup xs n ≡ just a →
  obj a' ≡ obj a →
  checked a' ≡ checked a →
  isG1 (checked b) ≡ false →
  hasG1 q (a' ∷ repl n b xs ++ ys) ≡ hasG1 q (xs ++ ys)
move-has q n xs a a' b ys lk eo ec ng =
  trans (has-++ q (a' ∷ repl n b xs) ys)
  (trans (cong (_∨ hasG1 q ys) (cong (λ z → z ∨ hasG1 q (repl n b xs)) (bit-eq q a' a eo ec)))
  (trans (cong (_∨ hasG1 q ys) (repl-move-has q n xs a b lk ng))
         (sym (has-++ q xs ys))))

or-move5 : ∀ a b l t r →
  ((a ∨ b) ∨ (l ∨ (t ∨ r))) ≡ (a ∨ (l ∨ ((b ∨ t) ∨ r)))
or-move5 a b l t r =
  trans (sym (∨-assoc (a ∨ b) l (t ∨ r)))
  (trans (cong (_∨ (t ∨ r)) (∨-assoc a b l))
  (trans (cong (λ z → (a ∨ z) ∨ (t ∨ r)) (∨-comm b l))
  (trans (∨-assoc a (l ∨ b) (t ∨ r))
  (trans (cong (a ∨_) (sym (∨-assoc (l ∨ b) t r)))
  (trans (cong (λ z → a ∨ (z ∨ r)) (∨-assoc l b t))
         (cong (a ∨_) (∨-assoc l (b ∨ t) r)))))))

has3 : ∀ i xs ys zs →
  hasG1 i (xs ++ ys ++ zs) ≡ hasG1 i xs ∨ hasG1 i ys ∨ hasG1 i zs
has3 i xs ys zs =
  trans (has-++ i xs (ys ++ zs))
        (cong (hasG1 i xs ∨_) (has-++ i ys zs))

length-set : ∀ h k v → length (setPayload h k v) ≡ length h
length-set [] _ _ = refl
length-set (_ ∷ _) zero _ = refl
length-set (_ ∷ os) (suc k) v rewrite length-set os k v = refl

monoS : ∀ {n rs} → Bound n rs → Bound (suc n) rs
monoS = bound-mono (≤-step ≤-refl)

close-bound : ∀ h' ps' n →
  length h' ≡ n →
  Bound n (edgeRefs h') →
  Bound n (ctlRefsPs ps') →
  Bound n (refsPs ps') →
  Bound (length h') (refsOf (sys h' ps'))
close-bound h' ps' n eq be bc br =
  subst (λ m → Bound m (refsOf (sys h' ps'))) (sym eq)
        (bound-++ (bound-++ be bc) br)

grow-sys : ∀ {h ps} h' ps' (extra : ℕ → ℕ) →
  WF (sys h ps) →
  Bound (length h') (refsOf (sys h' ps')) →
  (∀ k → count k (refsOf (sys h' ps')) ≡ count k (refsOf (sys h ps)) + extra k) →
  (∀ k → hasG1 k (refsOf (sys h' ps')) ≡ hasG1 k (refsOf (sys h ps))) →
  (∀ k → hasG1 k (refsOf (sys h ps)) ≡ true → extra k ≡ 0) →
  WF (sys h' ps')
grow-sys {h} {ps} h' ps' extra (_ , uq) bd cq hq zx =
  bd , grow-unique (refsOf (sys h' ps')) (refsOf (sys h ps)) extra cq hq zx uq

has-imp-heap : ∀ k h h' ps ps' →
  (hasG1 k (edgeRefs h') ≡ true → hasG1 k (edgeRefs h) ≡ true) →
  (hasG1 k (ctlRefsPs ps') ≡ true → hasG1 k (ctlRefsPs ps) ≡ true) →
  hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps) →
  hasG1 k (refsOf (sys h' ps')) ≡ true →
  hasG1 k (refsOf (sys h ps)) ≡ true
has-imp-heap k h h' ps ps' he hc hr hf =
  has-cat k (preOf h' ps') (refsPs ps') (preOf h ps) (refsPs ps)
    (λ hp → has-cat k (edgeRefs h') (ctlRefsPs ps') (edgeRefs h) (ctlRefsPs ps) he hc hp)
    (λ hq → subst (λ b → b ≡ true) hr hq)
    hf

count-le-ctl : ∀ k h ps ps' →
  count k (ctlRefsPs ps') ≤ count k (ctlRefsPs ps) →
  count k (refsPs ps') ≡ count k (refsPs ps) →
  count k (refsOf (sys h ps')) ≤ count k (refsOf (sys h ps))
count-le-ctl k h ps ps' leC re =
  subst (λ n → n ≤ count k (refsOf (sys h ps)))
        (sym (refs-count k h ps'))
        (subst (λ n → (count k (edgeRefs h) + count k (ctlRefsPs ps')) + count k (refsPs ps') ≤ n)
               (sym (refs-count k h ps))
               (≤-trans step1 step2))
  where
  E = count k (edgeRefs h)
  C' = count k (ctlRefsPs ps')
  R' = count k (refsPs ps')
  R = count k (refsPs ps)
  step1 : (E + C') + R' ≤ (E + C') + R
  step1 = subst (λ n → (E + C') + R' ≤ (E + C') + n) re (≤-+ʳ R' ≤-refl)
  step2 : (E + C') + R ≤ (E + count k (ctlRefsPs ps)) + R
  step2 = ≤-+ʳ R (≤-+ˡ E leC)

thin-sys : ∀ h ps ps' →
  WF (sys h ps) →
  refsPs ps' ≡ refsPs ps →
  (∀ k → count k (ctlRefsPs ps') ≤ count k (ctlRefsPs ps)) →
  (∀ k → hasG1 k (ctlRefsPs ps') ≡ true → hasG1 k (ctlRefsPs ps) ≡ true) →
  Bound (length h) (ctlRefsPs ps') →
  WF (sys h ps')
thin-sys h ps ps' (bdF , uq) rq leC hc bc =
  bound-++ (bound-++ bEdge bc) (subst (Bound (length h)) (sym rq) bRs)
  , thin-unique (refsOf (sys h ps')) (refsOf (sys h ps))
      (λ k → count-le-ctl k h ps ps' (leC k) (cong (count k) rq))
      (λ k → has-imp-heap k h h ps ps' (λ z → z) (hc k) (cong (hasG1 k) rq))
      uq
  where
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bdF)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bdF)

stuck-just : ∀ {A B : Set} {x : B} → nothing ≡ just x → A
stuck-just ()

bound-lookup : ∀ {n} xs i r → Bound n xs → lookup xs i ≡ just r → obj r < n
bound-lookup [] _ _ _ ()
bound-lookup (r ∷ _) zero .r (bcons lt _) refl = lt
bound-lookup (_ ∷ xs) (suc i) r (bcons _ rest) eq = bound-lookup xs i r rest eq

bound-repl-< : ∀ {n} i xs b a →
  Bound n xs → lookup xs i ≡ just a → obj b < n → Bound n (repl i b xs)
bound-repl-< _ [] _ _ _ () _
bound-repl-< zero (a ∷ xs) _ .a (bcons _ rest) refl lt = bcons lt rest
bound-repl-< (suc i) (_ ∷ xs) b a (bcons lt rest) eq ob =
  bcons lt (bound-repl-< i xs b a rest eq ob)

-- (b + t) + x = (x + t) + b. A focus and a moved edge trade places.
addXB : ∀ b t x → (b + t) + x ≡ (x + t) + b
addXB b t x =
  trans (+-assoc b t x)
  (trans (cong (b +_) (+-comm t x))
  (trans (sym (+-assoc b x t))
  (trans (cong (_+ t) (+-comm b x))
  (trans (+-assoc x b t)
  (trans (cong (x +_) (+-comm b t))
         (sym (+-assoc x t b)))))))

has-miss : ∀ q r rs → (obj r ≡ᵇ q) ≡ false → hasG1 q (r ∷ rs) ≡ hasG1 q rs
has-miss q r rs eb rewrite eb = refl

head-< : ∀ {n r xs} → Bound n (r ∷ xs) → obj r < n
head-< (bcons lt _) = lt

-- The caller's env and frames stay live when a function ref is dropped.
caller-has : ∀ q ra rf env fr →
  hasG1 q (env ++ fr) ≡ true →
  hasG1 q (ra ∷ env ++ (rf ∷ fr)) ≡ true
caller-has q ra rf env fr hf = step (hasG1 q env) refl
  where
  step : (b : Bool) → hasG1 q env ≡ b → hasG1 q (ra ∷ env ++ (rf ∷ fr)) ≡ true
  step true eb =
    drop-head-has q ra (env ++ (rf ∷ fr)) (has-left q env (rf ∷ fr) eb)
  step false eb rewrite has-++ q env fr | eb =
    drop-head-has q ra (env ++ (rf ∷ fr))
      (has-right q env (rf ∷ fr) (drop-head-has q rf fr hf))

-- A closure environment is one contiguous segment of the reference list.
clo-seg : ∀ (L envC R ctl rs : List Ref) →
  ((L ++ (envC ++ R)) ++ ctl) ++ rs ≡
  L ++ (envC ++ ((R ++ ctl) ++ rs))
clo-seg L envC R ctl rs =
  trans (++-assoc (L ++ (envC ++ R)) ctl rs)
  (trans (++-assoc L (envC ++ R) (ctl ++ rs))
  (trans (cong (L ++_) (++-assoc envC R (ctl ++ rs)))
         (cong (λ z → L ++ (envC ++ z)) (sym (++-assoc R ctl rs)))))

-- A bit that moves from control into a new edge does not change hasG1.
move-has5 : ∀ a a' b l t t' r c c' p p' →
  a' ≡ a ∨ b →
  c' ≡ l ∨ (t' ∨ r) →
  t' ≡ t →
  c ≡ l ∨ ((b ∨ t) ∨ r) →
  p' ≡ p →
  (a' ∨ c') ∨ p' ≡ (a ∨ c) ∨ p
move-has5 a a' b l t t' r c c' p p' ea ec' et ec ep =
  trans (cong (λ x → (x ∨ c') ∨ p') ea)
  (trans (cong (λ x → ((a ∨ b) ∨ x) ∨ p') ec')
  (trans (cong (λ x → ((a ∨ b) ∨ (l ∨ (x ∨ r))) ∨ p') et)
  (trans (cong (λ x → ((a ∨ b) ∨ (l ∨ (t ∨ r))) ∨ x) ep)
  (trans (cong (_∨ p) (or-move5 a b l t r))
         (cong (λ x → (a ∨ x) ∨ p) (sym ec))))))

eval-wf : ∀ h ps i t →
  eval1 (sys h ps) i ≡ just t →
  WF (sys h ps) →
  WF t
eval-wf h ps i t eq (bdF , uqF) = at (lookup ps i) eq refl
  where
  wf = bdF , uqF
  nH = length h
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bdF)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bCtl = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bdF)

  at : (m : Maybe Proc) → eval1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  at nothing e lk rewrite lk with e
  ... | ()
  at (just p) e lk rewrite lk = on (ctl p) e refl
    where
    bHere = ctl-bound-at i ps p lk bCtl

    grow-nat : ∀ n c →
      (∀ q → count q (ctlRefs c) ≡ count q (ctlRefs (ctl p)) + ext (nH ≡ᵇ q)) →
      (∀ q → hasG1 q (ctlRefs c) ≡ hasG1 q (ctlRefs (ctl p))) →
      Bound (suc nH) (ctlRefs c) →
      install (snoc h (nat n)) ps i c ≡ just t →
      WF t
    grow-nat n c cLoc hLoc bLoc eI = landed (setProc ps i c) eI refl
      where
      h2 = snoc h (nat n)
      landed : (m : Maybe (List Proc)) → mapSys h2 m ≡ just t → setProc ps i c ≡ m → WF t
      landed nothing () _
      landed (just ps2) eqj es = subst WF (just-inj eqj) got
        where
        rq = set-refsPs i ps c ps2 es
        cq = λ q → count-shift q h h2 ps ps2 zero (ext (nH ≡ᵇ q))
               (trans (cong (count q) (edge-nat h n))
                      (sym (+-identityʳ (count q (edgeRefs h)))))
               (lift-plus q i ps p c ps2 (ext (nH ≡ᵇ q)) lk es (cLoc q))
               (cong (count q) rq)
        hq = λ q → has-stable q h h2 ps ps2
               (cong (hasG1 q) (edge-nat h n))
               (lift-has q i ps p c ps2 lk es (hLoc q))
               (cong (hasG1 q) rq)
        bNew = close-bound h2 ps2 (suc nH) (length-snoc h (cell (nat n) live))
                 (subst (Bound (suc nH)) (sym (edge-nat h n)) (monoS bEdge))
                 (set-ctl-bound i ps p c ps2 lk es (monoS bCtl) bLoc)
                 (monoS (subst (Bound nH) (sym rq) bRs))
        got = grow-sys {h} {ps} h2 ps2 (λ q → ext (nH ≡ᵇ q)) wf bNew cq hq
                (λ q hf → fresh-zero q nH (refsOf (sys h ps)) bdF hf)

    alias-focus : ∀ c (extra : ℕ → ℕ) →
      (∀ q → count q (ctlRefs c) ≡ count q (ctlRefs (ctl p)) + extra q) →
      (∀ q → hasG1 q (ctlRefs c) ≡ hasG1 q (ctlRefs (ctl p))) →
      (∀ q → hasG1 q (refsOf (sys h ps)) ≡ true → extra q ≡ 0) →
      Bound nH (ctlRefs c) →
      install h ps i c ≡ just t →
      WF t
    alias-focus c extra cLoc hLoc zx bLoc eI = landed (setProc ps i c) eI refl
      where
      landed : (m : Maybe (List Proc)) → mapSys h m ≡ just t → setProc ps i c ≡ m → WF t
      landed nothing () _
      landed (just ps2) eqj es = subst WF (just-inj eqj) got
        where
        rq = set-refsPs i ps c ps2 es
        cq = λ q → count-shift q h h ps ps2 zero (extra q)
               (sym (+-identityʳ (count q (edgeRefs h))))
               (lift-plus q i ps p c ps2 (extra q) lk es (cLoc q))
               (cong (count q) rq)
        hq = λ q → has-stable q h h ps ps2 refl
               (lift-has q i ps p c ps2 lk es (hLoc q))
               (cong (hasG1 q) rq)
        bNew = close-bound h ps2 nH refl bEdge
                 (set-ctl-bound i ps p c ps2 lk es bCtl bLoc)
                 (subst (Bound nH) (sym rq) bRs)
        got = grow-sys {h} {ps} h ps2 extra wf bNew cq hq zx

    thin-ctl : ∀ c →
      (∀ q → count q (ctlRefs c) ≤ count q (ctlRefs (ctl p))) →
      (∀ q → hasG1 q (ctlRefs c) ≡ true → hasG1 q (ctlRefs (ctl p)) ≡ true) →
      Bound nH (ctlRefs c) →
      install h ps i c ≡ just t →
      WF t
    thin-ctl c leC hi bc eI = landed (setProc ps i c) eI refl
      where
      landed : (m : Maybe (List Proc)) → mapSys h m ≡ just t → setProc ps i c ≡ m → WF t
      landed nothing () _
      landed (just ps2) eqj es = subst WF (just-inj eqj) got
        where
        rq = set-refsPs i ps c ps2 es
        got = thin-sys h ps ps2 wf rq
                (λ q → lift-le q i ps p c ps2 lk es (leC q))
                (λ q → lift-has-imp q i ps p c ps2 lk es (hi q))
                (set-ctl-bound i ps p c ps2 lk es bCtl bc)

    xfer-ctl : ∀ c →
      (∀ q → count q (ctlRefs c) ≡ count q (ctlRefs (ctl p))) →
      (∀ q → hasG1 q (ctlRefs c) ≡ hasG1 q (ctlRefs (ctl p))) →
      Bound nH (ctlRefs c) →
      install h ps i c ≡ just t →
      WF t
    xfer-ctl c cq hq bc eI = landed (setProc ps i c) eI refl
      where
      landed : (m : Maybe (List Proc)) → mapSys h m ≡ just t → setProc ps i c ≡ m → WF t
      landed nothing () _
      landed (just ps2) eqj es =
        subst WF (just-inj eqj) (xfer-set h ps i p c ps2 wf lk es cq hq bc)

    push : ∀ c → ctlRefs c ≡ ctlRefs (ctl p) → install h ps i c ≡ just t → WF t
    push c creq eI =
      xfer-ctl c (λ q → cong (count q) creq) (λ q → cong (hasG1 q) creq)
        (subst (Bound nH) (sym creq) bHere) eI

    freshUnit : ∀ env k →
      ctlRefs (ctl p) ≡ env ++ framesRefs k →
      install (snoc h (nat zero)) ps i (rv (freshRef h gω) env k) ≡ just t → WF t
    freshUnit env k ceq eI = grow-nat zero c cLoc hLoc bLoc eI
      where
      c = rv (freshRef h gω) env k
      cLoc = λ q →
        trans (cong (ext (nH ≡ᵇ q) +_) (sym (cong (count q) ceq)))
              (+-comm (ext (nH ≡ᵇ q)) (count q (ctlRefs (ctl p))))
      hLoc = λ q →
        trans (has-nong1 q (freshRef h gω) (env ++ framesRefs k) refl)
              (sym (cong (hasG1 q) ceq))
      bLoc = bcons (fresh-< nH) (monoS (subst (Bound nH) ceq bHere))

    onTm : ∀ {n} (tm : GTm n) env k →
      ctl p ≡ ev tm env k →
      evalTm h ps i tm env k ≡ just t → WF t
    onTm (gapp f a) env k eqp e′ =
      push (ev f env (ar a ∷ k)) (sym (cong ctlRefs eqp)) e′
    onTm (gsu e0) env k eqp e′ =
      push (ev e0 env (su ∷ k)) (sym (cong ctlRefs eqp)) e′
    onTm (gmatch e0 z s) env k eqp e′ =
      push (ev e0 env (mt e0 z s ∷ k)) (sym (cong ctlRefs eqp)) e′
    onTm (gtyp _) env k eqp e′ = freshUnit env k (cong ctlRefs eqp) e′
    onTm (gpi _ _ _) env k eqp e′ = freshUnit env k (cong ctlRefs eqp) e′
    onTm gze env k eqp e′ = freshUnit env k (cong ctlRefs eqp) e′
    onTm {n} (glam cG ty b) env k eqp e′ =
      cloGo (not-true (anyG1 env) (proj₁ unpacked)) (proj₂ unpacked)
      where
      unpacked = pass-ok (not (anyG1 env))
                   (install (snoc h (clo env (n , glam cG ty b))) ps i
                     (rv (freshRef h gω) env k))
                   e′
      cloGo : anyG1 env ≡ false →
        install (snoc h (clo env (n , glam cG ty b))) ps i
          (rv (freshRef h gω) env k) ≡ just t → WF t
      cloGo ngE eI = landed (setProc ps i c) eI refl
        where
        c = rv (freshRef h gω) env k
        h2 = snoc h (clo env (n , glam cG ty b))
        tm = n , glam cG ty b
        ceq = cong ctlRefs eqp
        cLoc = λ q →
          trans (cong (ext (nH ≡ᵇ q) +_) (sym (cong (count q) ceq)))
                (+-comm (ext (nH ≡ᵇ q)) (count q (ctlRefs (ctl p))))
        hLoc = λ q →
          trans (has-nong1 q (freshRef h gω) (env ++ framesRefs k) refl)
                (sym (cong (hasG1 q) ceq))
        bLoc = bcons (fresh-< nH) (monoS (subst (Bound nH) ceq bHere))
        landed : (m : Maybe (List Proc)) → mapSys h2 m ≡ just t → setProc ps i c ≡ m → WF t
        landed nothing () _
        landed (just ps2) eqj es = subst WF (just-inj eqj) got
          where
          rq = set-refsPs i ps c ps2 es
          extra = λ q → count q env + ext (nH ≡ᵇ q)
          ee = λ q → trans (cong (count q) (edge-clo h env tm)) (count-++ q (edgeRefs h) env)
          he = λ q →
            trans (cong (hasG1 q) (edge-clo h env tm))
            (trans (has-++ q (edgeRefs h) env)
            (trans (cong (hasG1 q (edgeRefs h) ∨_) (any-has q env ngE))
                   (∨-falseʳ (hasG1 q (edgeRefs h)))))
          cq = λ q → count-shift q h h2 ps ps2 (count q env) (ext (nH ≡ᵇ q))
                 (ee q)
                 (lift-plus q i ps p c ps2 (ext (nH ≡ᵇ q)) lk es (cLoc q))
                 (cong (count q) rq)
          hq = λ q → has-stable q h h2 ps ps2 (he q)
                 (lift-has q i ps p c ps2 lk es (hLoc q))
                 (cong (hasG1 q) rq)
          zx = λ q hf → body q (split-ctl i ps p lk) hf
            where
            body : ∀ q → SplitCtl ps p → hasG1 q (refsOf (sys h ps)) ≡ true → extra q ≡ 0
            body q (spl L R eqC) hf =
              let shape = trans (cong (λ cs → (edgeRefs h ++ cs) ++ refsPs ps) eqC)
                                (cong (λ m → (edgeRefs h ++ (L ++ m)) ++ refsPs ps)
                                      (cong (_++ R) ceq))
                  flat = trans shape (regroup (edgeRefs h) L env (framesRefs k) R (refsPs ps))
                  zN = sub-miss q env (edgeRefs h ++ L)
                         (framesRefs k ++ (R ++ refsPs ps)) ngE
                         (subst Grade1Unique flat uqF)
                         (subst (λ xs → hasG1 q xs ≡ true) flat hf)
              in sum0 (count q env) (ext (nH ≡ᵇ q)) zN
                   (fresh-zero q nH (refsOf (sys h ps)) bdF hf)
          bEnv = proj₁ (bound-split env (framesRefs k) (subst (Bound nH) ceq bHere))
          bNew = close-bound h2 ps2 (suc nH)
                   (length-snoc h (cell (clo env tm) live))
                   (subst (Bound (suc nH)) (sym (edge-clo h env tm))
                      (bound-++ (monoS bEdge) (monoS bEnv)))
                   (set-ctl-bound i ps p c ps2 lk es (monoS bCtl) bLoc)
                   (monoS (subst (Bound nH) (sym rq) bRs))
          got = grow-sys {h} {ps} h2 ps2 extra wf bNew cq hq zx
    onTm (gvar x) env k eqp e′ = varGo (lookup env (toℕ x)) e′ refl
      where
      ix = toℕ x
      ceq = cong ctlRefs eqp
      varGo : (m : Maybe Ref) → useVar h ps i env k ix m ≡ just t →
              lookup env ix ≡ m → WF t
      varGo nothing () _
      varGo (just r) eV lr = fromS (spend (refKept r)) refl eV
        where
          movePtr : ∀ r′ → obj r′ ≡ obj r → checked r′ ≡ checked r →
                   pass (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1)
                        (install (snoc h (nat zero)) ps i
                          (rv r′ (repl ix (freshRef h g0) env) k)) ≡ just t →
                   WF t
          movePtr r′ eo ec eP =
            grow-nat zero c cLoc hLoc bLoc
              (proj₂ (pass-ok (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1)
                              (install (snoc h (nat zero)) ps i c) eP))
            where
            c = rv r′ (repl ix (freshRef h g0) env) k
            ph = freshRef h g0
            cLoc = λ q →
              trans (move-count q ix env r r′ ph (framesRefs k) lr eo)
                    (cong (_+ ext (nH ≡ᵇ q)) (sym (cong (count q) ceq)))
            hLoc = λ q →
              trans (move-has q ix env r r′ ph (framesRefs k) lr eo ec refl)
                    (sym (cong (hasG1 q) ceq))
            bPair = bound-split env (framesRefs k) (subst (Bound nH) ceq bHere)
            bRepl = bound-repl-< ix env ph r (monoS (proj₁ bPair)) lr (fresh-< nH)
            bLoc = bcons (≤-step (subst (λ o → o < nH) (sym eo)
                              (bound-lookup env ix r (proj₁ bPair) lr)))
                     (bound-++ bRepl (monoS (proj₂ bPair)))
          aliasPtr : ∀ r′ → obj r′ ≡ obj r → checked r′ ≡ checked r →
                     isG1 (checked r′) ≡ false →
                     install h ps i (rv r′ (repl ix r′ env) k) ≡ just t → WF t
          aliasPtr r′ eo ec eb eP =
            alias-focus c (λ q → ext (obj r′ ≡ᵇ q)) cLoc hLoc zx bLoc eP
            where
            c = rv r′ (repl ix r′ env) k
            cLoc = λ q →
              trans (cong (ext (obj r′ ≡ᵇ q) +_)
                      (trans (repl-tail-count q ix env r′ r (framesRefs k) lr eo)
                             (sym (cong (count q) ceq))))
                    (+-comm (ext (obj r′ ≡ᵇ q)) (count q (ctlRefs (ctl p))))
            hLoc = λ q →
              trans (has-nong1 q r′ (repl ix r′ env ++ framesRefs k) eb)
              (trans (repl-tail-has q ix env r′ r (framesRefs k) lr eo ec)
                     (sym (cong (hasG1 q) ceq)))
            bPair = bound-split env (framesRefs k) (subst (Bound nH) ceq bHere)
            bLoc = bcons (subst (λ o → o < nH) (sym eo)
                            (bound-lookup env ix r (proj₁ bPair) lr))
                     (bound-++ (bound-repl ix env r′ r (proj₁ bPair) lr eo) (proj₂ bPair))
            ngR = trans (sym (cong isG1 ec)) eb
            zx = λ q hf → body q (split-ctl i ps p lk) hf
              where
              body : ∀ q → SplitCtl ps p → hasG1 q (refsOf (sys h ps)) ≡ true →
                     ext (obj r′ ≡ᵇ q) ≡ 0
              body q (spl L R eqC) hf =
                let shape = trans (cong (λ cs → (edgeRefs h ++ cs) ++ refsPs ps) eqC)
                                  (cong (λ m → (edgeRefs h ++ (L ++ m)) ++ refsPs ps)
                                        (cong (_++ R) ceq))
                    flat = trans shape (regroup (edgeRefs h) L env (framesRefs k) R (refsPs ps))
                in trans (cong (λ o → ext (o ≡ᵇ q)) eo)
                     (nong1-ext q (edgeRefs h ++ L) env
                        (framesRefs k ++ (R ++ refsPs ps)) ix r lr ngR
                        (subst Grade1Unique flat uqF)
                        (subst (λ xs → hasG1 q xs ≡ true) flat hf))
          fromS : (s : Maybe (Spent (checked r))) →
                 spend (refKept r) ≡ s →
                 useVar h ps i env k ix (just r) ≡ just t → WF t
          fromS nothing eq eU rewrite eq with eU
          ... | ()
          fromS (just (spentK ρ κ)) eq eU rewrite eq with payloadAt h (obj r)
          fromS (just (spentK ρ κ)) eq eU | nothing with eU
          fromS (just (spentK ρ κ)) eq eU | nothing | ()
          fromS (just (spentK ρ κ)) eq eU | just (nat nv) = grow-nat nv c cLoc hLoc bLoc eU
            where
            r′ = ref (obj r) (checked r) ρ κ
            sm : spendRef r ≡ just r′
            sm rewrite eq = refl
            eo = spendRef-obj r r′ sm
            ec = spendRef-checked r r′ sm
            c = rv (freshRef h gω) (repl ix r′ env) k
            cLoc = λ q →
              trans (cong (ext (nH ≡ᵇ q) +_)
                      (trans (repl-tail-count q ix env r′ r (framesRefs k) lr eo)
                             (sym (cong (count q) ceq))))
                    (+-comm (ext (nH ≡ᵇ q)) (count q (ctlRefs (ctl p))))
            hLoc = λ q →
              trans (has-nong1 q (freshRef h gω) (repl ix r′ env ++ framesRefs k) refl)
              (trans (repl-tail-has q ix env r′ r (framesRefs k) lr eo ec)
                     (sym (cong (hasG1 q) ceq)))
            bPair = bound-split env (framesRefs k) (subst (Bound nH) ceq bHere)
            bLoc = bcons (fresh-< nH)
                     (monoS (bound-++ (bound-repl ix env r′ r (proj₁ bPair) lr eo) (proj₂ bPair)))
          fromS (just (spentK ρ κ)) eq eU | just (suc↑ _) with isG1 (checked r) in g1eq
          fromS (just (spentK ρ κ)) eq eU | just (suc↑ _) | true = movePtr r′ eo ec eU
            where
            r′ = ref (obj r) (checked r) ρ κ
            sm : spendRef r ≡ just r′
            sm rewrite eq = refl
            eo = spendRef-obj r r′ sm
            ec = spendRef-checked r r′ sm
          fromS (just (spentK ρ κ)) eq eU | just (suc↑ _) | false = aliasPtr (ref (obj r) (checked r) ρ κ) eo ec g1eq eU
            where
            r′ = ref (obj r) (checked r) ρ κ
            sm : spendRef r ≡ just r′
            sm rewrite eq = refl
            eo = spendRef-obj r r′ sm
            ec = spendRef-checked r r′ sm
          fromS (just (spentK ρ κ)) eq eU | just (clo _ _) with isG1 (checked r) in g1eq
          fromS (just (spentK ρ κ)) eq eU | just (clo _ _) | true = movePtr r′ eo ec eU
            where
            r′ = ref (obj r) (checked r) ρ κ
            sm : spendRef r ≡ just r′
            sm rewrite eq = refl
            eo = spendRef-obj r r′ sm
            ec = spendRef-checked r r′ sm
          fromS (just (spentK ρ κ)) eq eU | just (clo _ _) | false = aliasPtr (ref (obj r) (checked r) ρ κ) eo ec g1eq eU
            where
            r′ = ref (obj r) (checked r) ρ κ
            sm : spendRef r ≡ just r′
            sm rewrite eq = refl
            eo = spendRef-obj r r′ sm
            ec = spendRef-checked r r′ sm

    rotAr : ∀ r env {n} (a : GTm n) k →
      ctl p ≡ rv r env (ar a ∷ k) →
      install h ps i (ev a env (fn r ∷ k)) ≡ just t → WF t
    rotAr r env a k eqp e′ = xfer-ctl c cq hq bc e′
      where
      c = ev a env (fn r ∷ k)
      fr = framesRefs k
      ceq = cong ctlRefs eqp
      cq = λ q → trans (sym (rot-count q r env fr)) (sym (cong (count q) ceq))
      hq = λ q → trans (sym (rot-has q r env fr)) (sym (cong (hasG1 q) ceq))
      bc = rot-bound r env fr (subst (Bound nH) ceq bHere)

    sucGo : ∀ r env k →
      ctl p ≡ rv r env (su ∷ k) →
      install (snoc h (suc↑ r)) ps i (rv (freshRef h gω) env k) ≡ just t → WF t
    sucGo r env k eqp eI = landed (setProc ps i c) eI refl
      where
      c = rv (freshRef h gω) env k
      h2 = snoc h (suc↑ r)
      fr = framesRefs k
      ceq = cong ctlRefs eqp
      cLoc = λ q →
        trans (addXB (ext (nH ≡ᵇ q)) (count q (env ++ fr)) (ext (obj r ≡ᵇ q)))
              (cong (_+ ext (nH ≡ᵇ q)) (sym (cong (count q) ceq)))
      bShape = subst (Bound nH) ceq bHere
      bLoc = bcons (fresh-< nH) (monoS (bound-uncons bShape))
      landed : (m : Maybe (List Proc)) → mapSys h2 m ≡ just t → setProc ps i c ≡ m → WF t
      landed nothing () _
      landed (just ps2) eqj es = subst WF (just-inj eqj) (use (set-both i ps p c ps2 lk es))
        where
        rq = set-refsPs i ps c ps2 es
        use : Both ps ps2 p c → WF (sys h2 ps2)
        use (both L R eOld eNew rEq) = grow-sys {h} {ps} h2 ps2 (λ q → ext (nH ≡ᵇ q)) wf bNew cq hq
          (λ q hf → fresh-zero q nH (refsOf (sys h ps)) bdF hf)
          where
          bit = λ q → (obj r ≡ᵇ q) ∧ isG1 (checked r)
          ee = λ q → trans (cong (count q) (edge-suc h r)) (count-snoc q (edgeRefs h) r)
          he = λ q → trans (cong (hasG1 q) (edge-suc h r)) (has-snoc q (edgeRefs h) r)
          hNew = λ q → has-nong1 q (freshRef h gω) (env ++ fr) refl
          hOld = λ q → cong (hasG1 q) ceq
          cq = λ q →
            let X = ext (obj r ≡ᵇ q)
                B = ext (nH ≡ᵇ q)
                E = count q (edgeRefs h)
                C = count q (ctlRefsPs ps)
                C′ = count q (ctlRefsPs ps2)
                Rq = count q (refsPs ps)
            in trans (refs-count q h2 ps2)
               (trans (cong (λ e0 → (e0 + C′) + count q (refsPs ps2)) (ee q))
               (trans (cong (λ r0 → ((E + X) + C′) + r0) (cong (count q) rq))
               (trans (gain-fresh E X C C′ Rq B
                        (lift-swap q i ps p c ps2 X B lk es (cLoc q)))
                      (cong (_+ B) (sym (refs-count q h ps))))))
          hq = λ q →
            trans (refs-has q h2 ps2)
            (trans (move-has5 (hasG1 q (edgeRefs h)) (hasG1 q (edgeRefs h2)) (bit q)
                     (hasG1 q L) (hasG1 q (env ++ fr)) (hasG1 q (ctlRefs c))
                     (hasG1 q R)
                     (hasG1 q (ctlRefsPs ps)) (hasG1 q (ctlRefsPs ps2))
                     (hasG1 q (refsPs ps)) (hasG1 q (refsPs ps2))
                     (he q)
                     (trans (cong (hasG1 q) eNew) (has3 q L (ctlRefs c) R))
                     (hNew q)
                     (trans (trans (cong (hasG1 q) eOld) (has3 q L (ctlRefs (ctl p)) R))
                            (cong (λ z → hasG1 q L ∨ (z ∨ hasG1 q R)) (hOld q)))
                     (cong (hasG1 q) rEq))
                   (sym (refs-has q h ps)))
          bNew = close-bound h2 ps2 (suc nH) (length-snoc h (cell (suc↑ r) live))
                   (subst (Bound (suc nH)) (sym (edge-suc h r))
                      (bound-++ (monoS bEdge) (bcons (≤-step (head-< bShape)) bnil)))
                   (set-ctl-bound i ps p c ps2 lk es (monoS bCtl) bLoc)
                   (monoS (subst (Bound nH) (sym rq) bRs))

    betaGo : ∀ ra rf env k →
      ctl p ≡ rv ra env (fn rf ∷ k) →
      beta h ps i ra rf env k ≡ just t → WF t
    betaGo ra rf env k eqp eB = opened (payloadAt h (obj rf)) eB refl
      where
      fr = framesRefs k
      ceq = cong ctlRefs eqp
      opened : (v : Maybe Val) → beta h ps i ra rf env k ≡ just t →
               payloadAt h (obj rf) ≡ v → WF t
      opened nothing eP pv rewrite pv = stuck-just eP
      opened (just (nat _)) eP pv rewrite pv = stuck-just eP
      opened (just (suc↑ _)) eP pv rewrite pv = stuck-just eP
      opened (just (clo envC (nb , gvar _))) eP pv rewrite pv = stuck-just eP
      opened (just (clo envC (nb , gtyp _))) eP pv rewrite pv = stuck-just eP
      opened (just (clo envC (nb , gpi _ _ _))) eP pv rewrite pv = stuck-just eP
      opened (just (clo envC (nb , gapp _ _))) eP pv rewrite pv = stuck-just eP
      opened (just (clo envC (nb , gze))) eP pv rewrite pv = stuck-just eP
      opened (just (clo envC (nb , gsu _))) eP pv rewrite pv = stuck-just eP
      opened (just (clo envC (nb , gmatch _ _ _))) eP pv rewrite pv = stuck-just eP
      opened (just (clo envC (nb , glam cG ty body))) eP pv rewrite pv =
        let inner = install h ps i (ev body (regrade ra cG ∷ envC) (frameBd env ∷ k))
            outer = pass-ok (not (badG1 cG (obj ra) (refsOf (sys h ps))))
                            (pass (not (anyG1 envC)) inner) eP
            inn = pass-ok (not (anyG1 envC)) inner (proj₂ outer)
        in betaDone envC nb cG ty body pv
             (not-true (badG1 cG (obj ra) (refsOf (sys h ps))) (proj₁ outer))
             (not-true (anyG1 envC) (proj₁ inn))
             (proj₂ inn)
        where
        betaDone : ∀ envC nb cG ty body →
          payloadAt h (obj rf) ≡ just (clo envC (nb , glam cG ty body)) →
          badG1 cG (obj ra) (refsOf (sys h ps)) ≡ false →
          anyG1 envC ≡ false →
          install h ps i (ev body (regrade ra cG ∷ envC) (frameBd env ∷ k)) ≡ just t →
          WF t
        betaDone envC nb cG ty body pv badF ngE eI =
          landed (setProc ps i c2) eI refl
          where
          rg = regrade ra cG
          c2 = ev body (rg ∷ envC) (frameBd env ∷ k)
          landed : (m : Maybe (List Proc)) → mapSys h m ≡ just t → setProc ps i c2 ≡ m → WF t
          landed nothing () _
          landed (just ps2) eqj es = subst WF (just-inj eqj) (bNew , uNew)
            where
            rq = set-refsPs i ps c2 ps2 es
            cLoc = λ q →
              trans (beta-local q ra rg rf envC env fr refl)
                    (cong (_+ count q envC) (sym (cong (count q) ceq)))
            cEq = λ q →
              let E = count q (edgeRefs h)
                  C = count q (ctlRefsPs ps)
                  C′ = count q (ctlRefsPs ps2)
                  Rq = count q (refsPs ps)
                  F = ext (obj rf ≡ᵇ q)
                  N = count q envC
              in trans (cong (_+ F) (refs-count q h ps2))
                 (trans (cong (λ r0 → ((E + C′) + r0) + F) (cong (count q) rq))
                 (trans (shift-count E C C′ Rq F N
                          (lift-swap q i ps p c2 ps2 F N lk es (cLoc q)))
                        (cong (_+ N) (sym (refs-count q h ps)))))
            bCtlNew = edgeB (edge-at h (obj rf) (clo envC (nb , glam cG ty body)) pv)
              where
              edgeB : EdgeAt h (obj rf) (clo envC (nb , glam cG ty body)) →
                      Bound nH (ctlRefs c2)
              edgeB (eat L R e1 _) =
                let bShape = subst (Bound nH) ceq bHere
                    bRest = bound-uncons bShape
                    bEnv = proj₁ (bound-split env (rf ∷ fr) bRest)
                    bFr = bound-uncons (proj₂ (bound-split env (rf ∷ fr) bRest))
                    bEd = subst (Bound nH) e1 bEdge
                    bEC = proj₁ (bound-split envC R (proj₂ (bound-split L (envC ++ R) bEd)))
                in bcons (head-< bShape) (bound-++ bEC (bound-++ bEnv bFr))
            bNew = close-bound h ps2 nH refl bEdge
                     (set-ctl-bound i ps p c2 ps2 lk es bCtl bCtlNew)
                     (subst (Bound nH) (sym rq) bRs)
            uNew : Grade1Unique (refsOf (sys h ps2))
            uNew i0 hn = gradeSplit (isG1 cG) refl
              where
              missGrade : isG1 cG ≡ false →
                          ((obj rg ≡ᵇ i0) ∧ isG1 (checked rg)) ≡ false
              missGrade geb rewrite geb = ∧-falseʳ (obj rg ≡ᵇ i0)
              missObj : (obj ra ≡ᵇ i0) ≡ false →
                        ((obj rg ≡ᵇ i0) ∧ isG1 (checked rg)) ≡ false
              missObj eob rewrite eob = refl
              byMiss : ((obj rg ≡ᵇ i0) ∧ isG1 (checked rg)) ≡ false →
                       hasG1 i0 (refsOf (sys h ps2)) ≡ true →
                       count i0 (refsOf (sys h ps2)) ≡ 1
              byMiss bitF hn′ =
                from-sum (count i0 (refsOf (sys h ps2))) (ext (obj rf ≡ᵇ i0)) eq1
                  (has-count i0 (refsOf (sys h ps2)) hn′)
                where
                imp : hasG1 i0 (ctlRefs c2) ≡ true → hasG1 i0 (ctlRefs (ctl p)) ≡ true
                imp hnC =
                  subst (λ b → b ≡ true) (sym (cong (hasG1 i0) ceq))
                    (caller-has i0 ra rf env fr
                      (new-is-tail i0 rg envC (env ++ fr) bitF (any-has i0 envC ngE) hnC))
                ho = has-imp-heap i0 h h ps ps2 (λ z → z)
                       (λ hnC → lift-has-imp i0 i ps p c2 ps2 lk es imp hnC)
                       (cong (hasG1 i0) rq) hn′
                cntI = uqF i0 ho
                zN = envZero (edge-at h (obj rf) (clo envC (nb , glam cG ty body)) pv)
                  where
                  envZero : EdgeAt h (obj rf) (clo envC (nb , glam cG ty body)) →
                            count i0 envC ≡ 0
                  envZero (eat L R e1 _) =
                    let flat = trans (cong (λ e0 → (e0 ++ ctlRefsPs ps) ++ refsPs ps) e1)
                                      (clo-seg L envC R (ctlRefsPs ps) (refsPs ps))
                    in sub-miss i0 envC L ((R ++ ctlRefsPs ps) ++ refsPs ps) ngE
                         (subst Grade1Unique flat uqF)
                         (subst (λ xs → hasG1 i0 xs ≡ true) flat ho)
                eq1 = trans (cEq i0)
                        (trans (cong (count i0 (refsOf (sys h ps)) +_) zN)
                        (trans (+-identityʳ (count i0 (refsOf (sys h ps)))) cntI))
              byGate : (obj ra ≡ᵇ i0) ≡ true → isG1 cG ≡ true →
                       hasG1 i0 (refsOf (sys h ps2)) ≡ true →
                       count i0 (refsOf (sys h ps2)) ≡ 1
              byGate eob geb hn′ =
                from-sum (count i0 (refsOf (sys h ps2))) (ext (obj rf ≡ᵇ i0)) eq1
                  (has-count i0 (refsOf (sys h ps2)) hn′)
                where
                cntRa = ≡ᵇ-sound (count (obj ra) (refsOf (sys h ps))) 1
                          (bad-ok cG (count (obj ra) (refsOf (sys h ps))) badF geb)
                cntI = subst (λ o → count o (refsOf (sys h ps)) ≡ 1)
                         (≡ᵇ-sound (obj ra) i0 eob) cntRa
                oneShape = subst (λ n0 → n0 ≤ count i0 (ra ∷ env ++ (rf ∷ fr)))
                             (cong ext eob)
                             (m≤m+k (ext (obj ra ≡ᵇ i0))
                                    (count i0 (env ++ (rf ∷ fr))))
                oneHere = subst (λ n0 → suc zero ≤ n0) (sym (cong (count i0) ceq)) oneShape
                zN = squeezed (split-ctl i ps p lk)
                  where
                  edged : EdgeAt h (obj rf) (clo envC (nb , glam cG ty body)) →
                          count i0 (edgeRefs h) ≡ 0 → count i0 envC ≡ 0
                  edged (eat L R e1 _) zE =
                    sub-zero i0 L envC R (subst (λ xs → count i0 xs ≡ 0) e1 zE)
                  squeezed : SplitCtl ps p → count i0 envC ≡ 0
                  squeezed (spl L R eqC) =
                    let onePs = ≤-trans oneHere
                                  (subst (λ n0 → count i0 (ctlRefs (ctl p)) ≤ n0)
                                     (sym (cong (count i0) eqC))
                                     (count-ge-seg i0 L (ctlRefs (ctl p)) R))
                        eqFull = trans (sym (refs-count i0 h ps)) cntI
                        zE = proj₁ (squeeze3 (count i0 (edgeRefs h))
                                       (count i0 (ctlRefsPs ps))
                                       (count i0 (refsPs ps)) eqFull onePs)
                    in edged (edge-at h (obj rf) (clo envC (nb , glam cG ty body)) pv) zE
                eq1 = trans (cEq i0)
                        (trans (cong (count i0 (refsOf (sys h ps)) +_) zN)
                        (trans (+-identityʳ (count i0 (refsOf (sys h ps)))) cntI))
              gradeSplit : (b : Bool) → isG1 cG ≡ b → count i0 (refsOf (sys h ps2)) ≡ 1
              gradeSplit false geb = byMiss (missGrade geb) hn
              gradeSplit true geb = objSplit (obj ra ≡ᵇ i0) refl
                where
                objSplit : (b : Bool) → (obj ra ≡ᵇ i0) ≡ b → count i0 (refsOf (sys h ps2)) ≡ 1
                objSplit true eob = byGate eob geb hn
                objSplit false eob = byMiss (missObj eob) hn

    matchGo : ∀ r env {n} (e0 : GTm n) (z : GTm n) (s : GTm (suc n)) k →
      ctl p ≡ rv r env (mt e0 z s ∷ k) →
      onMatch h ps i r env e0 z s k (payloadAt h (obj r)) ≡ just t → WF t
    matchGo r env e0 z s k eqp eM = onV (payloadAt h (obj r)) eM refl
      where
      fr = framesRefs k
      ceq = cong ctlRefs eqp
      g = predComp env e0
      onV : (v : Maybe Val) →
            onMatch h ps i r env e0 z s k (payloadAt h (obj r)) ≡ just t →
            payloadAt h (obj r) ≡ v → WF t
      onV nothing eP pv rewrite pv = stuck-just eP
      onV (just (nat (suc _))) eP pv rewrite pv = stuck-just eP
      onV (just (clo _ _)) eP pv rewrite pv = stuck-just eP
      onV (just (nat zero)) eP pv rewrite pv = thin-ctl c le hi bc eP
        where
        c = ev z env k
        le = λ q → subst (λ n0 → count q (ctlRefs c) ≤ n0) (sym (cong (count q) ceq))
                      (drop-head-le q r (env ++ fr))
        hi = λ q hn → subst (λ b → b ≡ true) (sym (cong (hasG1 q) ceq))
                       (drop-head-has q r (env ++ fr) hn)
        bc = bound-uncons (subst (Bound nH) ceq bHere)
      onV (just (suc↑ pred)) eP pv rewrite pv =
        let inner = install (setPayload h (obj r) (nat zero)) ps i
                      (ev s (regrade pred g ∷ env) k)
            outer = pass-ok (not (badG1 g (obj pred) (refsOf (sys h ps)))) inner eP
        in sucDone pred pv (not-true (badG1 g (obj pred) (refsOf (sys h ps))) (proj₁ outer))
             (proj₂ outer)
        where
        sucDone : ∀ pred →
          payloadAt h (obj r) ≡ just (suc↑ pred) →
          badG1 g (obj pred) (refsOf (sys h ps)) ≡ false →
          install (setPayload h (obj r) (nat zero)) ps i
            (ev s (regrade pred g ∷ env) k) ≡ just t →
          WF t
        sucDone pred pv badF eI = landed (setProc ps i c2) eI refl
          where
          rg = regrade pred g
          c2 = ev s (rg ∷ env) k
          h2 = setPayload h (obj r) (nat zero)
          landed : (m : Maybe (List Proc)) → mapSys h2 m ≡ just t →
                   setProc ps i c2 ≡ m → WF t
          landed nothing () _
          landed (just ps2) eqj es = subst WF (just-inj eqj) (use (edge-at h (obj r) (suc↑ pred) pv))
            where
            rq = set-refsPs i ps c2 ps2 es
            use : EdgeAt h (obj r) (suc↑ pred) → WF (sys h2 ps2)
            use (eat L R e1 e2) = bNew , uNew
              where
              cE = λ q →
                trans (cong (_+ ext (obj pred ≡ᵇ q)) (cong (count q) e2))
                      (sym (trans (cong (count q) e1) (count-insert q L pred R)))
              cLoc = λ q →
                trans (addXB (ext (obj pred ≡ᵇ q)) (count q (env ++ fr)) (ext (obj r ≡ᵇ q)))
                      (cong (_+ ext (obj pred ≡ᵇ q)) (sym (cong (count q) ceq)))
              cEq = λ q →
                let F = ext (obj r ≡ᵇ q)
                    X = ext (obj pred ≡ᵇ q)
                    E = count q (edgeRefs h)
                    E′ = count q (edgeRefs h2)
                    C = count q (ctlRefsPs ps)
                    C′ = count q (ctlRefsPs ps2)
                    Rq = count q (refsPs ps)
                in trans (cong (_+ F) (refs-count q h2 ps2))
                   (trans (cong (λ r0 → ((E′ + C′) + r0) + F) (cong (count q) rq))
                   (trans (drop-move E E′ C C′ Rq X F (cE q)
                            (lift-swap q i ps p c2 ps2 F X lk es (cLoc q)))
                          (sym (refs-count q h ps))))
              bEd = subst (Bound nH) e1 bEdge
              bL = proj₁ (bound-split L (pred ∷ R) bEd)
              bMid = proj₂ (bound-split L (pred ∷ R) bEd)
              bNewE = subst (Bound nH) (sym e2) (bound-++ bL (bound-uncons bMid))
              bNewC = bcons (head-< bMid) (bound-uncons (subst (Bound nH) ceq bHere))
              bNew = close-bound h2 ps2 nH (length-set h (obj r) (nat zero)) bNewE
                       (set-ctl-bound i ps p c2 ps2 lk es bCtl bNewC)
                       (subst (Bound nH) (sym rq) bRs)
              uNew : Grade1Unique (refsOf (sys h2 ps2))
              uNew i0 hn = gradeSplit (isG1 g) refl
                where
                byMiss : hasG1 i0 (ctlRefs c2) ≡ hasG1 i0 (env ++ fr) →
                         hasG1 i0 (refsOf (sys h2 ps2)) ≡ true →
                         count i0 (refsOf (sys h2 ps2)) ≡ 1
                byMiss hEq hn′ =
                  sym (≤-antisym (has-count i0 (refsOf (sys h2 ps2)) hn′)
                        (≤-subst (le-from-plus (cEq i0)) (uqF i0 ho)))
                  where
                  imp : hasG1 i0 (ctlRefs c2) ≡ true → hasG1 i0 (ctlRefs (ctl p)) ≡ true
                  imp hnC =
                    subst (λ b → b ≡ true) (sym (cong (hasG1 i0) ceq))
                      (drop-head-has i0 r (env ++ fr)
                        (subst (λ b → b ≡ true) hEq hnC))
                  he : hasG1 i0 (edgeRefs h2) ≡ true → hasG1 i0 (edgeRefs h) ≡ true
                  he hnE =
                    subst (λ b → b ≡ true) (sym (cong (hasG1 i0) e1))
                      (insert-has i0 L pred R
                        (subst (λ b → b ≡ true) (cong (hasG1 i0) e2) hnE))
                  ho = has-imp-heap i0 h h2 ps ps2 he
                         (λ hnC → lift-has-imp i0 i ps p c2 ps2 lk es imp hnC)
                         (cong (hasG1 i0) rq) hn′
                byGate : (obj pred ≡ᵇ i0) ≡ true → isG1 g ≡ true →
                         hasG1 i0 (refsOf (sys h2 ps2)) ≡ true →
                         count i0 (refsOf (sys h2 ps2)) ≡ 1
                byGate eob geb hn′ =
                  from-sum (count i0 (refsOf (sys h2 ps2))) (ext (obj r ≡ᵇ i0))
                    (trans (cEq i0) cntI)
                    (has-count i0 (refsOf (sys h2 ps2)) hn′)
                  where
                  cntPred = ≡ᵇ-sound (count (obj pred) (refsOf (sys h ps))) 1
                              (bad-ok g (count (obj pred) (refsOf (sys h ps))) badF geb)
                  cntI = subst (λ o → count o (refsOf (sys h ps)) ≡ 1)
                           (≡ᵇ-sound (obj pred) i0 eob) cntPred
                gradeSplit : (b : Bool) → isG1 g ≡ b → count i0 (refsOf (sys h2 ps2)) ≡ 1
                gradeSplit false geb = byMiss (has-nong1 i0 rg (env ++ fr) geb) hn
                gradeSplit true geb = objSplit (obj pred ≡ᵇ i0) refl
                  where
                  objSplit : (b : Bool) → (obj pred ≡ᵇ i0) ≡ b →
                             count i0 (refsOf (sys h2 ps2)) ≡ 1
                  objSplit false eob = byMiss (has-miss i0 rg (env ++ fr) eob) hn
                  objSplit true eob = byGate eob geb hn

    popGo : ∀ r env env0 k →
      ctl p ≡ rv r env (frameBd env0 ∷ k) →
      install h ps i (rv r env0 k) ≡ just t → WF t
    popGo r env env0 k eqp e′ = thin-ctl c le hi bc e′
      where
      c = rv r env0 k
      ceq = cong ctlRefs eqp
      ys = env0 ++ framesRefs k
      le = λ q → subst (λ n0 → count q (ctlRefs c) ≤ n0) (sym (cong (count q) ceq))
                    (drop-mid-le q r env ys)
      hi = λ q hn → subst (λ b → b ≡ true) (sym (cong (hasG1 q) ceq))
                     (drop-mid-has q r env ys hn)
      bc = drop-mid-bound r env ys (subst (Bound nH) ceq bHere)

    onRet : ∀ r env k → ctl p ≡ rv r env k → evalRet h ps i r env k ≡ just t → WF t
    onRet r env [] eqp ()
    onRet r env (ar a ∷ k) eqp e′ = rotAr r env a k eqp e′
    onRet r env (fn rf ∷ k) eqp e′ = betaGo r rf env k eqp e′
    onRet r env (su ∷ k) eqp e′ = sucGo r env k eqp e′
    onRet r env (mt e0 z s ∷ k) eqp e′ = matchGo r env e0 z s k eqp e′
    onRet r env (frameBd env0 ∷ k) eqp e′ = popGo r env env0 k eqp e′
    onRet r env (saved _ ∷ k) eqp e′ with e′
    ... | ()

    on : (c : Ctl) → evalHere h ps i c ≡ just t → ctl p ≡ c → WF t
    on idle e′ _ with e′
    ... | ()
    on (ev tm env k) e′ eqp = onTm tm env k eqp e′
    on (rv r env k) e′ eqp = onRet r env k eqp e′
    on (pr _) e′ _ with e′
    ... | ()

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
  go (sys h ps) (step-eval {i = i} eq) wf =
    eval-wf h ps i t eq wf
  go s step-collect wf = collect-wf s wf

