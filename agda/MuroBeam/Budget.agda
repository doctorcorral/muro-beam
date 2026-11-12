------------------------------------------------------------------------
-- Adequacy of run derefs for grade 1.
--
-- `NoEscape` forbids a λ under a g1 binder, which is the capture this
-- machine refuses. Along every `Step*` from `lower` of a match-free
-- term, each environment ref whose *checked* grade is still g1 has
-- either residual g1 and exactly one computational occurrence ahead,
-- or residual g0 and none. A g1 binder's static count is 1, so a run
-- deref of it is the one use the checker counted, and `spendRef` does
-- not refuse it. At a `bd` pop the debt is 0, so the residual is g0.
--
-- Finite points above 1 are outside this statement: a `pt (fin 2)`
-- binder may be captured by an ω closure and used more than twice,
-- and that term is still `NoEscape`. An interval does not step down
-- to g0. `gmatch` is outside the trace theorem: the checker takes the
-- heavier branch, and `onMatch` extends the environment under frames
-- that were typed in the unextended one. A moved g1 scrutinee is also
-- rebound by `predComp` from the slot *after* the move, which is a
-- fresh g0. Those limits are recorded in DESIGN.md.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Budget where

open import Data.Bool.Base using (Bool; true; false; not; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _⊔_; _≡ᵇ_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; Σ; ∃; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base as Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_; lookup to vlookup)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (run; spec; Result; fail; _>>=_; _>>_) renaming (ok to okR)
open import Muro.Grade using
  ( Grade; g0; g1; Count; finᶜ; many; Spent; sp; Pair; gp
  ; Uses; GCtx; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch
  ; sat; decide; under; hold; checkCount; checkType
  ; predPair; pcomp; ptype; refuse; typeRefuse
  ; zeros; oneS; charge; addU; maxU; addᶜ; maxᶜ ; gω )

open import MuroBeam.Grade using
  ( Kept; fin-kept; isG1; isG1-sound; isG1-complete; selfKept; spend; spent
  ; isZeroGrade; Kind; Kmove; Kcopy; kind )
open import MuroBeam.Heap using
  ( Obj; cell; Status; live; free; Val; nat; suc↑; clo; Ref; ref
  ; obj; checked; residual; kept; payload; spendRef; repl
  ; spendRef-zero; spendRef-checked; count; childrenBelow )
open import MuroBeam.Lib using
  ( lookup; update; removeAt; +-assoc; +-identityʳ; ≡ᵇ-refl; ≡ᵇ-sound
  ; ∨-false; ≤-refl; ≤-trans ) renaming (lower to lower≤)
open import MuroBeam.Process using
  ( anyG1; Frame; ar; fn; su; mt; bd; saved
  ; Sys; sys; Proc; proc; ctl; roots; inbox; Msg; msg; Ctl; idle; ev; rv; pr
  ; eval1; evalTm; evalRet; useVar; beta; pass; install; freshRef; snoc
  ; regrade; badG1; payloadAt; deref; send; recv; alloc; reuse; poke
  ; refsOf; rootAt; putRoot; putHead; putHeadOf; mapSys
  ; derefAt; derefSpent; post; dropRoot; takeRoot; addMsg; copyTo
  ; dispatch; sendTaken; sendFrom; moveTo; moveToOn; moveRecv; moveOther
  ; recvAt; recvInbox
  ; addRoot; addRootOn; reuseOk; reuseFrom )
open import MuroBeam.Collect using
  ( Step; step-deref; step-send; step-recv; step-alloc; step-reuse
  ; step-eval; step-collect; collect; apply; clean; markVec
  ; filterKeep; filterMsg )
open import MuroBeam.Lower using (lower; Step*; step-done; step-more)
open import MuroBeam.Source using
  ( Checked; term; ok; NoEsc; NoEscape; g1InScope; predG
  ; ne-var; ne-typ; ne-ze; ne-su; ne-app; ne-pi; ne-lam; ne-mat )

open Checked public

------------------------------------------------------------------------
-- Occurrences the CEK still has to perform. Match keeps the heavier
-- branch. A λ counts free uses of the captured env. A Π is erased.
------------------------------------------------------------------------

occ : ∀ {n} → ℕ → GTm n → ℕ
occ i (gvar x) = if toℕ x ≡ᵇ i then suc zero else zero
occ _ (gtyp _) = zero
occ i (glam _ _ b) = occ (suc i) b
occ _ (gpi _ _ _) = zero
occ i (gapp f a) = occ i f + occ i a
occ _ gze = zero
occ i (gsu e) = occ i e
occ i (gmatch e z s) = occ i e + (occ i z ⊔ occ (suc i) s)

debtF : ℕ → List Frame → ℕ
debtF _ [] = zero
debtF i (ar a ∷ k) = occ i a + debtF i k
debtF i (fn _ ∷ k) = debtF i k
debtF i (su ∷ k) = debtF i k
debtF i (mt _ z s ∷ k) = (occ i z ⊔ occ (suc i) s) + debtF i k
debtF _ (bd _ ∷ _) = zero
debtF _ (saved _ ∷ _) = zero

------------------------------------------------------------------------
-- The checker's computational count is `occ`.
------------------------------------------------------------------------

compAt : ∀ {n} → Uses n → Fin n → Count
compAt {suc n} (sp c _ ∷ᵥ _) fzero = c
compAt {suc n} (_ ∷ᵥ us) (fsuc i) = compAt us i

private

  cong₂ : ∀ {A B C : Set} (f : A → B → C) {a a' b b'} →
          a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ _ refl refl = refl

  fail≢ok : ∀ {A : Set} {x : A} {msg : String} → fail msg ≡ okR x → ⊥
  fail≢ok ()

  ok-inj : ∀ {A : Set} {x y : A} → okR x ≡ okR y → x ≡ y
  ok-inj refl = refl

  check-ok : ∀ {A : Set} (b : Bool) (x : A) (msg : String) {y : A} →
             (if b then okR x else fail msg) ≡ okR y → b ≡ true × x ≡ y
  check-ok true x _ refl = refl , refl
  check-ok false _ _ ()

  bind-split : ∀ {A B : Set} (r : Result A) (f : A → Result B) {b : B} →
               (r >>= f) ≡ okR b → Σ A (λ a → r ≡ okR a × f a ≡ okR b)
  bind-split (okR a) f eq = a , refl , eq
  bind-split (fail _) _ ()

  >>-split : ∀ {A B : Set} (r : Result A) (s : Result B) {b : B} →
             (r >> s) ≡ okR b → Σ A (λ a → r ≡ okR a × s ≡ okR b)
  >>-split r s eq = bind-split r (λ _ → s) eq

  hold-both : ∀ c t co ty →
              hold run c t (sp co ty) ≡ okR tt →
              sat c co ≡ true × sat t ty ≡ true
  hold-both c t co ty eq with >>-split (checkCount run c co) (checkType t ty) eq
  ... | _ , cok , tok with check-ok (sat c co) tt (refuse c co) cok
  ... | sc , _ with check-ok (sat t ty) tt (typeRefuse t ty) tok
  ... | st , _ = sc , st

  under-both : ∀ {n} c t co ty (rest out : Uses n) →
               under run c t (sp co ty ∷ᵥ rest) ≡ okR out →
               sat c co ≡ true × rest ≡ out
  under-both c t co ty rest out eq
    with >>-split (hold run c t (sp co ty)) (okR rest) eq
  ... | _ , hok , rok with hold-both c t co ty hok
  ... | sc , _ = sc , ok-inj rok

  under-tail : ∀ {n} c t co ty (rest out : Uses n) →
               under spec c t (sp co ty ∷ᵥ rest) ≡ okR out →
               rest ≡ out
  under-tail c t co ty rest out eq
    with >>-split (checkType t ty) (okR rest) eq
  ... | _ , _ , rok = ok-inj rok

  -- Split the index in a helper. A direct recursive clause does not
  -- reduce `compAt` on the pattern, because that match is not
  -- cubical-compatible. The helper sees a constructed vector.
  comp-add : ∀ {n} (us vs : Uses n) (i : Fin n) →
             compAt (addU us vs) i ≡ addᶜ (compAt us i) (compAt vs i)
  comp-add {zero} []ᵥ []ᵥ ()
  comp-add {suc n} (sp c t ∷ᵥ us) (sp d u ∷ᵥ vs) i = step i
    where
    step : (j : Fin (suc n)) →
           compAt (addU (sp c t ∷ᵥ us) (sp d u ∷ᵥ vs)) j ≡
           addᶜ (compAt (sp c t ∷ᵥ us) j) (compAt (sp d u ∷ᵥ vs) j)
    step fzero = refl
    step (fsuc j) = comp-add us vs j

  comp-max : ∀ {n} (us vs : Uses n) (i : Fin n) →
             compAt (maxU us vs) i ≡ maxᶜ (compAt us i) (compAt vs i)
  comp-max {zero} []ᵥ []ᵥ ()
  comp-max {suc n} (sp c t ∷ᵥ us) (sp d u ∷ᵥ vs) i = step i
    where
    step : (j : Fin (suc n)) →
           compAt (maxU (sp c t ∷ᵥ us) (sp d u ∷ᵥ vs)) j ≡
           maxᶜ (compAt (sp c t ∷ᵥ us) j) (compAt (sp d u ∷ᵥ vs) j)
    step fzero = refl
    step (fsuc j) = comp-max us vs j

  comp-zeros : ∀ {n} (i : Fin n) → compAt (zeros {n}) i ≡ finᶜ zero
  comp-zeros {zero} ()
  comp-zeros {suc n} i = step i
    where
    step : (j : Fin (suc n)) → compAt (zeros {suc n}) j ≡ finᶜ zero
    step fzero = refl
    step (fsuc j) = comp-zeros j

  fin-if : ∀ b m n →
           (if b then finᶜ m else finᶜ n) ≡ finᶜ (if b then m else n)
  fin-if true _ _ = refl
  fin-if false _ _ = refl

  both-zero : ∀ b → (if b then finᶜ zero else finᶜ zero) ≡ finᶜ zero
  both-zero true = refl
  both-zero false = refl

  -- addᶜ / maxᶜ on finite counts are the numeric operations.
  fin-add : ∀ m n → addᶜ (finᶜ m) (finᶜ n) ≡ finᶜ (m + n)
  fin-add _ _ = refl

  fin-max : ∀ m n → maxᶜ (finᶜ m) (finᶜ n) ≡ finᶜ (m ⊔ n)
  fin-max _ _ = refl

  match-arith : ∀ a b c →
                addᶜ (finᶜ a) (maxᶜ (finᶜ b) (finᶜ c)) ≡ finᶜ (a + (b ⊔ c))
  match-arith _ _ _ = refl

  zero-arith : addᶜ (finᶜ zero) (maxᶜ (finᶜ zero) (finᶜ zero)) ≡ finᶜ zero
  zero-arith = refl

  comp-oneS : ∀ {n} (x i : Fin n) c ty →
              compAt (oneS x (sp c ty)) i ≡
              (if toℕ x ≡ᵇ toℕ i then c else finᶜ zero)
  comp-oneS {zero} ()
  comp-oneS {suc n} x i c ty = step x i
    where
    step : (x i : Fin (suc n)) →
           compAt (oneS x (sp c ty)) i ≡
           (if toℕ x ≡ᵇ toℕ i then c else finᶜ zero)
    step fzero fzero rewrite ≡ᵇ-refl zero = refl
    step fzero (fsuc j) = comp-zeros j
    step (fsuc _) fzero = refl
    step (fsuc y) (fsuc j) = comp-oneS y j c ty

  spec-zero : ∀ {n} (Γ : GCtx n) (e : GTm n) (us : Uses n) →
              decide spec Γ e ≡ okR us →
              (i : Fin n) → compAt us i ≡ finᶜ zero
  spec-zero _ (gvar x) us eq i rewrite sym (ok-inj eq) =
    trans (comp-oneS x i (finᶜ zero) (finᶜ (suc zero)))
          (both-zero (toℕ x ≡ᵇ toℕ i))
  spec-zero _ (gtyp x) us eq i rewrite sym (ok-inj eq) =
    trans (comp-oneS x i (finᶜ zero) (finᶜ (suc zero)))
          (both-zero (toℕ x ≡ᵇ toℕ i))
  spec-zero _ gze us eq i rewrite sym (ok-inj eq) = comp-zeros i
  spec-zero Γ (gsu e) us eq = spec-zero Γ e us eq
  spec-zero Γ (gapp f a) us eq with decide spec Γ f in fq
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | okR fu with decide spec Γ a in aq
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | okR au = λ i →
    trans (cong (λ u → compAt u i) (sym (ok-inj eq)))
      (trans (comp-add fu au i)
        (trans (cong₂ addᶜ (spec-zero Γ f fu fq i) (spec-zero Γ a au aq i))
               (fin-add zero zero)))
  spec-zero {n} Γ (glam c t b) out eq with decide spec (gp c t ∷ᵥ Γ) b in bq
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | okR bus = from bus bq eq
    where
    from : (bus : Uses (suc n)) →
           decide spec (gp c t ∷ᵥ Γ) b ≡ okR bus →
           under spec c t bus ≡ okR out →
           (i : Fin n) → compAt out i ≡ finᶜ zero
    from (sp co ty ∷ᵥ rest) bq' uq i with under-tail c t co ty rest out uq
    ... | refl = spec-zero (gp c t ∷ᵥ Γ) b (sp co ty ∷ᵥ rest) bq' (fsuc i)
  spec-zero {n} Γ (gpi c t b) out eq with decide spec (gp c t ∷ᵥ Γ) b in bq
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | okR bus = from bus bq eq
    where
    from : (bus : Uses (suc n)) →
           decide spec (gp c t ∷ᵥ Γ) b ≡ okR bus →
           under spec c t bus ≡ okR out →
           (i : Fin n) → compAt out i ≡ finᶜ zero
    from (sp co ty ∷ᵥ rest) bq' uq i with under-tail c t co ty rest out uq
    ... | refl = spec-zero (gp c t ∷ᵥ Γ) b (sp co ty ∷ᵥ rest) bq' (fsuc i)
  spec-zero {n} Γ (gmatch e z s) out eq with decide spec Γ e in eqe
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | okR eu with decide spec Γ z in eqz
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | okR zu with decide spec (predPair Γ e ∷ᵥ Γ) s in eqs
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | okR suU with under spec (pcomp (predPair Γ e)) (ptype (predPair Γ e)) suU in equ
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | okR srest = from suU eqs equ
    where
    pc = pcomp (predPair Γ e)
    pt = ptype (predPair Γ e)
    from : (suU : Uses (suc n)) →
           decide spec (predPair Γ e ∷ᵥ Γ) s ≡ okR suU →
           under spec pc pt suU ≡ okR srest →
           ∀ i → compAt out i ≡ finᶜ zero
    from (sp co ty ∷ᵥ rest) eqs' uq i with under-tail pc pt co ty rest srest uq
    ... | refl =
      trans (cong (λ u → compAt u i) (sym (ok-inj eq)))
        (trans (comp-add eu (maxU zu rest) i)
          (trans (cong₂ addᶜ
                    (spec-zero Γ e eu eqe i)
                    (trans (comp-max zu rest i)
                      (cong₂ maxᶜ
                        (spec-zero Γ z zu eqz i)
                        (spec-zero (predPair Γ e ∷ᵥ Γ) s (sp co ty ∷ᵥ rest) eqs' (fsuc i)))))
                 zero-arith))

count-sound : ∀ {n} (Γ : GCtx n) e us →
              decide run Γ e ≡ okR us →
              ∀ i → compAt us i ≡ finᶜ (occ (toℕ i) e)
count-sound Γ (gvar x) us eq i rewrite sym (ok-inj eq) =
  trans (comp-oneS x i (finᶜ (suc zero)) (finᶜ zero))
        (fin-if (toℕ x ≡ᵇ toℕ i) (suc zero) zero)
count-sound Γ (gtyp x) us eq i rewrite sym (ok-inj eq) =
  trans (comp-oneS x i (finᶜ zero) (finᶜ (suc zero)))
        (both-zero (toℕ x ≡ᵇ toℕ i))
count-sound Γ gze us eq i rewrite sym (ok-inj eq) = comp-zeros i
count-sound Γ (gsu e) us eq = count-sound Γ e us eq
count-sound Γ (gapp f a) us eq with decide run Γ f in fq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR fu with decide run Γ a in aq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR au = λ i →
  trans (cong (λ u → compAt u i) (sym (ok-inj eq)))
    (trans (comp-add fu au i)
      (trans (cong₂ addᶜ (count-sound Γ f fu fq i) (count-sound Γ a au aq i))
             (fin-add (occ (toℕ i) f) (occ (toℕ i) a))))
count-sound {n} Γ (glam c t b) out eq with decide run (gp c t ∷ᵥ Γ) b in bq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR bus = from bus bq eq
  where
  from : (bus : Uses (suc n)) →
         decide run (gp c t ∷ᵥ Γ) b ≡ okR bus →
         under run c t bus ≡ okR out →
         ∀ i → compAt out i ≡ finᶜ (occ (suc (toℕ i)) b)
  from (sp co ty ∷ᵥ rest) bq' uq i with under-both c t co ty rest out uq
  ... | _ , refl = count-sound (gp c t ∷ᵥ Γ) b (sp co ty ∷ᵥ rest) bq' (fsuc i)
count-sound {n} Γ (gpi c t b) out eq with decide spec (gp c t ∷ᵥ Γ) b in bq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR bus = from bus bq eq
  where
  from : (bus : Uses (suc n)) →
         decide spec (gp c t ∷ᵥ Γ) b ≡ okR bus →
         under spec c t bus ≡ okR out →
         ∀ i → compAt out i ≡ finᶜ zero
  from (sp co ty ∷ᵥ rest) bq' uq i with under-tail c t co ty rest out uq
  ... | refl = spec-zero (gp c t ∷ᵥ Γ) b (sp co ty ∷ᵥ rest) bq' (fsuc i)
count-sound {n} Γ (gmatch e z s) out eq with decide run Γ e in eqe
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR eu with decide run Γ z in eqz
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR zu with decide run (predPair Γ e ∷ᵥ Γ) s in eqs
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR suU with under run (pcomp (predPair Γ e)) (ptype (predPair Γ e)) suU in equ
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR srest = from suU eqs equ
  where
  pc = pcomp (predPair Γ e)
  pt = ptype (predPair Γ e)
  from : (suU : Uses (suc n)) →
         decide run (predPair Γ e ∷ᵥ Γ) s ≡ okR suU →
         under run pc pt suU ≡ okR srest →
         ∀ i → compAt out i ≡
               finᶜ (occ (toℕ i) e + (occ (toℕ i) z ⊔ occ (suc (toℕ i)) s))
  from (sp co ty ∷ᵥ rest) eqs' uq i with under-both pc pt co ty rest srest uq
  ... | _ , refl =
    trans (cong (λ u → compAt u i) (sym (ok-inj eq)))
      (trans (comp-add eu (maxU zu rest) i)
        (trans (cong₂ addᶜ
                  (count-sound Γ e eu eqe i)
                  (trans (comp-max zu rest i)
                    (cong₂ maxᶜ
                      (count-sound Γ z zu eqz i)
                      (count-sound (predPair Γ e ∷ᵥ Γ) s (sp co ty ∷ᵥ rest) eqs' (fsuc i)))))
               (match-arith (occ (toℕ i) e) (occ (toℕ i) z) (occ (suc (toℕ i)) s))))

-- A checked g1 binder is used exactly once by the syntax `occ` counts.
g1-count : ∀ {n} (Γ : GCtx n) c t b us →
           isG1 c ≡ true →
           decide run Γ (glam c t b) ≡ okR us →
           occ zero b ≡ suc zero
g1-count {n} Γ c t b us g eq with decide run (gp c t ∷ᵥ Γ) b in bq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR bus = from bus bq eq
  where
  sat-g1-one : ∀ n → sat g1 (finᶜ n) ≡ true → n ≡ suc zero
  sat-g1-one zero ()
  sat-g1-one (suc zero) _ = refl
  sat-g1-one (suc (suc _)) ()
  from : (bus : Uses (suc n)) →
         decide run (gp c t ∷ᵥ Γ) b ≡ okR bus →
         under run c t bus ≡ okR us →
         occ zero b ≡ suc zero
  from (sp co ty ∷ᵥ rest) bq' uq with under-both c t co ty rest us uq
  ... | sc , _ =
    sat-g1-one (occ zero b)
      (subst (λ g' → sat g' (finᶜ (occ zero b)) ≡ true) (isG1-sound c g)
        (subst (λ k → sat c k ≡ true)
          (count-sound (gp c t ∷ᵥ Γ) b (sp co ty ∷ᵥ rest) bq' fzero)
          sc))

------------------------------------------------------------------------
-- What a g1 slot still owes the machine.
------------------------------------------------------------------------

data Tight : Set where
  loose tight : Tight

data SlotOk (tg : Tight) (r : Ref) (d : ℕ) : Set where
  slot-g1 : isG1 (checked r) ≡ true → residual r ≡ g1 →
            (tg ≡ tight → d ≡ suc zero) → d ≤ suc zero →
            SlotOk tg r d
  slot-g0 : isG1 (checked r) ≡ true → residual r ≡ g0 →
            d ≡ zero → SlotOk tg r d
  slot-ω  : isG1 (checked r) ≡ false → SlotOk tg r d

data Funds (tg : Tight) : List Ref → (ℕ → ℕ) → Set where
  fnil  : ∀ {d} → Funds tg [] d
  fcons : ∀ {r rs d} →
          SlotOk tg r (d zero) →
          Funds tg rs (λ i → d (suc i)) →
          Funds tg (r ∷ rs) d

funds-cast : ∀ {tg rs d1 d2} →
             (∀ i → d1 i ≡ d2 i) →
             Funds tg rs d1 → Funds tg rs d2
funds-cast _ fnil = fnil
funds-cast eq (fcons s tl) =
  fcons (subst (SlotOk _ _) (eq zero) s)
        (funds-cast (λ i → eq (suc i)) tl)

slot-≤ : ∀ {r d1 d2} → d2 ≤ d1 → SlotOk loose r d1 → SlotOk loose r d2
slot-≤ le (slot-g1 g rz _ le1) = slot-g1 g rz (λ ()) (≤-trans le le1)
slot-≤ le (slot-g0 g rz dz) = slot-g0 g rz (≤0 le dz)
  where
  ≤0 : ∀ {m n} → m ≤ n → n ≡ zero → m ≡ zero
  ≤0 z≤n refl = refl
slot-≤ _ (slot-ω ng) = slot-ω ng

funds-≤ : ∀ {rs d1 d2} →
          (∀ i → d2 i ≤ d1 i) →
          Funds loose rs d1 → Funds loose rs d2
funds-≤ _ fnil = fnil
funds-≤ le (fcons s tl) =
  fcons (slot-≤ (le zero) s) (funds-≤ (λ i → le (suc i)) tl)

data NoSharp : ∀ {n} → Vec Grade n → List Ref → Set where
  ns-nil  : NoSharp []ᵥ []
  ns-cons : ∀ {n g} {Γ : Vec Grade n} {r rs} →
            (isG1 (checked r) ≡ true → isG1 g ≡ true) →
            NoSharp Γ rs →
            NoSharp (g ∷ᵥ Γ) (r ∷ rs)

notG1 : ∀ {g} {r : Ref} →
       (isG1 (checked r) ≡ true → isG1 g ≡ true) →
       isG1 g ≡ false →
       isG1 (checked r) ≡ false
notG1 {r = r} imp gz = go (isG1 (checked r)) refl
  where
  boom : true ≡ false → ⊥
  boom ()
  go : (b : Bool) → isG1 (checked r) ≡ b → isG1 (checked r) ≡ false
  go false p = p
  go true eq = ⊥-elim (boom (trans (sym (imp eq)) gz))

ns-clear : ∀ {n} {Γ : Vec Grade n} {rs} →
           NoSharp Γ rs → g1InScope Γ ≡ false → anyG1 rs ≡ false
ns-clear {Γ = []ᵥ} {rs = []} ns-nil _ = refl
ns-clear {Γ = g ∷ᵥ Γ} {rs = r ∷ rs} (ns-cons imp tl) eq
  with ∨-false (isG1 g) (g1InScope Γ) eq
... | gz , rest rewrite notG1 {g} {r} imp gz = ns-clear tl rest

------------------------------------------------------------------------
-- Spending a checked g1 whose residual is still g1 yields residual g0.
-- The checked grade and the object stay. This is the one use `g1-count`
-- budgets.
------------------------------------------------------------------------

spend-g1 : (r : Ref) → isG1 (checked r) ≡ true → residual r ≡ g1 →
           Σ Ref (λ r' →
             spendRef r ≡ just r' ×
             residual r' ≡ g0 ×
             checked r' ≡ checked r ×
             obj r' ≡ obj r)
spend-g1 (ref o c res k) cg rz with isG1-sound c cg
... | refl with rz
... | refl = go k
  where
  go : (k : Kept g1 g1) →
       Σ Ref (λ r' →
         spendRef (ref o g1 g1 k) ≡ just r' ×
         residual r' ≡ g0 ×
         checked r' ≡ g1 ×
         obj r' ≡ o)
  go (fin-kept le) =
    let r' = ref o g1 g0 (fin-kept (lower≤ le))
    in r' , refl , refl , refl , refl

------------------------------------------------------------------------
-- Grades of a context, and terms with no `gmatch`. Exact exhaustion
-- is stated only for the match-free fragment: a match spends the
-- heavier branch, so a lighter branch can leave a `fin n` above 0.
------------------------------------------------------------------------

grades : ∀ {n} → GCtx n → Vec Grade n
grades []ᵥ = []ᵥ
grades (gp c _ ∷ᵥ Γ) = c ∷ᵥ grades Γ

lookup-grades : ∀ {n} (Γ : GCtx n) (x : Fin n) →
                vlookup (grades Γ) x ≡ pcomp (vlookup Γ x)
lookup-grades {suc n} (gp c t ∷ᵥ Γ) x = step x
  where
  step : (y : Fin (suc n)) →
         vlookup (c ∷ᵥ grades Γ) y ≡ pcomp (vlookup (gp c t ∷ᵥ Γ) y)
  step fzero = refl
  step (fsuc y) = lookup-grades Γ y

data MatchFree {n} : GTm n → Set where
  mf-var : ∀ {x} → MatchFree (gvar x)
  mf-typ : ∀ {x} → MatchFree (gtyp x)
  mf-ze  : MatchFree gze
  mf-su  : ∀ {e} → MatchFree e → MatchFree (gsu e)
  mf-app : ∀ {f a} → MatchFree f → MatchFree a → MatchFree (gapp f a)
  mf-pi  : ∀ {c t b} → MatchFree b → MatchFree (gpi c t b)
  mf-lam : ∀ {c t b} → MatchFree b → MatchFree (glam c t b)

TMf : Tight → ∀ {n} → GTm n → Set
TMf loose _ = ⊤
TMf tight e = MatchFree e

-- A closure remembers the judgment it was checked under. The captured
-- environment has no g1 (`anyG1`), which is what `glam` required.
data Pay (tg : Tight) : Val → Set where
  pay-nat : ∀ k → Pay tg (nat k)
  pay-suc : ∀ r → Pay tg (suc↑ r)
  pay-clo : ∀ {n} {env : List Ref} {Γ : GCtx n} {c t : Grade}
              {b : GTm (suc n)} {us : Uses (suc n)} →
            anyG1 env ≡ false →
            NoEsc (c ∷ᵥ grades Γ) b →
            decide run (gp c t ∷ᵥ Γ) b ≡ okR us →
            (isG1 c ≡ true → occ zero b ≡ suc zero) →
            TMf tg b →
            NoSharp (grades Γ) env →
            Pay tg (clo env (n , glam c t b))

data HeapPay (tg : Tight) : List Obj → Set where
  hp-nil  : HeapPay tg []
  hp-cons : ∀ {o os} → Pay tg (payload o) → HeapPay tg os →
            HeapPay tg (o ∷ os)

OkRun : ∀ {n} → GCtx n → GTm n → Set
OkRun Γ e = Σ (Uses _) (λ us → decide run Γ e ≡ okR us)

-- Frames. `bd` freezes the outer environment at the outer debt and
-- presents debt 0 to the inner term. `saved` is not produced by a
-- pure `GTm` trace. A match frame exists only in the loose mode.
-- The debt index is `debtF` itself, not an abstract function. A
-- preserved frame then matches by constructor without function
-- extensionality.
-- Indexed by the grade vector of the focus that owns the
-- continuation. An `ar` frame stays in that vector, so the argument
-- is checked in the same context the value returns to. `bd` changes
-- it: the tail is the outer vector, the frame itself is the inner one.
data Fr (tg : Tight) : {n : ℕ} → Vec Grade n → List Frame → (ℕ → ℕ) → Set where
  fr-nil : Fr tg []ᵥ [] (λ i → debtF i [])
  fr-ar  : ∀ {n a k} {Γ : GCtx n} →
           NoEsc (grades Γ) a → OkRun Γ a → TMf tg a →
           Fr tg (grades Γ) k (λ i → debtF i k) →
           Fr tg (grades Γ) (ar a ∷ k) (λ i → debtF i (ar a ∷ k))
  fr-fn  : ∀ {n gs r k} →
           Fr tg {n} gs k (λ i → debtF i k) →
           Fr tg gs (fn r ∷ k) (λ i → debtF i (fn r ∷ k))
  fr-su  : ∀ {n gs k} →
           Fr tg {n} gs k (λ i → debtF i k) →
           Fr tg gs (su ∷ k) (λ i → debtF i (su ∷ k))
  fr-mt  : ∀ {n e z s k} {Γ : GCtx n} →
           tg ≡ loose →
           NoEsc (grades Γ) z →
           NoEsc (predG (grades Γ) e ∷ᵥ grades Γ) s →
           OkRun Γ z →
           OkRun (predPair Γ e ∷ᵥ Γ) s →
           (isG1 (pcomp (predPair Γ e)) ≡ true → occ zero s ≡ suc zero) →
           TMf tg z → TMf tg s →
           Fr tg (grades Γ) k (λ i → debtF i k) →
           Fr tg (grades Γ) (mt e z s ∷ k) (λ i → debtF i (mt e z s ∷ k))
  fr-bd  : ∀ {nIn nOut gsIn gsOut env k} →
           NoSharp {nOut} gsOut env →
           Funds tg env (λ i → debtF i k) →
           Fr tg {nOut} gsOut k (λ i → debtF i k) →
           Fr tg {nIn} gsIn (bd env ∷ k) (λ i → debtF i (bd env ∷ k))

data Focus (tg : Tight) : Ctl → Set where
  foc-ev : ∀ {n e env k} {Γ : GCtx n} →
           NoEsc (grades Γ) e →
           OkRun Γ e →
           TMf tg e →
           NoSharp (grades Γ) env →
           Funds tg env (λ i → occ i e + debtF i k) →
           Fr tg (grades Γ) k (λ i → debtF i k) →
           Focus tg (ev e env k)
  foc-rv : ∀ {n r env k} {gs : Vec Grade n} →
           NoSharp gs env →
           Funds tg env (λ i → debtF i k) →
           Fr tg gs k (λ i → debtF i k) →
           Focus tg (rv r env k)
  foc-idle : Focus tg idle
  foc-pr   : ∀ {c} → Focus tg (pr c)

data Inv (tg : Tight) : Sys → Set where
  inv : ∀ {h p} →
        HeapPay tg h →
        Focus tg (ctl p) →
        Inv tg (sys h (p ∷ []))

-- At scope exit the continuation debt is 0. A tight g1 slot cannot
-- still owe one use, so its residual is g0.
slot-spent : ∀ {r} → SlotOk tight r zero → isG1 (checked r) ≡ true →
             residual r ≡ g0
slot-spent (slot-g1 _ _ eq _) _ = ⊥-elim (boom (eq refl))
  where
  boom : zero ≡ suc zero → ⊥
  boom ()
slot-spent (slot-g0 _ rz _) _ = rz
slot-spent (slot-ω ng) g = ⊥-elim (boom (trans (sym ng) g))
  where
  boom : false ≡ true → ⊥
  boom ()

funds-spent : ∀ {env i r} →
              Funds tight env (λ _ → zero) →
              lookup env i ≡ just r →
              isG1 (checked r) ≡ true →
              residual r ≡ g0
funds-spent {i = zero} (fcons s _) refl g = slot-spent s g
funds-spent {i = suc i} (fcons _ tl) eq g = funds-spent tl eq g
funds-spent {i = zero} fnil ()
funds-spent {i = suc _} fnil ()

exit-g1 : ∀ {v env env0 k r i} →
          Focus tight (rv v env (bd env0 ∷ k)) →
          lookup env i ≡ just r →
          isG1 (checked r) ≡ true →
          residual r ≡ g0
exit-g1 (foc-rv _ fu (fr-bd _ _ _)) eq g = funds-spent fu eq g

------------------------------------------------------------------------
-- Trace. Match-free, so no `mt` frame is built. `tight` debt is
-- equality with `occ`. A checked g1 slot therefore holds residual g1
-- exactly when one use is still ahead, and residual g0 when the
-- continuation under a `bd` owes nothing.
------------------------------------------------------------------------

∅-just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
∅-just ()

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

≡ᵇ-comm : ∀ a b → (a ≡ᵇ b) ≡ (b ≡ᵇ a)
≡ᵇ-comm zero    zero    = refl
≡ᵇ-comm zero    (suc _) = refl
≡ᵇ-comm (suc _) zero    = refl
≡ᵇ-comm (suc a) (suc b) = ≡ᵇ-comm a b

gone : ∀ {n} → suc n ≤ suc zero → n ≡ zero
gone (s≤s z≤n) = refl

true≢false : true ≡ false → ⊥
true≢false ()

fund-at : ∀ {tg env d ix r} →
          Funds tg env d → lookup env ix ≡ just r → SlotOk tg r (d ix)
fund-at {ix = zero}  (fcons s _) refl = s
fund-at {ix = suc _} (fcons _ tl) eq  = fund-at tl eq
fund-at {ix = zero}  fnil ()
fund-at {ix = suc _} fnil ()

funds-repl : ∀ {tg env d d' ix r r'} →
             Funds tg env d →
             lookup env ix ≡ just r →
             (∀ i → (i ≡ᵇ ix) ≡ false → d i ≡ d' i) →
             SlotOk tg r' (d' ix) →
             Funds tg (repl ix r' env) d'
funds-repl {ix = zero} (fcons _ tl) refl eq sok =
  fcons sok (funds-cast (λ i → eq (suc i) refl) tl)
funds-repl {ix = suc ix} (fcons s tl) lk eq sok =
  fcons (subst (SlotOk _ _) (eq zero refl) s)
        (funds-repl tl lk (λ i p → eq (suc i) p) sok)
funds-repl {ix = zero}    fnil ()
funds-repl {ix = suc _}   fnil ()

ns-set : ∀ {n ix r r'} {Γ : Vec Grade n} {env} →
         NoSharp Γ env →
         lookup env ix ≡ just r →
         (isG1 (checked r') ≡ true → isG1 (checked r) ≡ true) →
         NoSharp Γ (repl ix r' env)
ns-set {ix = zero}    (ns-cons imp tl) refl wk = ns-cons (λ p → imp (wk p)) tl
ns-set {ix = suc ix}  (ns-cons imp tl) eq wk   = ns-cons imp (ns-set tl eq wk)
ns-set {ix = zero}    ns-nil ()
ns-set {ix = suc _}   ns-nil ()

funds-ω : ∀ {tg d} rs → anyG1 rs ≡ false → Funds tg rs d
funds-ω []       _  = fnil
funds-ω (r ∷ rs) eq with ∨-false (isG1 (checked r)) (anyG1 rs) eq
... | ng , rest = fcons (slot-ω ng) (funds-ω rs rest)

funds-clear : ∀ {n tg d} {Γ : Vec Grade n} {rs} →
              NoSharp Γ rs → g1InScope Γ ≡ false → Funds tg rs d
funds-clear {rs = []} ns-nil _ = fnil
funds-clear {Γ = g ∷ᵥ Γ} {rs = r ∷ rs} (ns-cons imp tl) eq
  with ∨-false (isG1 g) (g1InScope Γ) eq
... | gz , rest = fcons (slot-ω (notG1 {g} {r} imp gz)) (funds-clear tl rest)

hp-snoc : ∀ {tg h v} → HeapPay tg h → Pay tg v →
          HeapPay tg (h ++ cell v live ∷ [])
hp-snoc hp-nil         p = hp-cons p hp-nil
hp-snoc (hp-cons q tl) p = hp-cons q (hp-snoc tl p)

pay-at : ∀ {tg h i v} → HeapPay tg h → payloadAt h i ≡ just v → Pay tg v
pay-at {i = zero} (hp-cons p _) refl = p
pay-at {i = suc i} (hp-cons _ tl) eq = pay-at tl eq
pay-at {i = zero} hp-nil ()
pay-at {i = suc _} hp-nil ()

pay-apply : ∀ {tg} bs {h} → HeapPay tg h → HeapPay tg (apply bs h)
pay-apply {tg} bs {h} hp = go bs h hp
  where
  go : (bs : List Bool) (os : List Obj) → HeapPay tg os → HeapPay tg (apply bs os)
  go _ [] hp-nil = hp-nil
  go [] (_ ∷ os) (hp-cons _ tl) = hp-cons (pay-nat zero) (go [] os tl)
  go (false ∷ bs) (_ ∷ os) (hp-cons _ tl) = hp-cons (pay-nat zero) (go bs os tl)
  go (true ∷ bs) (_ ∷ os) (hp-cons p tl) = hp-cons p (go bs os tl)

pay-poke : ∀ k v {tg h} → HeapPay tg h → HeapPay tg (poke h k v)
pay-poke _       _ hp-nil         = hp-nil
pay-poke zero    v (hp-cons _ tl) = hp-cons (pay-nat v) tl
pay-poke (suc k) v (hp-cons p tl) = hp-cons p (pay-poke k v tl)

split-app : ∀ {n} (Γ : GCtx n) f a us →
            decide run Γ (gapp f a) ≡ okR us →
            Σ (Uses n) (λ fus → decide run Γ f ≡ okR fus ×
            Σ (Uses n) (λ aus → decide run Γ a ≡ okR aus))
split-app Γ f a _ eq
  with bind-split (decide run Γ f)
        (λ fus → decide run Γ a >>= λ aus → okR (addU fus aus)) eq
... | fus , feq , rest
  with bind-split (decide run Γ a) (λ aus → okR (addU fus aus)) rest
... | aus , aeq , _ = fus , feq , (aus , aeq)

lam-body : ∀ {n} (Γ : GCtx n) c t b us →
           decide run Γ (glam c t b) ≡ okR us →
           Σ (Uses (suc n)) (λ bus → decide run (gp c t ∷ᵥ Γ) b ≡ okR bus)
lam-body Γ c t b _ eq
  with bind-split (decide run (gp c t ∷ᵥ Γ) b) (under run c t) eq
... | bus , beq , _ = bus , beq

-- A gvar focus on a checked g1 still has residual g1. `spendRef` is
-- the one use `g1-count` recorded, not a refusal.
g1-ready : ∀ {tg n env k r} {x : Fin n} →
           Focus tg (ev (gvar x) env k) →
           lookup env (toℕ x) ≡ just r →
           isG1 (checked r) ≡ true →
           residual r ≡ g1
g1-ready {k = k} {r = r} {x = x} (foc-ev _ _ _ _ fu _) lk g with fund-at fu lk
... | s rewrite ≡ᵇ-refl (toℕ x) = body s g
  where
  body : SlotOk _ r (suc (debtF (toℕ x) k)) → isG1 (checked r) ≡ true →
         residual r ≡ g1
  body (slot-g1 _ rz _ _) _ = rz
  body (slot-g0 _ _ dz)   _ = ⊥-elim (bad dz)
    where
    bad : suc (debtF (toℕ x) k) ≡ zero → ⊥
    bad ()
  body (slot-ω ng) g' = ⊥-elim (true≢false (trans (sym g') ng))

g1-spends : ∀ {n env k r} {x : Fin n} →
            Focus tight (ev (gvar x) env k) →
            lookup env (toℕ x) ≡ just r →
            isG1 (checked r) ≡ true →
            Σ Ref (λ r' →
              spendRef r ≡ just r' × residual r' ≡ g0 ×
              checked r' ≡ checked r × obj r' ≡ obj r)
g1-spends foc lk g = spend-g1 _ g (g1-ready foc lk g)

------------------------------------------------------------------------
-- One step keeps the tight invariant. The system in the invariant has
-- one process, so an index above 0 does not step. `collect` keeps
-- control and only rewrites payloads the mark vector drops.
------------------------------------------------------------------------

-- A root or mailbox update builds a new process record. Control is
-- unchanged, so the same `Focus` is the focus of that record.
pres-deref : ∀ {h p t i j} →
             HeapPay tight h → Focus tight (ctl p) →
             deref run (sys h (p ∷ [])) i j ≡ just t →
             Inv tight t
pres-deref {h} {p} {t} {i = i} {j = j} hp foc eq = go i eq
  where
  go : ∀ i → deref run (sys h (p ∷ [])) i j ≡ just t → Inv tight t
  go (suc _) eq' = ⊥-elim (∅-just eq')
  go zero eq' = at (lookup (roots p) j) eq' refl
    where
    at : (m : Maybe Ref) →
         deref run (sys h (p ∷ [])) zero j ≡ just t →
         lookup (roots p) j ≡ m → Inv tight t
    at nothing eqR lk =
      ⊥-elim (∅-just
        (subst (λ m → derefAt (sys h (p ∷ [])) zero j m ≡ just t) lk eqR))
    at (just r) eqR lk =
      after (spendRef r) refl
        (subst (λ m → derefAt (sys h (p ∷ [])) zero j m ≡ just t) lk eqR)
      where
      after : (m : Maybe Ref) → spendRef r ≡ m →
              derefAt (sys h (p ∷ [])) zero j (just r) ≡ just t →
              Inv tight t
      after nothing es eqS =
        ⊥-elim (∅-just
          (subst (λ m → derefSpent h (p ∷ []) zero j r m ≡ just t) es eqS))
      after (just r') es eqS =
        upd (update j r' (roots p)) refl
          (subst (λ m → derefSpent h (p ∷ []) zero j r m ≡ just t) es eqS)
        where
        upd : (m : Maybe (List Ref)) →
              update j r' (roots p) ≡ m →
              mapSys h (putHeadOf p [] (update j r' (roots p))) ≡ just t →
              Inv tight t
        upd nothing uq eqU =
          ⊥-elim (∅-just
            (subst (λ m → mapSys h (putHeadOf p [] m) ≡ just t) uq eqU))
        upd (just rs) uq eqU =
          subst (Inv tight)
            (just-inj (subst (λ m → mapSys h (putHeadOf p [] m) ≡ just t) uq eqU))
            (inv {p = record p { roots = rs }} hp foc)

pres-recv : ∀ {h p t i} →
            HeapPay tight h → Focus tight (ctl p) →
            recv (sys h (p ∷ [])) i ≡ just t →
            Inv tight t
pres-recv {h} {p} {t} {i = i} hp foc eq = go i eq
  where
  go : ∀ i → recv (sys h (p ∷ [])) i ≡ just t → Inv tight t
  go (suc _) eq' = ⊥-elim (∅-just eq')
  go zero eq' = box (inbox p) eq' refl
    where
    box : (ms : List Msg) →
          recv (sys h (p ∷ [])) zero ≡ just t →
          inbox p ≡ ms → Inv tight t
    box [] eqB ib rewrite ib = ⊥-elim (∅-just eqB)
    box (msg r ∷ ms) eqB ib rewrite ib =
      subst (Inv tight) (just-inj eqB)
        (inv {p = record p { roots = roots p ++ r ∷ [] ; inbox = ms }} hp foc)

pres-alloc : ∀ {h p t i g v} →
             HeapPay tight h → Focus tight (ctl p) →
             alloc (sys h (p ∷ [])) i g v ≡ just t →
             Inv tight t
pres-alloc {h} {p} {t} {i = i} {g = g} {v = v} hp foc eq = go i eq
  where
  go : ∀ i → alloc (sys h (p ∷ [])) i g v ≡ just t → Inv tight t
  go (suc _) eq' = ⊥-elim (∅-just eq')
  go zero eq' =
    subst (Inv tight) (just-inj eq')
      (inv {p = record p { roots = roots p ++ ref (length h) g g (selfKept g) ∷ [] }}
           (hp-snoc hp (pay-nat v)) foc)

pres-reuse : ∀ {h p t i j g v} →
             HeapPay tight h → Focus tight (ctl p) →
             reuse (sys h (p ∷ [])) i j g v ≡ just t →
             Inv tight t
pres-reuse {h} {p} {t} {i = i} {j = j} {g = g} {v = v} hp foc eq = go i eq
  where
  go : ∀ i → reuse (sys h (p ∷ [])) i j g v ≡ just t → Inv tight t
  go (suc _) eq' = ⊥-elim (∅-just eq')
  go zero eq' = at (rootAt (sys h (p ∷ [])) zero j) eq' refl
    where
    at : (m : Maybe Ref) →
         reuse (sys h (p ∷ [])) zero j g v ≡ just t →
         rootAt (sys h (p ∷ [])) zero j ≡ m →
         Inv tight t
    at nothing eqR rq =
      ⊥-elim (∅-just
        (subst (λ m → reuseFrom (sys h (p ∷ [])) zero j g v m ≡ just t) rq eqR))
    at (just r) eqR rq =
      flags (isG1 (checked r))
            (isZeroGrade (residual r))
            (count (obj r) (refsOf (sys h (p ∷ []))) ≡ᵇ 1)
            refl refl refl
            (subst (λ m → reuseFrom (sys h (p ∷ [])) zero j g v m ≡ just t) rq eqR)
      where
      slot = ref (obj r) g g (selfKept g)
      flags : (a b c : Bool) →
              isG1 (checked r) ≡ a →
              isZeroGrade (residual r) ≡ b →
              (count (obj r) (refsOf (sys h (p ∷ []))) ≡ᵇ 1) ≡ c →
              reuseFrom (sys h (p ∷ [])) zero j g v (just r) ≡ just t →
              Inv tight t
      flags false _ _ aq _ _ eqF rewrite aq = ⊥-elim (∅-just eqF)
      flags true false _ aq bq _ eqF rewrite aq | bq = ⊥-elim (∅-just eqF)
      flags true true false aq bq cq eqF rewrite aq | bq | cq =
        ⊥-elim (∅-just eqF)
      -- A nat write has no children, so `childrenBelow` is `true`.
      flags true true true aq bq cq eqF rewrite aq | bq | cq =
        upd (update j slot (roots p)) refl eqF
        where
        upd : (m : Maybe (List Ref)) →
              update j slot (roots p) ≡ m →
              mapSys (poke h (obj r) v) (putHeadOf p [] (update j slot (roots p))) ≡ just t →
              Inv tight t
        upd nothing uq eqU =
          ⊥-elim (∅-just
            (subst (λ m → mapSys (poke h (obj r) v) (putHeadOf p [] m) ≡ just t) uq eqU))
        upd (just rs) uq eqU =
          subst (Inv tight)
            (just-inj
              (subst (λ m → mapSys (poke h (obj r) v) (putHeadOf p [] m) ≡ just t) uq eqU))
            (inv {p = record p { roots = rs }} (pay-poke (obj r) v hp) foc)

pres-send : ∀ {h p t si sj ri} →
            HeapPay tight h → Focus tight (ctl p) →
            send (sys h (p ∷ [])) si sj ri ≡ just t →
            Inv tight t
pres-send {h} {p} {t} {si = si} {sj = sj} {ri = ri} hp foc eq = from si ri eq
  where
  -- A copy posts into pid 0 and keeps the root. A move to pid 0 posts
  -- into the process whose root was dropped. Any other receiver is
  -- stuck on a one-process system.
  from : ∀ si ri → send (sys h (p ∷ [])) si sj ri ≡ just t → Inv tight t
  from (suc _) _ eq' = ⊥-elim (∅-just eq')
  from zero zero eq' = taken (removeAt sj (roots p)) eq' refl
    where
    taken : (m : Maybe (Ref × List Ref)) →
            send (sys h (p ∷ [])) zero sj zero ≡ just t →
            removeAt sj (roots p) ≡ m → Inv tight t
    taken nothing eqS rq =
      ⊥-elim (∅-just
        (subst (λ m → sendTaken (dropRoot p m) zero zero h (p ∷ []) ≡ just t) rq eqS))
    taken (just (r , rs)) eqS rq =
      grade (isZeroGrade (residual r)) (kind (checked r)) refl refl
        (subst (λ m → sendTaken (dropRoot p m) zero zero h (p ∷ []) ≡ just t) rq eqS)
      where
      sp' = record p { roots = rs }
      grade : (z : Bool) (mk : Maybe Kind) →
              isZeroGrade (residual r) ≡ z →
              kind (checked r) ≡ mk →
              dispatch z mk r sp' zero zero h (p ∷ []) ≡ just t →
              Inv tight t
      grade true _ zq _ eqG rewrite zq = ⊥-elim (∅-just eqG)
      grade false nothing zq kq eqG rewrite zq | kq = ⊥-elim (∅-just eqG)
      grade false (just Kcopy) zq kq eqG rewrite zq | kq =
        subst (Inv tight) (just-inj eqG)
          (inv {p = record p { inbox = inbox p ++ msg r ∷ [] }} hp foc)
      grade false (just Kmove) zq kq eqG rewrite zq | kq =
        subst (Inv tight) (just-inj eqG)
          (inv {p = record sp' { inbox = inbox p ++ msg r ∷ [] }} hp foc)
  from zero (suc rj) eq' = taken (removeAt sj (roots p)) eq' refl
    where
    taken : (m : Maybe (Ref × List Ref)) →
            send (sys h (p ∷ [])) zero sj (suc rj) ≡ just t →
            removeAt sj (roots p) ≡ m → Inv tight t
    taken nothing eqS rq =
      ⊥-elim (∅-just
        (subst (λ m → sendTaken (dropRoot p m) zero (suc rj) h (p ∷ []) ≡ just t) rq eqS))
    taken (just (r , rs)) eqS rq =
      grade (isZeroGrade (residual r)) (kind (checked r)) refl refl
        (subst (λ m → sendTaken (dropRoot p m) zero (suc rj) h (p ∷ []) ≡ just t) rq eqS)
      where
      sp' = record p { roots = rs }
      grade : (z : Bool) (mk : Maybe Kind) →
              isZeroGrade (residual r) ≡ z →
              kind (checked r) ≡ mk →
              dispatch z mk r sp' zero (suc rj) h (p ∷ []) ≡ just t →
              Inv tight t
      grade true _ zq _ eqG rewrite zq = ⊥-elim (∅-just eqG)
      grade false nothing zq kq eqG rewrite zq | kq = ⊥-elim (∅-just eqG)
      grade false (just Kcopy) zq kq eqG rewrite zq | kq = ⊥-elim (∅-just eqG)
      grade false (just Kmove) zq kq eqG rewrite zq | kq = ⊥-elim (∅-just eqG)

-- The process is a constructor here. `clean` of an abstract record
-- does not unify with the filtered fields, so the caller matches `proc`.
pres-collect : ∀ {h i st rs ib c} →
               HeapPay tight h →
               Focus tight c →
               Inv tight (collect (sys h (proc i st rs ib c ∷ [])))
pres-collect {h} {i = i} {st = st} {rs = rs} {ib = ib} {c = c} hp foc =
  inv {p = proc i st (filterKeep rs) (filterMsg ib) c}
      (pay-apply (markVec (sys h (proc i st rs ib c ∷ []))) hp)
      foc

-- `useVar` on a checked g1. A nat copy leaves the spent ref in the
-- slot. A suc↑ or clo moves, and the slot becomes a fresh g0.
pres-var : ∀ {h p t n env k} {Γ : GCtx n} {x : Fin n} →
           HeapPay tight h →
           NoSharp (grades Γ) env →
           Funds tight env (λ i → occ i (gvar x) + debtF i k) →
           Fr tight (grades Γ) k (λ i → debtF i k) →
           useVar h (p ∷ []) zero env k (toℕ x) (lookup env (toℕ x)) ≡ just t →
           Inv tight t
pres-var {h} {p} {t} {env = env} {k = k} {Γ = Γ} {x = x} hp ns fu fr eq =
  look (lookup env (toℕ x)) eq refl
  where
  skip : ∀ i → (i ≡ᵇ toℕ x) ≡ false →
         (occ i (gvar x) + debtF i k) ≡ debtF i k
  skip i neq rewrite ≡ᵇ-comm (toℕ x) i | neq = refl
  look : (m : Maybe Ref) →
         useVar h (p ∷ []) zero env k (toℕ x) (lookup env (toℕ x)) ≡ just t →
         lookup env (toℕ x) ≡ m → Inv tight t
  look nothing eq' lk =
    ⊥-elim (∅-just (subst (λ m →
      useVar h (p ∷ []) zero env k (toℕ x) m ≡ just t) lk eq'))
  look (just r) eq' lk =
    onS (fund-at fu lk)
        (subst (λ m →
           useVar h (p ∷ []) zero env k (toℕ x) m ≡ just t) lk eq')
    where
    onS : SlotOk tight r (occ (toℕ x) (gvar x) + debtF (toℕ x) k) →
          useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
          Inv tight t
    onS s eqS rewrite ≡ᵇ-refl (toℕ x) = onS' s eqS
      where
      onS' : SlotOk tight r (suc (debtF (toℕ x) k)) →
             useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
             Inv tight t
      onS' (slot-g0 _ _ dz) _ = ⊥-elim (bad dz)
        where
        bad : suc (debtF (toℕ x) k) ≡ zero → ⊥
        bad ()
      onS' (slot-ω ng) eqv = openSp (spendRef r) refl eqv
        where
        -- Rewrite `spendRef` in the clause that inspects the
        -- equation. A nested `where` that only restates `useVar`
        -- does not see a rewrite from its parent.
        openSp : (m : Maybe Ref) → spendRef r ≡ m →
                 useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
                 Inv tight t
        openSp nothing es eqS rewrite es = ⊥-elim (∅-just eqS)
        openSp (just r') es eqS =
          see (payloadAt h (obj r)) refl (spendRef-checked r r' es) eqS
          where
          see : (mv : Maybe Val) → payloadAt h (obj r) ≡ mv →
                checked r' ≡ checked r →
                useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
                Inv tight t
          see nothing pv chk eqU rewrite es | pv = ⊥-elim (∅-just eqU)
          see (just (nat nv)) pv chk eqU
              rewrite es | pv | sym (just-inj eqU) =
            inv (hp-snoc hp (pay-nat nv))
              (foc-rv
                (ns-set ns lk (λ q → subst (λ c → isG1 c ≡ true) chk q))
                (funds-repl fu lk skip
                  (slot-ω (subst (λ c → isG1 c ≡ false) (sym chk) ng)))
                fr)
          -- `mv` stays the constructor in this clause. Generalising it
          -- makes `see` stuck, so the bool split lives here.
          see (just (suc↑ _)) pv chk eqU =
            go (isG1 (checked r')) refl eqU
            where
            go : (b : Bool) → isG1 (checked r') ≡ b →
                 useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
                 Inv tight t
            go true gq _ =
              ⊥-elim (true≢false
                (trans (sym (subst (λ c → isG1 c ≡ true) chk gq)) ng))
            go false gq eqG rewrite es | pv | gq | sym (just-inj eqG) =
              inv hp
                (foc-rv
                  (ns-set ns lk (λ q → subst (λ c → isG1 c ≡ true) chk q))
                  (funds-repl fu lk skip (slot-ω gq)) fr)
          see (just (clo _ _)) pv chk eqU =
            go (isG1 (checked r')) refl eqU
            where
            go : (b : Bool) → isG1 (checked r') ≡ b →
                 useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
                 Inv tight t
            go true gq _ =
              ⊥-elim (true≢false
                (trans (sym (subst (λ c → isG1 c ≡ true) chk gq)) ng))
            go false gq eqG rewrite es | pv | gq | sym (just-inj eqG) =
              inv hp
                (foc-rv
                  (ns-set ns lk (λ q → subst (λ c → isG1 c ≡ true) chk q))
                  (funds-repl fu lk skip (slot-ω gq)) fr)
      onS' (slot-g1 cg rz _ le) eqv with spend-g1 r cg rz
      ... | r' , es , rz' , chk , _ = see (payloadAt h (obj r)) refl eqv
        where
        see : (mv : Maybe Val) → payloadAt h (obj r) ≡ mv →
              useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
              Inv tight t
        see nothing pv eqS rewrite es | pv = ⊥-elim (∅-just eqS)
        see (just (nat nv)) pv eqS
            rewrite es | pv | sym (just-inj eqS) =
          inv (hp-snoc hp (pay-nat nv))
            (foc-rv
              (ns-set ns lk (λ q → subst (λ c → isG1 c ≡ true) chk q))
              (funds-repl fu lk skip
                (slot-g0 (subst (λ c → isG1 c ≡ true) (sym chk) cg)
                         rz' (gone le)))
              fr)
        see (just (suc↑ _)) pv eqS =
          go (count (obj r) (refsOf (sys h (p ∷ []))) ≡ᵇ 1) refl eqS
          where
          go : (b : Bool) →
               (count (obj r) (refsOf (sys h (p ∷ []))) ≡ᵇ 1) ≡ b →
               useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
               Inv tight t
          go false cq eqG rewrite es | pv | chk | cg | cq =
            ⊥-elim (∅-just eqG)
          go true cq eqG
              rewrite es | pv | chk | cg | cq | sym (just-inj eqG) =
            inv (hp-snoc hp (pay-nat zero))
              (foc-rv (ns-set ns lk (λ ()))
                      (funds-repl fu lk skip (slot-ω refl)) fr)
        see (just (clo _ _)) pv eqS =
          go (count (obj r) (refsOf (sys h (p ∷ []))) ≡ᵇ 1) refl eqS
          where
          go : (b : Bool) →
               (count (obj r) (refsOf (sys h (p ∷ []))) ≡ᵇ 1) ≡ b →
               useVar h (p ∷ []) zero env k (toℕ x) (just r) ≡ just t →
               Inv tight t
          go false cq eqG rewrite es | pv | chk | cg | cq =
            ⊥-elim (∅-just eqG)
          go true cq eqG
              rewrite es | pv | chk | cg | cq | sym (just-inj eqG) =
            inv (hp-snoc hp (pay-nat zero))
              (foc-rv (ns-set ns lk (λ ()))
                      (funds-repl fu lk skip (slot-ω refl)) fr)

pres-beta : ∀ {n h p t ra rf env k} {gs : Vec Grade n} →
            HeapPay tight h →
            NoSharp gs env →
            Funds tight env (λ i → debtF i k) →
            Fr tight gs k (λ i → debtF i k) →
            beta h (p ∷ []) zero ra rf env k ≡ just t →
            Inv tight t
pres-beta {h = h} {p = p} {t = t} {ra = ra} {rf = rf} {env = env} {k = k}
          hp ns fu fr eq = opened (payloadAt h (obj rf)) refl eq
  where
  opened : (mv : Maybe Val) → payloadAt h (obj rf) ≡ mv →
           beta h (p ∷ []) zero ra rf env k ≡ just t → Inv tight t
  opened nothing pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (nat _)) pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (suc↑ _)) pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (clo _ (_ , gvar _))) pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (clo _ (_ , gtyp _))) pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (clo _ (_ , gpi _ _ _))) pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (clo _ (_ , gapp _ _))) pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (clo _ (_ , gze))) pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (clo _ (_ , gsu _))) pv eqB rewrite pv = ⊥-elim (∅-just eqB)
  opened (just (clo _ (_ , gmatch _ _ _))) pv eqB rewrite pv =
    ⊥-elim (∅-just eqB)
  opened (just (clo envC (_ , glam c _ body))) pv eqB =
    go (pay-at hp pv) (trans (sym (betaForm pv)) eqB)
    where
    -- `betaForm` rewrites in its own clause. A nested `rewrite` of
    -- the same proof is ill-typed: it abstracts `payloadAt` out of
    -- the proof's type.
    form : Bool → Bool → Maybe Sys
    form sharp ok =
      pass ok
        (pass (not sharp)
          (install h (p ∷ []) zero
            (ev body (regrade ra c ∷ envC) (bd env ∷ k))))
    betaForm :
      payloadAt h (obj rf) ≡ just (clo envC (_ , glam c _ body)) →
      beta h (p ∷ []) zero ra rf env k ≡
      form (anyG1 envC) (not (badG1 c (obj ra) (refsOf (sys h (p ∷ [])))))
    betaForm eq rewrite eq = refl
    head : (isG1 c ≡ true → occ zero body ≡ suc zero) →
           SlotOk tight (regrade ra c) (occ zero body)
    head oc' = slot (isG1 c) refl oc'
      where
      slot : (b : Bool) → isG1 c ≡ b →
             (isG1 c ≡ true → occ zero body ≡ suc zero) →
             SlotOk tight (regrade ra c) (occ zero body)
      slot false gc _ = slot-ω gc
      slot true gc oc'' =
        slot-g1 gc (isG1-sound c gc) (λ _ → oc'' gc)
          (subst (λ n → n ≤ suc zero) (sym (oc'' gc)) ≤-refl)
    go : Pay tight (clo envC (_ , glam c _ body)) →
         form (anyG1 envC) (not (badG1 c (obj ra) (refsOf (sys h (p ∷ []))))) ≡ just t →
         Inv tight t
    go (pay-clo {us = bus} ag ne dok oc tmB nsC) eqC =
      finish (not (badG1 c (obj ra) (refsOf (sys h (p ∷ []))))) refl
      where
      cleared :
        form false (not (badG1 c (obj ra) (refsOf (sys h (p ∷ []))))) ≡ just t
      cleared =
        subst (λ b →
            form b (not (badG1 c (obj ra) (refsOf (sys h (p ∷ []))))) ≡ just t)
          ag eqC
      finish : (b : Bool) →
               not (badG1 c (obj ra) (refsOf (sys h (p ∷ [])))) ≡ b →
               Inv tight t
      finish b bq =
        step b (subst (λ b' → form false b' ≡ just t) bq cleared)
        where
        step : (b : Bool) → form false b ≡ just t → Inv tight t
        step false eqF = ⊥-elim (∅-just eqF)
        step true eqF =
          subst (Inv tight) (just-inj eqF)
            (inv hp
              (foc-ev ne (bus , dok) tmB
                 (ns-cons (λ q → q) nsC)
                 (funds-cast (λ i → sym (+-identityʳ (occ i body)))
                    (fcons (head oc) (funds-ω envC ag)))
                 (fr-bd ns fu fr)))

pres-ret : ∀ {h p t r env k} →
           HeapPay tight h →
           Focus tight (rv r env k) →
           evalRet h (p ∷ []) zero r env k ≡ just t →
           Inv tight t
-- Case on the continuation in a helper, so `fu`'s debt is stated at
-- the constructed spine. `refl` refines the parent continuation.
pres-ret {h = h} {p = p} {t = t} {r = r} {env = env} {k = k}
         hp (foc-rv {gs = gs} ns fu fr) eq = go k fu fr refl eq
  where
  go : ∀ k' →
       Funds tight env (λ i → debtF i k') →
       Fr tight gs k' (λ i → debtF i k') →
       k ≡ k' →
       evalRet h (p ∷ []) zero r env k ≡ just t →
       Inv tight t
  go [] _ fr' refl eq' = none fr' eq'
    where
    none : Fr tight gs [] (λ i → debtF i []) →
           evalRet h (p ∷ []) zero r env [] ≡ just t →
           Inv tight t
    none fr-nil eqN = ⊥-elim (∅-just eqN)
  go (saved code ∷ xs) _ fr' refl _ = noSaved fr'
    where
    noSaved : Fr tight gs (saved code ∷ xs) (λ i → debtF i (saved code ∷ xs)) →
              Inv tight t
    noSaved ()
  go (mt e z s ∷ xs) _ fr' refl _ = noMatch fr'
    where
    noMatch : Fr tight gs (mt e z s ∷ xs) (λ i → debtF i (mt e z s ∷ xs)) →
              Inv tight t
    noMatch (fr-mt () _ _ _ _ _ _ _ _)
  go (ar a ∷ xs) fu' fr' refl eq' = pop fr' eq'
    where
    pop : Fr tight gs (ar a ∷ xs) (λ i → debtF i (ar a ∷ xs)) →
          evalRet h (p ∷ []) zero r env (ar a ∷ xs) ≡ just t →
          Inv tight t
    pop (fr-ar ne ok tm fr'') eqA =
      subst (Inv tight) (just-inj eqA)
        (inv {p = record p { ctl = ev a env (fn r ∷ xs) }} hp
           (foc-ev ne ok tm ns fu' (fr-fn fr'')))
  go (su ∷ xs) fu' fr' refl eq' = pop fr' eq'
    where
    pop : Fr tight gs (su ∷ xs) (λ i → debtF i (su ∷ xs)) →
          evalRet h (p ∷ []) zero r env (su ∷ xs) ≡ just t →
          Inv tight t
    pop (fr-su fr'') eqA =
      subst (Inv tight) (just-inj eqA)
        (inv {p = record p { ctl = rv (freshRef h gω) env xs }}
           (hp-snoc hp (pay-suc r))
           (foc-rv ns fu' fr''))
  go (bd env0 ∷ xs) _ fr' refl eq' = pop fr' eq'
    where
    pop : Fr tight gs (bd env0 ∷ xs) (λ i → debtF i (bd env0 ∷ xs)) →
          evalRet h (p ∷ []) zero r env (bd env0 ∷ xs) ≡ just t →
          Inv tight t
    pop (fr-bd ns0 fu0 fr'') eqA =
      subst (Inv tight) (just-inj eqA)
        (inv {p = record p { ctl = rv r env0 xs }} hp
           (foc-rv ns0 fu0 fr''))
  go (fn rf ∷ xs) fu' fr' refl eq' = pop fr' eq'
    where
    pop : Fr tight gs (fn rf ∷ xs) (λ i → debtF i (fn rf ∷ xs)) →
          evalRet h (p ∷ []) zero r env (fn rf ∷ xs) ≡ just t →
          Inv tight t
    pop (fr-fn fr'') eqA =
      pres-beta {h = h} {p = p} {t = t} {ra = r} {rf = rf}
                {env = env} {k = xs} {gs = gs}
                hp ns fu' fr'' eqA

pres-at : ∀ {h p t} i →
          HeapPay tight h → Focus tight (ctl p) →
          eval1 (sys h (p ∷ [])) i ≡ just t → Inv tight t
pres-at {h} {p} {t} zero hp foc eq = by (ctl p) eq refl
  where
  by : (c : Ctl) →
       eval1 (sys h (p ∷ [])) zero ≡ just t →
       ctl p ≡ c → Inv tight t
  by idle eq' cq rewrite cq = ⊥-elim (∅-just eq')
  by (pr _) eq' cq rewrite cq = ⊥-elim (∅-just eq')
  -- `e` is bound by this pattern, so its length is rigid before
  -- `foc-ev` is matched. Matching earlier leaves that length a meta
  -- and the split gets stuck.
  by (ev e env k) eq' cq rewrite cq = onFoc foc eq'
    where
    onFoc : Focus tight (ev e env k) →
            evalTm h (p ∷ []) zero e env k ≡ just t →
            Inv tight t
    onFoc (foc-ev ne ok tm ns fu fr) eqE = go e ne ok tm ns fu fr eqE
      where
      go : ∀ {n} (e' : GTm n) {Γ : GCtx n} →
           NoEsc (grades Γ) e' → OkRun Γ e' → MatchFree e' →
           NoSharp (grades Γ) env →
           Funds tight env (λ i → occ i e' + debtF i k) →
           Fr tight (grades Γ) k (λ i → debtF i k) →
           evalTm h (p ∷ []) zero e' env k ≡ just t →
           Inv tight t
      go (gmatch _ _ _) _ _ () _ _ _ _
      go (gvar x) _ _ _ ns' fu' fr' eqv = pres-var hp ns' fu' fr' eqv
      go (gapp f a) (ne-app nf na) (_ , dek) (mf-app mf ma) ns' fu' fr' eqv
        with split-app _ f a _ dek
      ... | fus , feq , (aus , aeq) rewrite sym (just-inj eqv) =
          inv hp (foc-ev nf (fus , feq) mf ns'
                   (funds-cast (λ i → +-assoc (occ i f) (occ i a) (debtF i k)) fu')
                   (fr-ar na (aus , aeq) ma fr'))
      go (gsu e') (ne-su ne') ok' (mf-su m) ns' fu' fr' eqv
        rewrite sym (just-inj eqv) =
        inv hp (foc-ev ne' ok' m ns' fu' (fr-su fr'))
      go gze ne-ze _ mf-ze ns' fu' fr' eqv rewrite sym (just-inj eqv) =
        inv (hp-snoc hp (pay-nat zero)) (foc-rv ns' fu' fr')
      go (gtyp _) (ne-typ _) _ mf-typ ns' fu' fr' eqv rewrite sym (just-inj eqv) =
        inv (hp-snoc hp (pay-nat zero)) (foc-rv ns' fu' fr')
      go (gpi _ _ _) (ne-pi _) _ (mf-pi _) ns' fu' fr' eqv
        rewrite sym (just-inj eqv) =
        inv (hp-snoc hp (pay-nat zero)) (foc-rv ns' fu' fr')
      go (glam c ty b) (ne-lam q nb) (us , dek) (mf-lam mb) ns' fu' fr' eqv
        with lam-body _ c ty b us dek
      ... | bus , beq rewrite ns-clear ns' q | sym (just-inj eqv) =
          inv (hp-snoc hp (pay-clo (ns-clear ns' q) nb beq
                             (λ g → g1-count _ c ty b us g dek) mb ns'))
              (foc-rv ns' (funds-clear ns' q) fr')
  by (rv r env k) eq' cq rewrite cq = pres-ret hp foc eq'
pres-at (suc _) _ _ eq = ⊥-elim (∅-just eq)

preserve : ∀ {s t} → Inv tight s → Step s t → Inv tight t
preserve (inv hp foc) (step-deref {i = i} {j = j} eq) =
  pres-deref {i = i} {j = j} hp foc eq
preserve (inv hp foc) (step-send {i = i} {j = j} {k = k} eq) =
  pres-send {si = i} {sj = j} {ri = k} hp foc eq
preserve (inv hp foc) (step-recv {i = i} eq) =
  pres-recv {i = i} hp foc eq
preserve (inv hp foc) (step-alloc {i = i} {g = g} {v = v} eq) =
  pres-alloc {i = i} {g = g} {v = v} hp foc eq
preserve (inv hp foc) (step-reuse {i = i} {j = j} {g = g} {v = v} eq) =
  pres-reuse {i = i} {j = j} {g = g} {v = v} hp foc eq
preserve (inv hp foc) (step-eval {i = i} eq) = pres-at i hp foc eq
preserve (inv {p = proc i st rs ib c} hp foc) step-collect =
  pres-collect {i = i} {st = st} {rs = rs} {ib = ib} {c = c} hp foc

start : (e : Checked) → NoEscape (term e) → MatchFree (term e) →
        Inv tight (lower e)
start e ne mf =
  inv hp-nil (foc-ev ne ([]ᵥ , ok e) mf ns-nil fnil fr-nil)

------------------------------------------------------------------------
-- `budget-adequate` is the trace invariant. It is stated for a
-- match-free program: `gmatch` is excluded, and only a checked grade
-- of g1 is tracked. Finite points above 1 and intervals are outside
-- it. `exact-exhausts` reads the invariant at a `bd` pop.
------------------------------------------------------------------------

budget-adequate : (e : Checked) {s : Sys} →
                  NoEscape (term e) → MatchFree (term e) →
                  Step* (lower e) s → Inv tight s
budget-adequate e ne mf tr = go (start e ne mf) tr
  where
  go : ∀ {a b} → Inv tight a → Step* a b → Inv tight b
  go i step-done = i
  go i (step-more st rest) = go (preserve i st) rest

exact-exhausts : ∀ (e : Checked) {s h p v env env0 k i r} →
                 NoEscape (term e) → MatchFree (term e) →
                 Step* (lower e) s →
                 s ≡ sys h (p ∷ []) →
                 ctl p ≡ rv v env (bd env0 ∷ k) →
                 lookup env i ≡ just r →
                 isG1 (checked r) ≡ true →
                 residual r ≡ g0
exact-exhausts e {h = h} {p = p} {v = v} {env = env} {env0 = env0} {k = k}
               ne mf tr refl refl lk g =
  exit-g1 (pick (budget-adequate e ne mf tr)) lk g
  where
  pick : Inv tight (sys h (p ∷ [])) →
         Focus tight (rv v env (bd env0 ∷ k))
  pick (inv _ foc) = foc

budget-g1 : ∀ (e : Checked) {s h p n env k r} {x : Fin n} →
            NoEscape (term e) → MatchFree (term e) →
            Step* (lower e) s →
            s ≡ sys h (p ∷ []) →
            ctl p ≡ ev (gvar x) env k →
            lookup env (toℕ x) ≡ just r →
            isG1 (checked r) ≡ true →
            residual r ≡ g1
budget-g1 e {h = h} {p = p} {env = env} {k = k} {x = x}
          ne mf tr refl refl lk g =
  g1-ready (pick (budget-adequate e ne mf tr)) lk g
  where
  pick : Inv tight (sys h (p ∷ [])) → Focus tight (ev (gvar x) env k)
  pick (inv _ foc) = foc
