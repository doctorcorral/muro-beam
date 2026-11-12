------------------------------------------------------------------------
-- Adequacy of the checker and of an empty live set.
--
-- `decide-sound` is binder discharge. The sentence "each free `us[x]`
-- satisfies `sat` of `Γ[x]`" is false for an open term: `decide` on
-- `gvar` does not consult `Γ`.
-- `decide run (gp g0 g0 ∷ []) (gvar fzero)` returns computational
-- count 1, and `sat g0 (finᶜ 1)` is false. A closed `Uses 0` is empty,
-- so that reading says nothing there either. What `under` checks, and
-- what this theorem records, is each binder the judgment accepts.
-- `co` and `ty` are the head of the vector `decide` returns for that
-- body (`sp co ty ∷ _`), so `sat` is about those uses, not about counts
-- chosen beside the derivation. Spec mode forgets the computational
-- component. A `gpi` is checked in spec mode, including when the
-- surrounding judgment is run. `¬discharged-ghost` is the old hand-built
-- inhabitant: both counts zero on `glam g0 g0 (gvar fzero)`. The body
-- checks as one computational use, so that derivation is empty.
--
-- `done-collect-empty` does not follow a trace of `eval1`. `collect`
-- marks from `liveRefs` only, and a false bit never marks a child, so
-- an empty live set frees every slot even when edges exist. Pid 0
-- finished, with an empty environment, ether, root list, and inbox,
-- is that state (`done-pid0`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Adequacy where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation.Core using (¬_)
open import Data.Fin.Base using (Fin) renaming (zero to fzero)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; Σ)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (Mode; run; spec; evid; Result; fail; _>>=_; _>>_)
  renaming (ok to okR)
open import Muro.Grade using
  ( Grade; g0; Count; finᶜ; many; Spent; sp; Pair; gp
  ; Uses; GCtx; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch
  ; sat; decide; under; hold; checkCount; checkType
  ; predPair; pcomp; ptype; refuse; typeRefuse )

open import MuroBeam.Heap using (Obj; cell; nat; free; payload; kids)
open import MuroBeam.Process using
  ( Sys; sys; heap; Proc; proc; PState; pr; liveRefs )
open import MuroBeam.PSyntax using (done) renaming (go to pgo)
open import MuroBeam.Collect using
  ( go; lookupB; markIf; seed; seedFrom; apply; collect )

------------------------------------------------------------------------
-- What a successful `decide` guarantees about binders.
------------------------------------------------------------------------

data Discharged (m : Mode) {n} (Γ : GCtx n) : GTm n → Set where
  ds-var : (x : Fin n) → Discharged m Γ (gvar x)
  ds-typ : (x : Fin n) → Discharged m Γ (gtyp x)
  ds-ze  : Discharged m Γ gze
  ds-su  : ∀ {e} → Discharged m Γ e → Discharged m Γ (gsu e)
  ds-app : ∀ {f a} → Discharged m Γ f → Discharged m Γ a →
           Discharged m Γ (gapp f a)
  ds-pi  : ∀ {c t b us} (co ty : Count) →
           decide spec (gp c t ∷ Γ) b ≡ okR (sp co ty ∷ us) →
           sat t ty ≡ true →
           Discharged spec (gp c t ∷ Γ) b →
           Discharged m Γ (gpi c t b)
  ds-lam : ∀ {c t b us} (co ty : Count) →
           decide m (gp c t ∷ Γ) b ≡ okR (sp co ty ∷ us) →
           sat t ty ≡ true →
           (m ≡ run ⊎ m ≡ evid → sat c co ≡ true) →
           Discharged m (gp c t ∷ Γ) b →
           Discharged m Γ (glam c t b)
  ds-mat : ∀ {e z s us} (co ty : Count) →
           decide m (predPair Γ e ∷ Γ) s ≡ okR (sp co ty ∷ us) →
           sat (ptype (predPair Γ e)) ty ≡ true →
           (m ≡ run ⊎ m ≡ evid → sat (pcomp (predPair Γ e)) co ≡ true) →
           Discharged m Γ e →
           Discharged m Γ z →
           Discharged m (predPair Γ e ∷ Γ) s →
           Discharged m Γ (gmatch e z s)

private

  fail≢ok : ∀ {A : Set} {x : A} {msg : String} → fail msg ≡ okR x → ⊥
  fail≢ok ()

  ok-inj : ∀ {A : Set} {x y : A} → okR x ≡ okR y → x ≡ y
  ok-inj refl = refl

  check-ok : ∀ {A : Set} (b : Bool) (x : A) (msg : String) {y : A} →
             (if b then okR x else fail msg) ≡ okR y → b ≡ true × x ≡ y
  check-ok true  x _ refl = refl , refl
  check-ok false _ _ ()

  bind-split : ∀ {A B : Set} (r : Result A) (f : A → Result B) {b : B} →
               (r >>= f) ≡ okR b → Σ A (λ a → r ≡ okR a × f a ≡ okR b)
  bind-split (okR a) f eq = a , refl , eq
  bind-split (fail _) _ ()

  >>-split : ∀ {A B : Set} (r : Result A) (s : Result B) {b : B} →
             (r >> s) ≡ okR b → Σ A (λ a → r ≡ okR a × s ≡ okR b)
  >>-split r s eq = bind-split r (λ _ → s) eq

  hold-run : ∀ c t co ty →
             hold run c t (sp co ty) ≡ okR tt →
             sat c co ≡ true × sat t ty ≡ true
  hold-run c t co ty eq with >>-split (checkCount run c co) (checkType t ty) eq
  ... | _ , cok , tok with check-ok (sat c co) tt (refuse c co) cok
  ... | sc , _ with check-ok (sat t ty) tt (typeRefuse t ty) tok
  ... | st , _ = sc , st

  hold-evid : ∀ c t co ty →
              hold evid c t (sp co ty) ≡ okR tt →
              sat c co ≡ true × sat t ty ≡ true
  hold-evid c t co ty eq with >>-split (checkCount evid c co) (checkType t ty) eq
  ... | _ , cok , tok with check-ok (sat c co) tt (refuse c co) cok
  ... | sc , _ with check-ok (sat t ty) tt (typeRefuse t ty) tok
  ... | st , _ = sc , st

  under-run : ∀ {n} c t co ty (rest out : Uses n) →
              under run c t (sp co ty ∷ rest) ≡ okR out →
              sat c co ≡ true × sat t ty ≡ true × rest ≡ out
  under-run c t co ty rest out eq
    with >>-split (hold run c t (sp co ty)) (okR rest) eq
  ... | _ , hok , rok with hold-run c t co ty hok
  ... | sc , st = sc , st , ok-inj rok

  under-evid : ∀ {n} c t co ty (rest out : Uses n) →
               under evid c t (sp co ty ∷ rest) ≡ okR out →
               sat c co ≡ true × sat t ty ≡ true × rest ≡ out
  under-evid c t co ty rest out eq
    with >>-split (hold evid c t (sp co ty)) (okR rest) eq
  ... | _ , hok , rok with hold-evid c t co ty hok
  ... | sc , st = sc , st , ok-inj rok

  under-spec : ∀ {n} c t co ty (rest out : Uses n) →
               under spec c t (sp co ty ∷ rest) ≡ okR out →
               sat t ty ≡ true × rest ≡ out
  under-spec c t co ty rest out eq
    with >>-split (checkType t ty) (okR rest) eq
  ... | _ , tok , rok with check-ok (sat t ty) tt (typeRefuse t ty) tok
  ... | st , _ = st , ok-inj rok

  CompOk : Mode → Grade → Count → Set
  CompOk m c co = m ≡ run ⊎ m ≡ evid → sat c co ≡ true

  under-facts : ∀ {n} m c t co ty (rest out : Uses n) →
                under m c t (sp co ty ∷ rest) ≡ okR out →
                sat t ty ≡ true × CompOk m c co
  under-facts spec c t co ty rest out eq with under-spec c t co ty rest out eq
  ... | st , _ = st , λ { (inj₁ ()) ; (inj₂ ()) }
  under-facts run c t co ty rest out eq with under-run c t co ty rest out eq
  ... | sc , st , _ = st , λ { (inj₁ refl) → sc ; (inj₂ ()) }
  under-facts evid c t co ty rest out eq with under-evid c t co ty rest out eq
  ... | sc , st , _ = st , λ { (inj₁ ()) ; (inj₂ refl) → sc }

discharge : ∀ {n} m (Γ : GCtx n) e us →
            decide m Γ e ≡ okR us → Discharged m Γ e
discharge m Γ (gvar x) _ _ = ds-var x
discharge m Γ (gtyp x) _ _ = ds-typ x
discharge m Γ gze _ _ = ds-ze
discharge m Γ (gsu e) us eq = ds-su (discharge m Γ e us eq)
discharge m Γ (gapp f a) out eq with decide m Γ f in fq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR fu with decide m Γ a in aq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR au = ds-app (discharge m Γ f fu fq) (discharge m Γ a au aq)
discharge m Γ (glam c t b) out eq with decide m (gp c t ∷ Γ) b in bq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR us = fromUs us bq eq
  where
  fromUs : (us : Uses (suc _)) →
           decide m (gp c t ∷ Γ) b ≡ okR us →
           under m c t us ≡ okR out →
           Discharged m Γ (glam c t b)
  fromUs (sp co ty ∷ rest) bq' uq with under-facts m c t co ty rest out uq
  ... | st , sc =
    ds-lam co ty bq' st sc
      (discharge m (gp c t ∷ Γ) b (sp co ty ∷ rest) bq')
discharge m Γ (gpi c t b) out eq with decide spec (gp c t ∷ Γ) b in bq
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR us = fromPi us bq eq
  where
  fromPi : (us : Uses (suc _)) →
           decide spec (gp c t ∷ Γ) b ≡ okR us →
           under spec c t us ≡ okR out →
           Discharged m Γ (gpi c t b)
  fromPi (sp co ty ∷ rest) bq' uq with under-spec c t co ty rest out uq
  ... | st , _ =
    ds-pi co ty bq' st
      (discharge spec (gp c t ∷ Γ) b (sp co ty ∷ rest) bq')
discharge m Γ (gmatch e z s) out eq with decide m Γ e in eqe
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR eu with decide m Γ z in eqz
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR zu with decide m (predPair Γ e ∷ Γ) s in eqs
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR su with under m (pcomp (predPair Γ e)) (ptype (predPair Γ e)) su in equ
... | fail _ = ⊥-elim (fail≢ok eq)
... | okR srest =
    fromMatch su equ eqs
      (discharge m Γ e eu eqe)
      (discharge m Γ z zu eqz)
      (discharge m (predPair Γ e ∷ Γ) s su eqs)
  where
  fromMatch : (su : Uses (suc _)) →
              under m (pcomp (predPair Γ e)) (ptype (predPair Γ e)) su ≡ okR srest →
              decide m (predPair Γ e ∷ Γ) s ≡ okR su →
              Discharged m Γ e → Discharged m Γ z →
              Discharged m (predPair Γ e ∷ Γ) s →
              Discharged m Γ (gmatch e z s)
  fromMatch (sp co ty ∷ rest) uq sq de dz ds
    with under-facts m (pcomp (predPair Γ e)) (ptype (predPair Γ e)) co ty rest srest uq
  ... | st , sc = ds-mat co ty sq st sc de dz ds

decide-sound : ∀ {n} (Γ : GCtx n) e us →
               decide run Γ e ≡ okR us → Discharged run Γ e
decide-sound Γ e us eq = discharge run Γ e us eq

-- The body uses the grade-0 binder once. `decide` refuses the λ.
-- `Discharged` refuses it too: `ds-lam` must quote that vector, and
-- `sat g0` rejects the computational count. A zero-count premise
-- contradicts the same equality.
ghost-body-once :
  decide run (gp g0 g0 ∷ []) (gvar fzero)
    ≡ okR (sp (finᶜ (suc zero)) (finᶜ zero) ∷ [])
ghost-body-once = refl

ghost-decide-fails :
  decide run [] (glam g0 g0 (gvar fzero))
    ≡ fail "erased variable used computationally"
ghost-decide-fails = refl

¬discharged-ghost : ¬ Discharged run [] (glam g0 g0 (gvar fzero))
¬discharged-ghost (ds-lam co ty eq _ sc _)
  with ok-inj (trans (sym ghost-body-once) eq)
... | refl = bad (sc (inj₁ refl))
  where
  bad : false ≡ true → ⊥
  bad ()

-- A point g0 accepts only the count zero. This is the static half of
-- "a run binder of grade 0 is not a computational use".
sat-g0-zero : ∀ k → sat g0 k ≡ true → k ≡ finᶜ zero
sat-g0-zero (finᶜ zero) _ = refl
sat-g0-zero (finᶜ (suc _)) ()
sat-g0-zero many ()

------------------------------------------------------------------------
-- An empty live set frees every heap slot.
------------------------------------------------------------------------

data AllFree : List Obj → Set where
  af-nil  : AllFree []
  af-cons : ∀ {os} → AllFree os → AllFree (cell (nat zero) free ∷ os)

data Quiet : List Bool → Set where
  qnil  : Quiet []
  qcons : ∀ {bs} → Quiet bs → Quiet (false ∷ bs)

lookup-quiet : ∀ bs i → Quiet bs → lookupB bs i ≡ false
lookup-quiet []            _       _        = refl
lookup-quiet (false ∷ _)   zero    _        = refl
lookup-quiet (false ∷ bs)  (suc i) (qcons q) = lookup-quiet bs i q

markIf-false : ∀ i rs bs → markIf false i rs bs ≡ bs
markIf-false _ _ _ = refl

go-quiet : ∀ os i bs → Quiet bs → Quiet (go os i bs)
go-quiet []       _ _  q = q
go-quiet (o ∷ os) i bs q =
  subst Quiet (sym step) marked
  where
  tail = go os (suc i) bs
  q'   = go-quiet os (suc i) bs q
  marked : Quiet (markIf false i (kids (payload o)) tail)
  marked = subst Quiet (sym (markIf-false i (kids (payload o)) tail)) q'
  step : markIf (lookupB tail i) i (kids (payload o)) tail
       ≡ markIf false i (kids (payload o)) tail
  step = cong (λ b → markIf b i (kids (payload o)) tail)
              (lookup-quiet tail i q')

seedFrom-quiet : ∀ b n → Quiet (seedFrom [] b n)
seedFrom-quiet _ zero    = qnil
seedFrom-quiet b (suc n) = qcons (seedFrom-quiet (suc b) n)

apply-quiet : ∀ bs os → Quiet bs → AllFree (apply bs os)
apply-quiet []           []       _        = af-nil
apply-quiet []           (_ ∷ os) _        = af-cons (apply-quiet [] os qnil)
apply-quiet (false ∷ _)  []       _        = af-nil
apply-quiet (false ∷ bs) (_ ∷ os) (qcons q) = af-cons (apply-quiet bs os q)

done-collect-empty : ∀ s → liveRefs s ≡ [] → AllFree (heap (collect s))
done-collect-empty s eq rewrite eq =
  apply-quiet (go (heap s) zero (seed [] n)) (heap s)
              (go-quiet (heap s) zero (seed [] n) (seedFrom-quiet zero n))
  where
  n = length (heap s)

done-pid0 : ∀ (st : PState) (h : List Obj) →
            AllFree (heap (collect
              (sys h (proc zero st [] [] (pr (pgo (done {0}) [] [] [] [])) ∷ []))))
done-pid0 st h =
  done-collect-empty
    (sys h (proc zero st [] [] (pr (pgo (done {0}) [] [] [] [])) ∷ []))
    refl
