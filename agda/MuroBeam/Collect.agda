------------------------------------------------------------------------
-- Total collection. A slot stays live exactly when some root or in-flight
-- message still has a residual other than the point g0. ω and intervals
-- are not that point, so those roots are kept alive. There is no tracing
-- walk: objects do not contain pointers.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Collect where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; subst)

open import Muro.Base using (Mode; run)
open import Muro.Grade using (Grade; g0)
open import MuroBeam.Grade using (isZeroGrade)
open import MuroBeam.Heap using (Obj; cell; Status; live; free; Ref; residual; obj; status; payload)
open import MuroBeam.Lib using
  ( lookup; ≡ᵇ-refl; ≡ᵇ-cong; ∨-trueʳ; plus; plus-suc; plus-zero )
open import MuroBeam.Process using
  ( Proc; proc; PState; Msg; msg; Sys; sys; heap; procs; roots; inbox
  ; refsOf; AllInv; refs-inv
  ; deref; send; recv; alloc; reuse )

open Obj public

------------------------------------------------------------------------
-- Keepers: residual is not the point g0.
------------------------------------------------------------------------

anyKeeper : ℕ → List Ref → Bool
anyKeeper i []       = false
anyKeeper i (r ∷ rs) =
  ((obj r ≡ᵇ i) ∧ not (isZeroGrade (residual r))) ∨ anyKeeper i rs

data Reach (i : ℕ) : List Ref → Set where
  here  : ∀ {r rs} → obj r ≡ i → isZeroGrade (residual r) ≡ false → Reach i (r ∷ rs)
  there : ∀ {r rs} → Reach i rs → Reach i (r ∷ rs)

reach→any : ∀ {i rs} → Reach i rs → anyKeeper i rs ≡ true
reach→any {i} (here {r} eq z)
  rewrite trans (≡ᵇ-cong (obj r) i i eq) (≡ᵇ-refl i) | z = refl
reach→any (there p) rewrite reach→any p = ∨-trueʳ _

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
filterMsg []             = []
filterMsg (msg r ∷ ms)   = keepMsg (isZeroGrade (residual r)) r (filterMsg ms)

clean : Proc → Proc
clean p = record p { roots = filterKeep (roots p) ; inbox = filterMsg (inbox p) }

markB : Bool → Obj → Obj
markB true  o = record o { status = live }
markB false _ = cell zero free

mark : List Ref → ℕ → Obj → Obj
mark rs i o = markB (anyKeeper i rs) o

walk : List Ref → ℕ → List Obj → List Obj
walk rs n []       = []
walk rs n (o ∷ os) = mark rs n o ∷ walk rs (suc n) os

collect : Sys → Sys
collect s = sys (walk (refsOf s) zero (heap s)) (map clean (procs s))

lookup-walk : ∀ rs n os i o →
  lookup os i ≡ just o →
  lookup (walk rs n os) i ≡ just (mark rs (plus i n) o)
lookup-walk rs n []       i o ()
lookup-walk rs n (_ ∷ os) zero o refl = refl
lookup-walk rs n (x ∷ os) (suc i) o eq rewrite sym (plus-suc i n) =
  lookup-walk rs (suc n) os i o eq

mark-live : ∀ {rs i o} → anyKeeper i rs ≡ true →
  mark rs i o ≡ record o { status = live }
mark-live eq rewrite eq = refl

mark-free : ∀ {rs i o} → anyKeeper i rs ≡ false →
  mark rs i o ≡ cell zero free
mark-free eq rewrite eq = refl

-- collect never frees an object reachable from a residual that is not g0.
collect-safe : ∀ s i → Reach i (refsOf s) → ∀ o →
  lookup (heap s) i ≡ just o →
  lookup (heap (collect s)) i ≡ just (record o { status = live })
collect-safe s i reach o eq = kept (at eq)
  where
  at : lookup (heap s) i ≡ just o →
       lookup (heap (collect s)) i ≡ just (mark (refsOf s) i o)
  at eq′ =
    subst (λ n → lookup (walk (refsOf s) zero (heap s)) i ≡ just (mark (refsOf s) n o))
          (plus-zero i)
          (lookup-walk (refsOf s) zero (heap s) i o eq′)

  kept : lookup (heap (collect s)) i ≡ just (mark (refsOf s) i o) →
         lookup (heap (collect s)) i ≡ just (record o { status = live })
  kept p rewrite reach→any reach = p

-- A slot with no positive residual reference is freed.
collect-frees-zero : ∀ s i o →
  lookup (heap s) i ≡ just o →
  anyKeeper i (refsOf s) ≡ false →
  lookup (heap (collect s)) i ≡ just (cell zero free)
collect-frees-zero s i o eq nk = dropped nk (at eq)
  where
  at : lookup (heap s) i ≡ just o →
       lookup (heap (collect s)) i ≡ just (mark (refsOf s) i o)
  at eq′ =
    subst (λ n → lookup (walk (refsOf s) zero (heap s)) i ≡ just (mark (refsOf s) n o))
          (plus-zero i)
          (lookup-walk (refsOf s) zero (heap s) i o eq′)

  dropped : anyKeeper i (refsOf s) ≡ false →
            lookup (heap (collect s)) i ≡ just (mark (refsOf s) i o) →
            lookup (heap (collect s)) i ≡ just (cell zero free)
  dropped eqk p rewrite eqk = p

-- Totality is the type `collect : Sys → Sys` under --safe.
-- This packages that fact under the name the design uses.
data Collected (s : Sys) : Set where
  collected : (t : Sys) → t ≡ collect s → Collected s

collect-total : ∀ s → Collected s
collect-total s = collected (collect s) refl

------------------------------------------------------------------------
-- One scheduling step. Some process, or the collector. No fairness.
------------------------------------------------------------------------

data Step : Sys → Sys → Set where
  step-deref   : ∀ {s i j t} → deref run s i j ≡ just t → Step s t
  step-send    : ∀ {s i j k t} → send s i j k ≡ just t → Step s t
  step-recv    : ∀ {s i t} → recv s i ≡ just t → Step s t
  step-alloc   : ∀ {s i g v t} → alloc s i g v ≡ just t → Step s t
  step-reuse   : ∀ {s i j g v t} → reuse s i j g v ≡ just t → Step s t
  step-collect : ∀ {s} → Step s (collect s)

-- Every reference after a step still satisfies residual ≤ᵍ checked.
residual-inv-step : ∀ {s t} → Step s t → AllInv (refsOf t)
residual-inv-step _ = refs-inv _
