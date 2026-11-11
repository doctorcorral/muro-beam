------------------------------------------------------------------------
-- Lower a checked closed term to one idle-heap process and keep the
-- v0 invariants along every finite trace.
--
-- `PTm`, `checkP`, and `lowerP` are v1b. `NoEscape`, `decide-sound`,
-- `budget-adequate`, `exact-exhausts`, `done-collect-empty`,
-- `MuroBeam.Ref`, and `lower-sim` are v1c.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Lower where

open import Data.List.Base using ([] ; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (zero)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; subst)

open import Muro.Base using (run)
open import Muro.Grade using (g0)

open import MuroBeam.Grade using (Kept; kept-g0)
open import MuroBeam.Heap using
  ( Ref; checked; residual; kept; spendRef; spendRef-zero
  ; Bound; bnil; Grade1Unique; uniq-nil; Ordered; ordered-nil )
open import MuroBeam.Process using
  ( Sys; sys; heap; Proc; proc; ready; Ctl; ev
  ; refsOf; rootAt; deref; AllInv
  ; grade0-not-dereferenced; residual-inv-refs )
open import MuroBeam.Collect using (Step)
open import MuroBeam.Source using (Checked; term)
open import MuroBeam.Unique using (WF; step-preserves-grade1)

------------------------------------------------------------------------
-- One process, pid 0, empty heap, the term in an empty environment.
------------------------------------------------------------------------

lower : Checked → Sys
lower e =
  sys []
    (proc zero ready [] [] (ev (term e) [] []) ∷ [])

lower-wf : ∀ e → WF (lower e)
lower-wf e = bnil , uniq-nil

lower-ordered : ∀ e → Ordered (heap (lower e))
lower-ordered e = ordered-nil

------------------------------------------------------------------------
-- Finite traces. Evaluation may diverge, so this is not a function.
------------------------------------------------------------------------

data Step* : Sys → Sys → Set where
  step-done : ∀ {s} → Step* s s
  step-more : ∀ {s t u} → Step s t → Step* t u → Step* s u

lower-safe : ∀ {e s} → Step* (lower e) s → WF s × AllInv (refsOf s)
lower-safe {e} {s} tr = keep (lower e) tr (lower-wf e) , residual-inv-refs s
  where
  keep : ∀ a {b} → Step* a b → WF a → WF b
  keep a step-done wf = wf
  keep a (step-more st rest) wf = keep _ rest (step-preserves-grade1 st wf)

------------------------------------------------------------------------
-- A checked grade of g0 forces a g0 residual (`Kept`), and `spend`
-- refuses it. `deref` and a `gvar` step both go through `spendRef`,
-- so neither is a step. `gtyp` and `gpi` never call `spend`.
-- Connecting a checker `g0` binder to a trace is `decide-sound` (v1c).
------------------------------------------------------------------------

lower-g0-never-deref : ∀ s i j r →
  rootAt s i j ≡ just r →
  checked r ≡ g0 →
  residual r ≡ g0 × spendRef r ≡ nothing × deref run s i j ≡ nothing
lower-g0-never-deref s i j r lk cg =
  let rz = kept-g0 (subst (λ c → Kept (residual r) c) cg (kept r))
  in rz , spendRef-zero r rz , grade0-not-dereferenced s i j r lk rz
