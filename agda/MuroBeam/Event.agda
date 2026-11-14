------------------------------------------------------------------------
-- Trace events. The same fields as book/trace.muro.
--
-- alloc, deref, send, eval1, collect, and the process steps do not
-- build these. MuroBeam.Emit calls those operations and pairs the
-- resulting system with the events of that one step.
--
-- tr-down is peer death, observed by one process about another.
-- It is not a protocol tag. codeDead / deadAt stay consumption
-- marks on Code. The reason is the raw reason the observer stores.
-- This model does not rewrite a kill into a second spelling.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Event where

open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)

open import Muro.Grade using (Grade)

open import MuroBeam.Grade using (Kind)
open import MuroBeam.Heap using (Ref)

-- Observed death reason. Not a tag in Code's dead list.
data Why : Set where
  killed  : Why
  crash   : Why
  normal  : Why
  abandon : Why

data Event : Set where
  tr-alloc   : ℕ → Grade → Event
  tr-spend   : ℕ → Grade → Grade → Event
  tr-send    : ℕ → ℕ → Ref → Kind → Event
  tr-recv    : ℕ → Ref → Event
  tr-spawn   : ℕ → ℕ → Event
  tr-step    : ℕ → Event
  tr-collect : List ℕ → Event
  tr-down    : ℕ → ℕ → Why → Event
