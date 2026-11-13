------------------------------------------------------------------------
-- Trace events. The same fields as book/trace.muro.
--
-- alloc, deref, send, eval1, collect, and the process steps do not
-- build these. MuroBeam.Emit calls those operations and pairs the
-- resulting system with the events of that one step.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Event where

open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)

open import Muro.Grade using (Grade)

open import MuroBeam.Grade using (Kind)
open import MuroBeam.Heap using (Ref)

data Event : Set where
  tr-alloc   : ℕ → Grade → Event
  tr-spend   : ℕ → Grade → Grade → Event
  tr-send    : ℕ → ℕ → Ref → Kind → Event
  tr-recv    : ℕ → Ref → Event
  tr-spawn   : ℕ → ℕ → Event
  tr-step    : ℕ → Event
  tr-collect : List ℕ → Event
