------------------------------------------------------------------------
-- A closed run-mode term that muro's grade checker accepts.
--
-- `decide-sound`, `NoEscape`, and `noEscape?` are v1c. The `ok` field
-- is the checker's own `refl`; this module does not re-prove it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Source where

open import Data.Vec.Base using ([])
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import Muro.Base using (run) renaming (ok to okR)
open import Muro.Grade using (GTm; decide)

record Checked : Set where
  field
    term : GTm 0
    ok   : decide run [] term ≡ okR []

open Checked public
