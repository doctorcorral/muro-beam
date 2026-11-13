------------------------------------------------------------------------
-- The closed §2B counterexample, and the one-process system a closed
-- term lowers to.
--
-- One definition of the term. Example re-exports `cex` and checks it.
-- Conform prints `lowerTm` of it. This module does not import Unique,
-- Source, Lower, Example, PExample, Stray, or PWf.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Cex where

open import Data.Fin.Base using () renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([] ; _∷_)
open import Data.Nat.Base using (zero)

open import Muro.Grade using
  ( g0; g1; gω; aff
  ; GTm; gvar; glam; gapp )

open import MuroBeam.Process using (Sys; sys; proc; ready; ev)

-- λ(g1) x. (λ(gω) f. f f) (λ(aff) _. x)
cex : GTm zero
cex =
  glam g1 g0
    (gapp
      (glam gω g0 (gapp (gvar fzero) (gvar fzero)))
      (glam aff g0 (gvar (fsuc fzero))))

-- One process, pid 0, empty heap, the term in an empty environment.
lowerTm : ∀ {n} → GTm n → Sys
lowerTm t = sys [] (proc zero ready [] [] (ev t [] []) ∷ [])
