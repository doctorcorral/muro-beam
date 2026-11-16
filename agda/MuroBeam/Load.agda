------------------------------------------------------------------------
-- Load an image. Parse, then demand format 1 and this tree's
-- boundary version, then re-run `checkP`.
--
-- `lowerP` (in `MuroBeam.PTm`) is the initial system. `lowerP-wf`
-- and `lowerP-safe` apply to anything `load` accepts. The emitter
-- is outside the TCB for those two.
--
-- Non-consequences of `load`:
-- `lower-safe` (pure `lower` of a `Checked`),
-- `budget-adequate` (needs `NoEscape` and `MatchFree`),
-- `no-stray-reply` (needs `ReplyDone`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Load where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.String.Base using (String)
open import Data.Vec.Base using ([])
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Result; ok; fail)
open import Muro.Grade using (Uses)

open import MuroBeam.Boundary using (boundary-version)
open import MuroBeam.Image using (Image; format; boundary; term; format-version)
open import MuroBeam.Parse using (parseR)
open import MuroBeam.PSyntax using (PTm; seq; done)
open import MuroBeam.PTm using (CheckedP; checkedP; checkP)

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ (suc m) (suc n) = eqℕ m n
eqℕ _       _       = false

-- `Uses 0` is an empty vector, so the only success is `ok []`.
admit : (p : PTm 0) (r : Result (Uses 0)) → checkP [] p ≡ r → Result CheckedP
admit _ (fail e) _  = fail e
admit p (ok []) eq  = ok (checkedP p eq)

load : String → Result CheckedP
load s with parseR s
... | fail e = fail e
... | ok i with eqℕ (format i) format-version
... | false = fail "bad version"
... | true with eqℕ (boundary i) boundary-version
... | false = fail "bad boundary version"
... | true = admit (seq (term i) (done {1})) (checkP [] (seq (term i) (done {1}))) refl

-- The equation is `CheckedP.okp`. It holds for every `CheckedP`,
-- and this proof does not use `load s ≡ ok p`. The real guarantee
-- is the return type: `admit` builds `checkedP` only after `checkP`
-- has returned `ok []`.
load-sound : ∀ s p → load s ≡ ok p → checkP [] (CheckedP.prog p) ≡ ok []
load-sound _ p _ = CheckedP.okp p
