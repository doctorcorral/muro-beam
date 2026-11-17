------------------------------------------------------------------------
-- Load an image. Parse, then demand format 1 or 2 and this tree's
-- boundary version, then re-run `checkP` on the definitions and the
-- entry. A definition is checked once there. `gref` is checked again
-- only as a use, at grade ω, by that same pass.
--
-- `lowerP` (in `MuroBeam.PTm`) is the initial system. `lowerP-wf`
-- and `lowerP-safe` apply to anything `load` accepts. The emitter
-- is outside the TCB for those two.
--
-- Non-consequences of `load`:
-- `lower-safe` is not on the `lowerP` path. It is `Step* (lower e)`
-- for a pure `Checked`.
-- `budget-adequate` is
-- `(e : Checked) {s : Sys} → NoEscape (term e) → MatchFree (term e) →
--  Step* (lower e) s → Inv tight s`
-- (`MuroBeam.Budget`). `checkP` on `seq` runs
-- `boundaryOk (inB? (comps Γ) e)`. `load` calls that at `Γ = []` on
-- the entry, so a success implies `InBoundary` of the entry, and
-- `inBoundary→noEscape` gives `NoEscape`. What is missing is
-- `MatchFree` (`match.mbi` loads and contains `gmatch`; `MatchFree`
-- has no `gmatch` clause) and the theorem's path: pure `Checked` /
-- `lower` / `Step*`, not `CheckedP` / `lowerP` / `PStep*`.
-- `no-stray-reply` (needs `ReplyDone`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Load where

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.String.Base using (String)
open import Data.Vec.Base using ([])
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Result; ok; fail)
open import Muro.Grade using (Uses)

open import MuroBeam.Boundary using (boundary-version)
open import MuroBeam.Image using
  (Image; format; boundary; term; defs; format-version)
open import MuroBeam.Parse using (parseR)
open import MuroBeam.PSyntax using (PTm; seq; done)
open import MuroBeam.PTm using (CheckedP; checkedP; checkP)

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ (suc m) (suc n) = eqℕ m n
eqℕ _       _       = false

-- v1 is the empty-defs file muro emits. v2 carries a defs section.
-- Any other number is refused. The printer reprints the number it read.
versionOk : ℕ → Bool
versionOk n = eqℕ n format-version ∨ eqℕ n 2

-- `Uses 0` is an empty vector, so the only success is `ok []`.
admit : (p : PTm 0) (r : Result (Uses 0)) → checkP [] p ≡ r → Result CheckedP
admit _ (fail e) _  = fail e
admit p (ok []) eq  = ok (checkedP p eq)

load : String → Result CheckedP
load s with parseR s
... | fail e = fail e
... | ok i with versionOk (format i)
... | false = fail "bad version"
... | true with eqℕ (boundary i) boundary-version
... | false = fail "bad boundary version"
... | true = admit (seq (defs i) (term i) (done {1}))
                 (checkP [] (seq (defs i) (term i) (done {1}))) refl

-- The equation is `CheckedP.okp`. It holds for every `CheckedP`,
-- and this proof does not use `load s ≡ ok p`. The real guarantee
-- is the return type: `admit` builds `checkedP` only after `checkP`
-- has returned `ok []`.
load-sound : ∀ s p → load s ≡ ok p → checkP [] (CheckedP.prog p) ≡ ok []
load-sound _ p _ = CheckedP.okp p
