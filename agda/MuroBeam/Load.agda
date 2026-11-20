------------------------------------------------------------------------
-- Load an image. Parse, then demand format 1 or 2 and this tree's
-- boundary version, then re-run `checkP` on the definitions and the
-- entry. A definition is checked once there. A `gref` in that pass
-- is `ok zeros`: the use vector is zeros. It is not a discharge of
-- a local binder.
--
-- The entry is a surface process term. `(defs …)` is the definition
-- list of a root `seq`. Any other entry with a non-empty list is
-- refused: a nested `seq` does not inherit that list. A legacy entry
-- `(seq <btm> (done))` is `seq defs btm done`, the program load
-- checked before process entries.
--
-- `lowerP` (in `MuroBeam.PTm`) is the initial system. `lowerP-wf`
-- and `lowerP-safe` apply to anything `load` accepts. The emitter
-- is outside the TCB for those two. `lower-safe` is not that claim.
-- It is `Step* (lower e)` for a pure `Checked`.
--
-- Non-consequences of `load`:
-- `budget-adequate` is
-- `(e : Checked) {s : Sys} → NoEscape (term e) → MatchFree (term e) →
--  Step* (lower e) s → Inv tight s`
-- (`MuroBeam.Budget`). `checkP` on `seq` runs
-- `boundaryOk (inB? (comps Γ) e)`. `load` calls that at `Γ = []` on
-- the entry term `e`. That decision is `InB [] e`. The capture
-- predicate on the same term is `NoEsc [] e`. `InBoundary` and
-- `NoEscape` are those two predicates on `embed` of a `GTm`, and
-- `inBoundary→noEscape` has that `GTm` type. There is no theorem
-- `load s ≡ ok p → InB [] e`, and none `load s ≡ ok p → NoEsc [] e`.
-- The public adequacy predicates stay `GTm`-only. What is also
-- missing is `MatchFree` (`match.mbi` loads and contains `gmatch`;
-- `MatchFree` has no `gmatch` clause; `mf-ref` is a clause of `Mf`)
-- and the theorem's path: pure `Checked` / `lower` / `Step*`, not
-- `CheckedP` / `lowerP` / `PStep*`.
-- `no-stray-reply` (needs `ReplyDone`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Load where

open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.String.Base using (String)
open import Data.Vec.Base using ([])
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Result; ok; fail)
open import Muro.Grade using (Uses)

open import MuroBeam.Boundary using (boundary-version)
open import MuroBeam.BTm using (BTm)
open import MuroBeam.Image using
  ( Image; format; boundary; entry; defs; format-version
  ; SPtm; sdone; ssend; srecv; sspawn; sseq; sawait; signore; snignore )
open import MuroBeam.Parse using (parseR)
open import MuroBeam.PSyntax using
  (PTm; done; send; recv; spawn; seq; await; ignore; nignore)
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

-- Surface syntax has no definition list on `seq`. The image section
-- is attached here, and only to the root `seq`. Nested seqs stay empty.
toP : ∀ {n} → SPtm n → PTm n
toP sdone              = done
toP (ssend j x k)      = send j x (toP k)
toP (srecv c t k)      = recv c t (toP k)
toP (sspawn th ch pa)  = spawn th (toP ch) (toP pa)
toP (sseq e k)         = seq [] e (toP k)
toP (sawait x k)       = await x (toP k)
toP (signore x k)      = ignore x (toP k)
toP (snignore x k)     = nignore x (toP k)

noDefs : List (BTm 0) → PTm 0 → Result (PTm 0)
noDefs []       p = ok p
noDefs (_ ∷ _)  _ = fail "defs need a seq entry"

assemble : List (BTm 0) → SPtm 0 → Result (PTm 0)
assemble ds (sseq e k)         = ok (seq ds e (toP k))
assemble ds sdone              = noDefs ds (toP sdone)
assemble ds (ssend j x k)      = noDefs ds (toP (ssend j x k))
assemble ds (srecv c t k)      = noDefs ds (toP (srecv c t k))
assemble ds (sspawn th ch pa)  = noDefs ds (toP (sspawn th ch pa))
assemble ds (sawait x k)       = noDefs ds (toP (sawait x k))
assemble ds (signore x k)      = noDefs ds (toP (signore x k))
assemble ds (snignore x k)     = noDefs ds (toP (snignore x k))

load : String → Result CheckedP
load s with parseR s
... | fail e = fail e
... | ok i with versionOk (format i)
... | false = fail "bad version"
... | true with eqℕ (boundary i) boundary-version
... | false = fail "bad boundary version"
... | true with assemble (defs i) (entry i)
... | fail e = fail e
... | ok p = admit p (checkP [] p) refl

-- The equation is `CheckedP.okp`. It holds for every `CheckedP`,
-- and this proof does not use `load s ≡ ok p`. The real guarantee
-- is the return type: `admit` builds `checkedP` only after `checkP`
-- has returned `ok []`.
load-sound : ∀ s p → load s ≡ ok p → checkP [] (CheckedP.prog p) ≡ ok []
load-sound _ p _ = CheckedP.okp p
