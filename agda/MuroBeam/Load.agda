------------------------------------------------------------------------
-- Load an image. Parse, then demand format 1, 2, or 3 and this tree's
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
-- (`MuroBeam.Budget`). `inB?` runs on a `seq` body
-- (`boundaryOk (inB? (comps Γ) e)` in that clause) and on each
-- definition (`checkDef`). A `done`, `spawn`, `send`, or `recv`
-- entry does not call `inB?`. `load` of a root `seq` runs it at
-- `Γ = []` on the body `e`, and that decision is `InB [] e` for
-- that body. It is not a theorem for an arbitrary entry. The capture
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
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.Vec.Base using ([])
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

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
open import MuroBeam.Port using (Ports; portsOf)

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ (suc m) (suc n) = eqℕ m n
eqℕ _       _       = false

-- v1 is the empty-defs file muro emits. v2 carries a defs section.
-- v3 (B4a) is the v1/v2 grammar run with the host console at pid 1
-- (`MuroBeam.Port`). `load` checks a v3 program exactly as a v1 or v2
-- one; the format number only reaches the layout, through `loadIO`.
-- Any other number is refused. The printer reprints the number it read.
versionOk : ℕ → Bool
versionOk n = eqℕ n format-version ∨ eqℕ n 2 ∨ eqℕ n 3

-- `Uses 0` is an empty vector, so the only success is `ok []`.
-- The name is `packLoad`: `admit` reads like a hole.
packLoad : (p : PTm 0) (r : Result (Uses 0)) → checkP [] p ≡ r → Result CheckedP
packLoad _ (fail e) _ = fail e
packLoad p (ok []) eq = ok (checkedP p eq)

-- `checkP` is the result `packLoad` matches. A `fail` stays a `fail`.
loadChecked : (p : PTm 0) → Result CheckedP
loadChecked p = packLoad p (checkP [] p) refl

-- Matching `refl` carries a re-run of `checkP` onto the stored result.
-- A `rewrite` of `checkP [] q` under `packLoad q (checkP [] q) refl`
-- is ill-typed: that `refl` does not survive the abstraction.
pack-match : (q : PTm 0) {r : Result (Uses 0)} (eq : checkP [] q ≡ r) →
  packLoad q (checkP [] q) refl ≡ packLoad q r eq
pack-match q refl = refl

-- The `with` lives here, where the result type does not mention
-- `packLoad`. `view-ok` carries the `ok []` proof out to `load-facts`.
data CheckView (q : PTm 0) : Set where
  view-fail : (e : String) → checkP [] q ≡ fail e → CheckView q
  view-ok   : checkP [] q ≡ ok [] → CheckView q

checkView : (q : PTm 0) → CheckView q
checkView q with checkP [] q in eq
... | fail e = view-fail e eq
... | ok []  = view-ok eq

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

-- Each gate is a function of the boolean or the `Result` it matches,
-- so a proof can case on that argument and use the `load` equation.
fromProgram : Result (PTm 0) → Result CheckedP
fromProgram (fail e) = fail e
fromProgram (ok p)   = loadChecked p

fromBoundary : Image → Bool → Result CheckedP
fromBoundary i false = fail "bad boundary version"
fromBoundary i true  = fromProgram (assemble (defs i) (entry i))

fromVersion : Image → Bool → Result CheckedP
fromVersion i false = fail "bad version"
fromVersion i true  = fromBoundary i (eqℕ (boundary i) boundary-version)

loadFrom : Result Image → Result CheckedP
loadFrom (fail e) = fail e
loadFrom (ok i)   = fromVersion i (versionOk (format i))

load : String → Result CheckedP
load s = loadFrom (parseR s)

-- A successful `load` is `packLoad` of the program `checkP` accepted,
-- and that check is `ok []`. The premise is the `load` equation.
-- `CheckedP.okp` of an arbitrary `CheckedP` is not this statement.
load-facts : ∀ s p → load s ≡ ok p →
  (packLoad (CheckedP.prog p) (checkP [] (CheckedP.prog p)) refl ≡ ok p)
  × (checkP [] (CheckedP.prog p) ≡ ok [])
load-facts s p eq = fromImage (parseR s) eq
  where
  Goal =
    (packLoad (CheckedP.prog p) (checkP [] (CheckedP.prog p)) refl ≡ ok p)
    × (checkP [] (CheckedP.prog p) ≡ ok [])
  fromImage : (r : Result Image) → loadFrom r ≡ ok p → Goal
  fromImage (fail _) ()
  fromImage (ok i) eqv = onVersion (versionOk (format i)) refl eqv
    where
    onVersion : (b : Bool) → versionOk (format i) ≡ b → loadFrom (ok i) ≡ ok p → Goal
    onVersion false vb eqv rewrite vb = no eqv
      where
      no : fromVersion i false ≡ ok p → Goal
      no ()
    onVersion true vb eqv rewrite vb = onBoundary (eqℕ (boundary i) boundary-version) refl eqv
      where
      onBoundary : (b : Bool) → eqℕ (boundary i) boundary-version ≡ b →
                   fromVersion i true ≡ ok p → Goal
      onBoundary false bb eqb rewrite bb = no eqb
        where
        no : fromBoundary i false ≡ ok p → Goal
        no ()
      onBoundary true bb eqb rewrite bb = onProgram (assemble (defs i) (entry i)) eqb
        where
        onProgram : (r : Result (PTm 0)) → fromProgram r ≡ ok p → Goal
        onProgram (fail _) ()
        onProgram (ok q) eqq with checkView q
        ... | view-fail e eqc =
          refused (subst (λ z → z ≡ ok p) (pack-match q eqc) eqq)
          where
          refused : packLoad q (fail e) eqc ≡ ok p → Goal
          refused ()
        ... | view-ok eqc =
          packed (subst (λ z → z ≡ ok p) (pack-match q eqc) eqq)
          where
          packed : packLoad q (ok []) eqc ≡ ok p → Goal
          packed refl = pack-match q eqc , eqc

-- A successful `load` is `packLoad` of the program `checkP` accepted.
load-sound : ∀ s p → load s ≡ ok p →
  packLoad (CheckedP.prog p) (checkP [] (CheckedP.prog p)) refl ≡ ok p
load-sound s p eq = proj₁ (load-facts s p eq)

-- The checker equation, derived from `load-facts`. A successful pack
-- stored `ok []`, so the loaded program is that check.
load-checks : ∀ s p → load s ≡ ok p → checkP [] (CheckedP.prog p) ≡ ok []
load-checks s p eq = proj₂ (load-facts s p eq)

------------------------------------------------------------------------
-- B4a. `loadIO` is `load` plus the host ports the format number asks
-- for (`portsOf`: 3 is the console, 1 and 2 are none). The checked
-- program is the one `load` returns (`loadIO-load`), so every `load`
-- fact transfers. `muro-beam` calls this, then `drive` on `lowerIO`.
------------------------------------------------------------------------

record Boot : Set where
  constructor mkBoot
  field
    prog  : CheckedP
    ports : Ports

withPorts : Ports → Result CheckedP → Result Boot
withPorts _  (fail e) = fail e
withPorts pt (ok p)   = ok (mkBoot p pt)

bootFrom : Result Image → Result Boot
bootFrom (fail e) = fail e
bootFrom (ok i)   = withPorts (portsOf (format i)) (loadFrom (ok i))

loadIO : String → Result Boot
loadIO s = bootFrom (parseR s)

withPorts-ok : ∀ pt r b → withPorts pt r ≡ ok b → r ≡ ok (Boot.prog b)
withPorts-ok pt (fail e) b ()
withPorts-ok pt (ok p) .(mkBoot p pt) refl = refl

bootFrom-ok : ∀ r b → bootFrom r ≡ ok b → loadFrom r ≡ ok (Boot.prog b)
bootFrom-ok (fail e) b ()
bootFrom-ok (ok i)   b eq = withPorts-ok (portsOf (format i)) (loadFrom (ok i)) b eq

-- A `loadIO` success is a `load` success on the same text.
loadIO-load : ∀ s b → loadIO s ≡ ok b → load s ≡ ok (Boot.prog b)
loadIO-load s b eq = bootFrom-ok (parseR s) b eq

loadIO-checks : ∀ s b → loadIO s ≡ ok b →
  checkP [] (CheckedP.prog (Boot.prog b)) ≡ ok []
loadIO-checks s b eq = load-checks s (Boot.prog b) (loadIO-load s b eq)

withPorts-ports : ∀ pt r b → withPorts pt r ≡ ok b → Boot.ports b ≡ pt
withPorts-ports pt (fail e) b ()
withPorts-ports pt (ok p) .(mkBoot p pt) refl = refl

-- The ports are the parsed format's: 3 is `console`, 1 and 2 `none`.
loadIO-ports : ∀ s i b → parseR s ≡ ok i → loadIO s ≡ ok b →
  Boot.ports b ≡ portsOf (format i)
loadIO-ports s i b pe eq rewrite pe =
  withPorts-ports (portsOf (format i)) (loadFrom (ok i)) b eq
