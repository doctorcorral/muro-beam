------------------------------------------------------------------------
-- Run one pure image.
--
-- `runImage` is the pid-0 harness: `seq1` once, then `runFor`. The
-- value sits on the `saved` frame; `bind` and `done` are not taken.
--
-- `cliRun` is what the `muro-beam` binary calls. It `load`s the text
-- and runs `drive` at the fuel the caller passes. `scripts/build_runner.py`
-- generates `MAlonzo/RunnerMain.hs`, which reads the path and the
-- fuel. That main is not an Agda module, so the audit still sees
-- only `--safe` files. A pure entry, whose continuation is `done`,
-- stops `stuck`: `seq1` pushes `saved` over `seg`, and `bind1`
-- leaves that stack when the continuation is `done`. A continuation
-- that is not `done` is resumed. The nat `drive` kept is the value
-- on that `rv`, or the first delivered payload. The tag `fuel` is
-- `outOfFuel`. The tag `load` is a `fail` from `load`, and no
-- schedule is run. The line under the tag is `showDrove`: outcome,
-- events, fingerprint, and kept nat. That printer is
-- `MuroBeam.Show`, shared with `MuroBeam.Conform` and the book.
-- Decimals are the fuel-bounded `showℕ`. A numeral past eight
-- digits is `overflow`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.RunImage where

open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using (proj₁)
open import Data.String.Base using (String; _++_; fromList)
open import Muro.Base using (Result; ok; fail)

open import MuroBeam.Heap using (Obj; Val; nat; suc↑; clo; obj)
open import MuroBeam.Image using (showImage; showNat)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.Load using (load)
open import MuroBeam.Parse using (parse)
open import MuroBeam.PRun using (seq1)
open import MuroBeam.PTm using (lowerP)
open import MuroBeam.Sched using
  ( drive; Drove; oc; val; plain; Outcome
  ; plain-halted; plain-deadlock; plain-stuck; plain-fuel )
open import MuroBeam.Show using (showOc; showVal; showDrove)
open import MuroBeam.Process using
  ( Sys; heap; procs; Proc; ctl; Ctl; rv
  ; Frame; saved; seg; eval1; runFor; payloadAt )

data Halt : Set where
  hnat  : ℕ → Halt
  hclo  : Halt
  hstuck : Halt

bump : Halt → Halt
bump (hnat n) = hnat (suc n)
bump hclo     = hstuck
bump hstuck   = hstuck

-- Fuel is one past the heap length, so a successor chain that is
-- a path in the heap is read, and a cycle stops.
readRef : List Obj → ℕ → ℕ → Halt
readRef _ zero    _ = hstuck
readRef h (suc f) i with payloadAt h i
... | just (nat n)    = hnat n
... | just (suc↑ r)   = bump (readRef h f (obj r))
... | just (clo _ _)  = hclo
... | nothing         = hstuck

renderV : Halt → String
renderV (hnat n) = "nat " ++ fromList (showNat n)
renderV hclo     = "closure"
renderV hstuck   = "stuck"

valueCtl : List Obj → Ctl → String
valueCtl h (rv r _ []) = renderV (readRef h (suc (length h)) (obj r))
valueCtl h (rv r _ (saved _ ∷ [])) = renderV (readRef h (suc (length h)) (obj r))
-- `seq1` parks the value on `saved` and leaves the code segment under it.
valueCtl h (rv r _ (saved _ ∷ seg _ ∷ [])) =
  renderV (readRef h (suc (length h)) (obj r))
valueCtl _ _ = "stuck"

finish : Sys → String
finish s with eval1 s zero
... | just _  = "fuel"
... | nothing with lookup (procs s) zero
... | nothing = "stuck"
... | just p  = valueCtl (heap s) (ctl p)

runSys : ℕ → Sys → String
runSys fuel s with seq1 s zero
... | nothing = "stuck"
... | just s1 = finish (runFor fuel s1)

runImage : String → ℕ → String
runImage src fuel with load src
... | fail e = "refuse: " ++ e
... | ok p   = runSys fuel (lowerP p)

echoImage : String → String
echoImage s with parse s
... | just i = showImage i
... | nothing = "no"

-- Fuelled drive of a loaded image. The file has one process. `seq1`
-- pushes `saved` over `seg`. `bind1` resumes that stack when the
-- continuation is not `done`, and leaves a `done` continuation
-- parked, so a pure entry can stop `stuck` with the nat in `rv`.
-- The text is the outcome and the nat `drive` kept.

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

-- 1000, the same default `scripts/build_runner.py` `DEFAULT_FUEL` uses.
-- `driveImage` and `muro-beam` therefore stop on the same fuel.
-- `MuroBeam.SchedThm.driveFuel` stays 16: the closed `refl`s recompute
-- `drive`, and a pure image that has already stopped does not need the
-- runner's budget.
imgFuel : ℕ
imgFuel =
  let p2   = dbl (suc zero)
      p4   = dbl p2
      p8   = dbl p4
      p16  = dbl p8
      p32  = dbl p16
      p64  = dbl p32
      p128 = dbl p64
      p256 = dbl p128
      p512 = dbl p256
  in p512 + p256 + p128 + p64 + p32 + p8

driveImage : String → String
driveImage src with load src
... | fail e = "refuse: " ++ e
... | ok p   =
  let d = proj₁ (drive imgFuel zero [] nothing (lowerP p))
  in showOc (oc d) ++ " " ++ showVal (val d)

-- The full line `showDrove` prints. No newline: the Haskell main adds one.
-- Reply images pin this, not only the outcome and the nat.
droveImage : String → String
droveImage src with load src
... | fail e = "refuse: " ++ e
... | ok p   = showDrove (proj₁ (drive imgFuel zero [] nothing (lowerP p)))

------------------------------------------------------------------------
-- The line `muro-beam` prints is `showDrove` from MuroBeam.Show.
-- `seq` and `bind` emit no event. `eval` emits `tr-step`. A halt
-- emits `tr-collect`. A pure image does not halt.
--
-- `ok` is a finished schedule: halted, deadlock, or stuck. Those
-- three tags are wired here. A pure entry stops `stuck`. A process
-- entry can halt, deadlock, or stick, and the binary reports that
-- outcome. `fuel` is `outOfFuel`, and the next
-- line is the partial schedule. `load` is the reason `load`
-- returned. No schedule is run.
------------------------------------------------------------------------

mark : ∀ {t} → Outcome t → String
mark o with plain o
... | plain-fuel     = "fuel"
... | plain-halted   = "ok"
... | plain-deadlock = "ok"
... | plain-stuck _  = "ok"

cliBody : Drove → String
cliBody d = mark (oc d) ++ "\n" ++ showDrove d

cliRun : String → ℕ → String
cliRun src fuel with load src
... | fail e = "load\n" ++ e
... | ok p   = cliBody (proj₁ (drive fuel zero [] nothing (lowerP p)))
