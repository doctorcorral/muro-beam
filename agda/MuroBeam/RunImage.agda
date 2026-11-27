------------------------------------------------------------------------
-- Run one pure image.
--
-- `runImage` is the pid-0 harness: `seq1` once, then `runFor`. The
-- value sits on the `saved` frame; `bind` and `done` are not taken.
--
-- `cliRun` is what the `muro-beam` binary calls. It `loadIO`s the text
-- and runs `drive` at the fuel the caller passes, on `lowerIO`: a
-- format-3 image has the host console at pid 1 and prints its inbox
-- before the summary line (B4a, `MuroBeam.Port`). `cliRunIn` is the
-- same with `--input`: it parses the host text with `readInput` and
-- runs on `bootIn`, so a format-4 image also has the input port at
-- pid 2 sending those values to pid 0 (B4b); any other format is
-- `no input port`. `scripts/build_runner.py` generates
-- `MAlonzo/RunnerMain.hs`, which reads the path, the fuel, and the
-- optional `--input` file or stdin. That main is not an Agda module, so the audit still sees
-- only `--safe` files. A pure entry, whose continuation is `done`,
-- stops `stuck`: `seq1` pushes `saved` over `seg`, and `bind1`
-- leaves that stack when the continuation is `done`. A continuation
-- that is not `done` is resumed. The nat `drive` kept is the value
-- on that `rv`, or the first delivered payload. The tag `fuel` is
-- `outOfFuel`. The tag `load` is a `fail` from `loadIO`, and no
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
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Muro.Base using (Result; ok; fail)

open import MuroBeam.Heap using (Obj; Val; nat; suc↑; clo; con; obj)
open import MuroBeam.Image using (showImage; showNat)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.Load using (loadIO; Boot; mkBoot)
open import MuroBeam.Port using
  ( Ports; none; console; stdio; lowerIn; lowerIO; portOut
  ; OutV; out-nat; out-clo; out-con; out-bad )
open import MuroBeam.Input using (readInput)
open import MuroBeam.Parse using (parse)
open import MuroBeam.PRun using (seq1; bind1)
open import MuroBeam.PTm using
  ( lowerP; CheckedP; checkedP; spawnAwait; spawnAwait-ok )
open import MuroBeam.Sched using
  ( drive; Drove; oc; val; final; plain; Outcome
  ; plain-halted; plain-deadlock; plain-stuck; plain-fuel )
open import MuroBeam.Show using (showOc; showVal; showDrove)
open import MuroBeam.Process using
  ( Sys; sys; heap; procs; Proc; ctl; Ctl; rv
  ; Frame; saved; seg; eval1; runFor; payloadAt; setProc )

data Halt : Set where
  hnat  : ℕ → Halt
  hclo  : Halt
  hcon  : ℕ → Halt
  hstuck : Halt

bump : Halt → Halt
bump (hnat n) = hnat (suc n)
bump hclo     = hstuck
bump (hcon _) = hstuck
bump hstuck   = hstuck

-- Fuel is one past the heap length, so a successor chain that is
-- a path in the heap is read, and a cycle stops.
readRef : List Obj → ℕ → ℕ → Halt
readRef _ zero    _ = hstuck
readRef h (suc f) i with payloadAt h i
... | just (nat n)    = hnat n
... | just (suc↑ r)   = bump (readRef h f (obj r))
... | just (clo _ _)  = hclo
... | just (con t _)  = hcon t
... | nothing         = hstuck

renderV : Halt → String
renderV (hnat n) = "nat " ++ fromList (showNat n)
renderV hclo     = "closure"
renderV (hcon t) = "con " ++ fromList (showNat t)
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

-- The system an image boots: `lowerIO` on the ports `loadIO` read.
-- Formats 1 and 2 are `lowerP` (`lowerIO none` is `lowerP` by
-- definition). Format 3 adds the console at pid 1. Format 4 adds the
-- console and the input port at pid 2, here with no input, so the
-- port ends at once. Every image entry in this module goes through
-- `loadIO` and `bootSys` (or `bootIn` with host input), so no runner
-- lowers a format-3 or format-4 program without its ports. `load` is
-- the checker; it does not choose a layout.
bootSys : Boot → Sys
bootSys b = lowerIO (Boot.ports b) (Boot.prog b)

-- With host input `xs` (B4b). Only a format-4 (`stdio`) layout puts
-- `xs` anywhere; `bootSys` is `bootIn []`.
bootIn : List ℕ → Boot → Sys
bootIn xs b = lowerIn xs (Boot.ports b) (Boot.prog b)

-- The harness reads pid 0 only. A console at pid 1 is not stepped.
runImage : String → ℕ → String
runImage src fuel with loadIO src
... | fail e = "refuse: " ++ e
... | ok b   = runSys fuel (bootSys b)

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
-- runner's budget. `gtypReply` does not halt at 16. Its pin is
-- `gtypFuel`, which is 20.
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
driveImage src with loadIO src
... | fail e = "refuse: " ++ e
... | ok b   =
  let d = proj₁ (drive imgFuel zero [] nothing (bootSys b))
  in showOc (oc d) ++ " " ++ showVal (val d)

-- The full line `showDrove` prints. No newline: the Haskell main adds one.
-- Reply images pin this, not only the outcome and the nat. A format-3
-- image runs with its console here too; the console lines are
-- `ioImage`, and this is only the summary line.
droveImage : String → String
droveImage src with loadIO src
... | fail e = "refuse: " ++ e
... | ok b   = showDrove (proj₁ (drive imgFuel zero [] nothing (bootSys b)))

------------------------------------------------------------------------
-- An aliased non-g1 reply is refused. `checkP` already rejects a
-- non-fresh body, and a fresh head's returning step allocates at
-- `length` of the heap. There is no theorem from `freshBody` to the
-- tag. This probe runs the hand-built term `spawnAwait`, not the file
-- `alias-await.mbi`. It steps until `eval1` stops on `saved ∷ seg`,
-- and plants a second reference to that cell.
-- `bind1` then returns `nothing` instead of resuming the ω alias.
-- Eight eval steps cover `gze` and `gsu gze`. `runFor` stops when
-- `eval1` returns `nothing`, so the rest of the fuel is not a loop.
------------------------------------------------------------------------

aliasFuel : ℕ
aliasFuel = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

plantCtl : Ctl → Maybe Ctl
plantCtl (rv r env (saved c ∷ seg ds ∷ [])) =
  just (rv r (r ∷ env) (saved c ∷ seg ds ∷ []))
plantCtl _ = nothing

plantAlias : Sys → Maybe Sys
plantAlias (sys h ps) with lookup ps zero
... | nothing = nothing
... | just p with plantCtl (ctl p)
... | nothing = nothing
... | just c with setProc ps zero c
... | nothing = nothing
... | just ps' = just (sys h ps')

-- The probe on a booted system. `aliasStep` is the hand-built entry
-- on `lowerP`. `aliasImage` and `aliasCli` boot through `loadIO`.
aliasSys : Sys → String
aliasSys s0 with seq1 s0 zero
... | nothing = "missed"
... | just s with runFor aliasFuel s
... | s2 with plantAlias s2
... | nothing = "missed"
... | just s3 with bind1 s3 zero
... | nothing = "refuse: aliased reply result"
... | just _  = "accepted"

aliasStep : CheckedP → String
aliasStep p = aliasSys (lowerP p)

-- Closed test of `bind-count-refuses`, not the lemma. The plant puts
-- the returned cell in the environment as well as in `rv`, so the
-- count is not 1, the cell is not `g1`, and the continuation is a
-- reply root. The term is the hand-built `spawnAwait`. It is not a
-- load of `alias-await.mbi`: that file's body is not fresh, so
-- `checkP` refuses it (`aliasAwait-no`) and `bind1` never runs.
-- `aliasStep` prints the `nothing` branch. The general fact is
-- `bind-count-refuses` in `MuroBeam.PRun`.
spawnAwait-alias :
  aliasStep (checkedP spawnAwait spawnAwait-ok) ≡ "refuse: aliased reply result"
spawnAwait-alias = refl

aliasImage : String → String
aliasImage src with loadIO src
... | fail e = "refuse: " ++ e
... | ok b   = aliasSys (bootSys b)

-- The text of `examples/images/alias-bind.mbi`. Agda does not open
-- the file. This is that line, including the trailing newline.
-- The body is `gsu gze`: a fresh head, so `load` accepts it and the
-- plant is what refuses.
aliasBindSrc : String
aliasBindSrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gsu gze) (spawn (keep t[]) (send 0 0 (done)) (await 0 (done))))))\n"

alias-bind-plant :
  aliasImage aliasBindSrc ≡ "refuse: aliased reply result"
alias-bind-plant = refl

-- The CLI tag. A load refusal is the same `loadIO` line `cliRun` uses,
-- so the Haskell main exits 2 and writes the reason on stderr. A
-- loaded image is `ok` plus the plant string. `aliasImage` stays the
-- raw plant, which is what `alias-bind-plant` states.
aliasCli : String → String
aliasCli src with loadIO src
... | fail e = "load\n" ++ e
... | ok b   = "ok\n" ++ aliasSys (bootSys b)

------------------------------------------------------------------------
-- The line `muro-beam` prints is `showDrove` from MuroBeam.Show.
-- `seq` and `bind` emit no event. `eval` emits `tr-step`. A halt
-- emits `tr-collect`. A pure image does not halt.
--
-- `ok` is a finished schedule: halted, deadlock, or stuck. Those
-- three tags are wired here. A pure entry stops `stuck`. A process
-- entry can halt, deadlock, or stick, and the binary reports that
-- outcome. `fuel` is `outOfFuel`, and the next
-- line is the partial schedule. `load` is the reason `loadIO`
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

------------------------------------------------------------------------
-- B4a console output. A format-3 image runs on `lowerIO console`, and
-- the host prints the console inbox of the final system before the
-- `showDrove` line: one line per message, in delivery order. A nat is
-- its decimal, a constructor is `con <tag>`, a closure is `closure`,
-- and a cell `readOut` cannot read is `stuck`. Format 1 and 2 print
-- no output lines, so their bytes do not move (`ioBody none` is
-- `cliBody`).
------------------------------------------------------------------------

showOutV : OutV → String
showOutV (out-nat n) = fromList (showNat n)
showOutV out-clo     = "closure"
showOutV (out-con t) = "con " ++ fromList (showNat t)
showOutV out-bad     = "stuck"

outLines : List OutV → String
outLines []       = ""
outLines (v ∷ vs) = showOutV v ++ "\n" ++ outLines vs

-- The output lines then the summary line. No trailing newline: the
-- Haskell main adds one.
ioLine : Ports → Drove → String
ioLine none    d = showDrove d
ioLine console d = outLines (portOut console (final d)) ++ showDrove d
ioLine stdio   d = outLines (portOut stdio (final d)) ++ showDrove d

ioBody : Ports → Drove → String
ioBody none    d = cliBody d
ioBody console d = mark (oc d) ++ "\n" ++ ioLine console d
ioBody stdio   d = mark (oc d) ++ "\n" ++ ioLine stdio d

driveIO : ℕ → Boot → Drove
driveIO fuel b = proj₁ (drive fuel zero [] nothing (bootSys b))

driveIn : ℕ → List ℕ → Boot → Drove
driveIn fuel xs b = proj₁ (drive fuel zero [] nothing (bootIn xs b))

cliRun : String → ℕ → String
cliRun src fuel with loadIO src
... | fail e = "load\n" ++ e
... | ok b   = ioBody (Boot.ports b) (driveIO fuel b)

-- `cliRun` keeps `proj₁`. The `PStep*` is `proj₂` of that same `drive`,
-- and this string does not carry it. `drive-sound` names `proj₂` when
-- the `Drove` is matched (`Port.io-final-wf` is `WF` of that final
-- system). It is not a theorem about `cliRun`.
cli-drove : ∀ src fuel b →
  loadIO src ≡ ok b →
  cliRun src fuel ≡ ioBody (Boot.ports b) (driveIO fuel b)
cli-drove src fuel b eq rewrite eq = refl

-- A format 1 or 2 image is the pre-B4 line: `cliBody` of `drive` on
-- `lowerP`.
cli-drove-none : ∀ src fuel p →
  loadIO src ≡ ok (mkBoot p none) →
  cliRun src fuel ≡
    cliBody (proj₁ (drive fuel zero [] nothing (lowerP p)))
cli-drove-none src fuel p eq rewrite eq = refl

-- What a format-3 pin states: the output lines and the summary at
-- `imgFuel`. A refusal is `refuse: ` and the reason, as `droveImage`.
ioImage : String → String
ioImage src with loadIO src
... | fail e = "refuse: " ++ e
... | ok b   = ioLine (Boot.ports b) (driveIO imgFuel b)

------------------------------------------------------------------------
-- B4b host input. `muro-beam IMAGE --input FILE` (or `--input -` for
-- stdin) calls `cliRunIn` with the text it read. A format-4 image
-- boots with the input port at pid 2 sending those values to pid 0.
-- Input to any other format is the load refusal `no input port`; a
-- text `readInput` refuses is `bad input`. Both are tagged `load`, so
-- the binary exits 2 with the reason on stderr, as for a parse or
-- `checkP` refusal. Without `--input` the binary calls `cliRun`: a
-- format-4 image then runs with an empty input, and its port ends at
-- once.
------------------------------------------------------------------------

-- The port gate. Only `stdio` takes input.
inGate : ℕ → Boot → Ports → Result (List ℕ) → String
inGate fuel b none    _        = "load\nno input port"
inGate fuel b console _        = "load\nno input port"
inGate fuel b stdio   (fail e) = "load\n" ++ e
inGate fuel b stdio   (ok xs)  = ioBody stdio (driveIn fuel xs b)

cliRunIn : String → ℕ → String → String
cliRunIn src fuel inp with loadIO src
... | fail e = "load\n" ++ e
... | ok b   = inGate fuel b (Boot.ports b) (readInput inp)

cli-in : ∀ src fuel inp b →
  loadIO src ≡ ok b →
  cliRunIn src fuel inp ≡ inGate fuel b (Boot.ports b) (readInput inp)
cli-in src fuel inp b eq rewrite eq = refl

-- A format-4 image with no input is the same run as `cliRun`.
cli-in-empty : ∀ src fuel p →
  loadIO src ≡ ok (mkBoot p stdio) →
  cliRunIn src fuel "" ≡ cliRun src fuel
cli-in-empty src fuel p eq rewrite eq = refl

-- What a format-4 pin states: `ioImage` with that input. A refusal is
-- `refuse: ` and the reason.
inPinGate : Boot → Ports → Result (List ℕ) → String
inPinGate b none    _        = "refuse: no input port"
inPinGate b console _        = "refuse: no input port"
inPinGate b stdio   (fail e) = "refuse: " ++ e
inPinGate b stdio   (ok xs)  = ioLine stdio (driveIn imgFuel xs b)

ioImageIn : String → String → String
ioImageIn src inp with loadIO src
... | fail e = "refuse: " ++ e
... | ok b   = inPinGate b (Boot.ports b) (readInput inp)
