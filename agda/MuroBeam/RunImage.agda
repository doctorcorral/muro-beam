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
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Muro.Base using (Result; ok; fail)

open import MuroBeam.Heap using (Obj; Val; nat; suc↑; clo; obj)
open import MuroBeam.Image using (showImage; showNat)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.Load using (load)
open import MuroBeam.Parse using (parse)
open import MuroBeam.PRun using (seq1; bind1)
open import MuroBeam.PTm using
  ( lowerP; CheckedP; checkedP; spawnAwait; spawnAwait-ok )
open import MuroBeam.Sched using
  ( drive; Drove; oc; val; plain; Outcome
  ; plain-halted; plain-deadlock; plain-stuck; plain-fuel )
open import MuroBeam.Show using (showOc; showVal; showDrove)
open import MuroBeam.Process using
  ( Sys; sys; heap; procs; Proc; ctl; Ctl; rv
  ; Frame; saved; seg; eval1; runFor; payloadAt; setProc )

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
-- An aliased non-g1 reply is refused. `checkP` already rejects a
-- non-fresh body, and a fresh head's returning step allocates at
-- `length` of the heap. There is no theorem from `freshBody` to the
-- tag. This probe loads a reply image, runs the body until `eval1`
-- stops on `saved ∷ seg`, and plants a second reference to that cell.
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

aliasStep : CheckedP → String
aliasStep p with seq1 (lowerP p) zero
... | nothing = "missed"
... | just s with runFor aliasFuel s
... | s2 with plantAlias s2
... | nothing = "missed"
... | just s3 with bind1 s3 zero
... | nothing = "refuse: aliased reply result"
... | just _  = "accepted"

-- Closed test of `bind-count-refuses`, not the lemma. The plant puts
-- the returned cell in the environment as well as in `rv`, so the
-- count is not 1, the cell is not `g1`, and the continuation is a
-- reply root. `aliasStep` prints the `nothing` branch. The general
-- fact is `bind-count-refuses` in `MuroBeam.PRun`.
alias-await-probe :
  aliasStep (checkedP spawnAwait spawnAwait-ok) ≡ "refuse: aliased reply result"
alias-await-probe = refl

aliasImage : String → String
aliasImage src with load src
... | fail e = "refuse: " ++ e
... | ok p   = aliasStep p

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

-- The CLI tag. A load refusal is the same `load` line `cliRun` uses,
-- so the Haskell main exits 2 and writes the reason on stderr. A
-- loaded image is `ok` plus the plant string. `aliasImage` stays the
-- raw plant, which is what `alias-bind-plant` states.
aliasCli : String → String
aliasCli src with load src
... | fail e = "load\n" ++ e
... | ok p   = "ok\n" ++ aliasStep p

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

-- `cliRun` keeps `proj₁`. The `PStep*` is `proj₂` of that same `drive`,
-- and this string does not carry it. `drive-sound` names `proj₂` when
-- the `Drove` is matched. It is not a theorem about `cliRun`.
cli-drove : ∀ src fuel p →
  load src ≡ ok p →
  cliRun src fuel ≡
    cliBody (proj₁ (drive fuel zero [] nothing (lowerP p)))
cli-drove src fuel p eq rewrite eq = refl
