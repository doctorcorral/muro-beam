------------------------------------------------------------------------
-- Closed traces for the MAlonzo comparison.
--
-- The strings are the encoding in book/show.muro. Nothing here is a
-- proof: the Haskell driver prints `report`, and the book prints the
-- same lines by normalising its show definitions. A refusal is the
-- word nothing, with no fingerprint. A successful Maybe Run is just,
-- the events, and a post-state fingerprint. collect is total, so that
-- line is ran.
--
-- The fingerprint is h<heap length>l<live cells>p<process count>.
-- It is not the system. The older lines do not compare payloads,
-- grades, or control. A scheduled line also prints the outcome and
-- the first nat the driver kept (`v-` when it kept none). `sched-up`
-- keeps a delivered `suc↑`. `sched-stray` also prints `mailHas` and
-- whether any wrapper is enabled. `sched-empty` prints the final
-- heap's freeness. `sched-console` (B4a) writes to a `done`, `idle`
-- process at pid 1 and prints the nat of its first message.
-- `sched-input` (B4b) is the format-4 shape: an input port at pid 2
-- sends to pid 0, which receives it; the console at pid 1 stays empty.
-- `sched-scrub` (B4c) is a flush that scrubs a reply out of the
-- console's inbox: `out` is `v-`.
-- Event spelling, decimals, and `showDrove` are
-- `MuroBeam.Show`, shared with the `muro-beam` CLI.
--
-- Example, Lower, Unique, PExample, Stray, and PWf are not imported.
-- The closed cex term and lowerTm live in MuroBeam.Cex.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Conform where

open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product.Base using (proj₁)
open import Data.String.Base using (String; _++_)

open import Muro.Grade using
  ( Grade; Point; fin; inf; pt; iv; g0; g1
  ; GTm; gapp; gze )

open import MuroBeam.BTm using (embed)
open import MuroBeam.Cex using (cex; lowerTm)
open import MuroBeam.Emit using
  ( Run; ran; Pop; pop-spawn; pop-emit; pop-deliver; pop-recv
  ; emitPops; emitAlloc; emitDeref; emitSendRoot; emitEval; emitCollect )
open import MuroBeam.Death using
  ( Meet; mt; ph-run; downH; downρ
  ; DRun; dran; base; runDs
  ; downOps; againOps; doneOps; abandonOps; sendOps
  ; settleAfterOps
  ; meetMail; meetEmpty; meetNormal )
open import MuroBeam.Event using
  ( Event; tr-alloc; tr-spend; tr-send; tr-recv; tr-spawn; tr-step; tr-collect; tr-down
  ; Why; killed; crash; normal; abandon )
open import MuroBeam.Grade using (Kept; fin-kept; ω-kept; iv-kept; selfKept; Kind; Kmove; Kcopy)
open import MuroBeam.Heap using (Obj; cell; nat; suc↑; live; free; Ref; ref)
open import MuroBeam.PSyntax using (PTm; t[]; keep; done; send; recv; spawn; await; ignore; flushT; go)
open import MuroBeam.PRun using (mailHas)
open import MuroBeam.Process using
  ( Sys; sys; heap; Proc; proc; ready; idle; ev; pr; procs; eval1; runFor; msg )
  renaming (done to pstDone)
open import MuroBeam.Sched using
  ( drive; Drove; final; oc; evs; val; findHit; inboxNat
  ; Outcome; plain; plain-halted; plain-deadlock; plain-stuck; plain-fuel )
open import MuroBeam.Show

------------------------------------------------------------------------
-- Decimal, event, fingerprint, and schedule lines live in
-- MuroBeam.Show, shared with MuroBeam.RunImage.cliRun. The wide
-- check below and `make conformance` still pin that spelling to
-- the book printer, so a change there fails this comparison.
------------------------------------------------------------------------

showMaybe : Maybe Run → String
showMaybe nothing = "nothing"
showMaybe (just (ran s es)) = "just " ++ showEvents es ++ " " ++ showFp s

showRan : Run → String
showRan (ran s es) = "ran " ++ showEvents es ++ " " ++ showFp s

-- eval1 returns a system, not a trace. just carries the fingerprint.
-- nothing is a refusal and stays the word nothing.
showStuck : Maybe Sys → String
showStuck nothing = "nothing"
showStuck (just s) = "just " ++ showFp s

line : String → String → String
line name body = name ++ ": " ++ body ++ "\n"

------------------------------------------------------------------------
-- trip. Same pops as book/trip.muro: spawn, emit, deliver, recv.
------------------------------------------------------------------------

ρ : Ref
ρ = ref zero g1 g1 (selfKept g1)

tripH0 : List Obj
tripH0 = cell (nat zero) live ∷ []

tripChild : PTm (suc zero)
tripChild = send zero (fzero {zero}) done

tripParent : PTm (suc zero)
tripParent = recv g1 g0 done

tripTm : PTm (suc zero)
tripTm = spawn (keep t[]) tripChild tripParent

s0 : Sys
s0 = sys tripH0 (proc zero ready [] [] (pr (go tripTm (ρ ∷ []) [] [] [])) ∷ [])

tripPops : List Pop
tripPops =
  pop-spawn zero ∷ pop-emit (suc zero) ∷ pop-deliver (suc zero) ∷ pop-recv zero ∷ []

------------------------------------------------------------------------
-- One alloc, one deref, one send, one eval, one collect.
-- The systems are the ones book/emit.muro pins.
------------------------------------------------------------------------

idle0 : Sys
idle0 = sys [] (proc zero ready [] [] idle ∷ [])

liveG1 : Sys
liveG1 = sys tripH0 (proc zero ready (ρ ∷ []) [] idle ∷ [])

twoG1 : Sys
twoG1 =
  sys tripH0
    (proc zero ready (ρ ∷ []) [] idle
    ∷ proc (suc zero) ready [] [] idle
    ∷ [])

emitZe : Sys
emitZe = sys [] (proc zero ready [] [] (ev (embed (gze {zero})) [] []) ∷ [])

lone : Sys
lone = sys tripH0 (proc zero ready [] [] idle ∷ [])

------------------------------------------------------------------------
-- cex, from MuroBeam.Cex. One process, empty heap, empty env.
------------------------------------------------------------------------

cexApp : GTm zero
cexApp = gapp cex gze

fuel6 : ℕ
fuel6 = suc (suc (suc (suc (suc (suc zero)))))

stuckRun : Maybe Sys
stuckRun = eval1 (runFor fuel6 (lowerTm cexApp)) zero

------------------------------------------------------------------------
-- Printer check. Fuel 8 cannot show a nine-digit nat, and a unary
-- 10^8 is not normalised. ten is two digits, so fuel 1 exhausts.
-- Remainder 10 is the bump catch-all. Digit 10 is the digit catch-all.
-- The last word is ten at fuel 8, which is 10.
------------------------------------------------------------------------

ten : ℕ
ten = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

pairText : Dig → String
pairText over = "overflow"
pairText (dig _ _) = "pair"

digitText : ℕ → String
digitText n = showText (showDigit n)

wideBody : String
wideBody =
  showAt (suc zero) ten ++ " " ++
  pairText (bump zero ten) ++ " " ++
  digitText ten ++ " " ++
  showℕ ten

------------------------------------------------------------------------
-- The death schedules project to Run through the underlying Sys.
-- Flags are not on the fingerprint. The book pins those.
------------------------------------------------------------------------

asRun : Maybe DRun → Maybe Run
asRun nothing = nothing
asRun (just (dran m es)) = just (ran (base m) es)

-- Scheduled runs. The driver chooses every pop. Fuel 16 is the
-- book's driveFuel. The cursor starts at 0 and the kept nat starts
-- empty. No pop list is written down.
------------------------------------------------------------------------

driveFuel : ℕ
driveFuel =
  suc (suc (suc (suc
  (suc (suc (suc (suc
  (suc (suc (suc (suc
  (suc (suc (suc (suc zero)))))))))))))))

-- showOc, showVal, and showDrove come from MuroBeam.Show.

schedBody : Sys → List Meet → String
schedBody s ms = showDrove (proj₁ (drive driveFuel zero ms nothing s))

igTm : PTm (suc zero)
igTm = spawn (keep t[]) tripChild (ignore (fzero {zero}) (done {suc zero}))

ig0 : Sys
ig0 = sys tripH0 (proc zero ready [] [] (pr (go igTm (ρ ∷ []) [] [] [])) ∷ [])

awTm : PTm (suc zero)
awTm = spawn (keep t[]) tripChild (await (fzero {zero}) (done {suc zero}))

aw0 : Sys
aw0 = sys tripH0 (proc zero ready [] [] (pr (go awTm (ρ ∷ []) [] [] [])) ∷ [])

deadSys : Sys
deadSys =
  sys []
    (proc zero ready [] []
      (pr (go (recv g1 g0 (done {suc zero})) [] [] [] [])) ∷ [])

stuckSys : Sys
stuckSys =
  sys []
    (proc zero ready [] []
      (pr (go (send zero (fzero {zero}) (done {suc zero})) [] [] [] [])) ∷ [])

twoTm : PTm zero
twoTm = spawn t[] (done {zero}) (done {zero})

twoSys : Sys
twoSys = sys [] (proc zero ready [] [] (pr (go twoTm [] [] [] [])) ∷ [])

threeTm : PTm zero
threeTm = spawn t[] (done {zero}) (spawn t[] (done {zero}) (done {zero}))

threeSys : Sys
threeSys = sys [] (proc zero ready [] [] (pr (go threeTm [] [] [] [])) ∷ [])

schedDownPs : List Proc
schedDownPs =
  proc zero ready [] (msg downρ ∷ [])
    (pr (go (recv g1 g0 (done {suc zero})) [] [] [] []))
  ∷ proc (suc zero) ready [] []
    (pr (go (done {zero}) [] [] [] []))
  ∷ []

schedDown : Bool → Meet
schedDown noted =
  mt (sys downH schedDownPs)
     true zero (suc zero) ph-run ph-run
     false true killed true false noted killed

-- Boolean image of `AllFree`: every cell is `nat 0` and `free`.
freeCell : Obj → Bool
freeCell (cell (nat zero) free) = true
freeCell (cell _ _) = false

allFreeB : List Obj → Bool
allFreeB [] = true
allFreeB (o ∷ os) = freeCell o ∧ allFreeB os

showBool : Bool → String
showBool true = "true"
showBool false = "false"

-- `none` is `findHit ≡ nothing`: no `At` step. It is not `¬ PStep`.
showEn : Sys → String
showEn s with findHit s
... | nothing = "none"
... | just _  = "some"

-- Delivered payload is `suc↑` of `nat 0`. The kept nat is 1.
up0 : Ref
up0 = ref zero g0 g0 (selfKept g0)

up1 : Ref
up1 = ref (suc zero) g0 g0 (selfKept g0)

upSys : Sys
upSys =
  sys (cell (nat zero) live ∷ cell (suc↑ up0) live ∷ [])
    (proc zero ready [] (msg up1 ∷ [])
      (pr (go (recv g0 g0 (done {suc zero})) [] [] [] []))
    ∷ [])

-- Tag 0 is dead and unreferenced (`ReplyDone` in `SchedThm`). The
-- child holds a g0 placeholder and an empty ether, so it cannot put
-- tag 0 back in a mailbox. `mail` is `mailHas` of that tag. `en` is
-- the enabled scan on the final system.
ph1 : Ref
ph1 = ref (suc zero) g0 g0 (selfKept g0)

straySys : Sys
straySys =
  sys (cell (nat zero) live ∷ cell (nat zero) live ∷ [])
    ( proc zero ready [] []
        (pr (go (done {zero}) [] [] (zero ∷ []) []))
    ∷ proc (suc zero) ready [] []
        (pr (go (send zero (fzero {zero}) (done {suc zero}))
              (ph1 ∷ []) [] [] []))
    ∷ [])

strayBody : String
strayBody =
  let d = proj₁ (drive driveFuel zero [] nothing straySys) in
  showDrove d ++ " mail " ++ showBool (mailHas (procs (final d)) zero zero)
    ++ " en " ++ showEn (final d)

-- One already-done process and an orphan live cell. Halt collects.
-- `free` is the boolean image of `AllFree` on the final heap.
emptySys : Sys
emptySys =
  sys (cell (nat zero) live ∷ [])
    (proc zero pstDone [] [] idle ∷ [])

emptyBody : String
emptyBody =
  let d = proj₁ (drive driveFuel zero [] nothing emptySys) in
  showDrove d ++ " free " ++ showBool (allFreeB (heap (final d)))

-- B4a console layout, written out here so Conform does not import
-- `MuroBeam.Port` (and with it PWf). pid 0 sends an ω nat 2 to pid 1,
-- which is `pstDone`, `idle`, and has an empty inbox: the process
-- `lowerIO console` appends. The console never steps. The deliver
-- lands in its inbox, pid 0 ends, and the run halts. `out` is the
-- nat of the console's first message on the final system.
consoleW : Ref
consoleW = ref zero (pt inf) (pt inf) (selfKept (pt inf))

consoleSys : Sys
consoleSys =
  sys (cell (nat (suc (suc zero))) live ∷ [])
    ( proc zero ready [] []
        (pr (go (send (suc zero) (fzero {zero}) (done {suc zero}))
              (consoleW ∷ []) [] [] []))
    ∷ proc (suc zero) pstDone [] [] idle
    ∷ [])

consoleBody : String
consoleBody =
  let d = proj₁ (drive driveFuel zero [] nothing consoleSys) in
  showDrove d ++ " out " ++ showVal (inboxNat (final d) (suc zero))

-- B4b input layout, written out the same way. pid 2 is the input
-- port after its `seq` has bound the value: it holds an ω nat 2 and
-- sends it to pid 0. pid 0 is `recv` at ω, then `done`. The console
-- at pid 1 is idle, and `out` is the nat of its first message on the
-- final system, so `v-` says input did not pass through it. The
-- port's numeral `seq` is not in this line: the book `bind` resumes
-- only a singleton `saved`, and the port's `seq` pushes `saved` over
-- an empty `seg`. A write of the received slot is left out because
-- the book normaliser takes tens of minutes on that three-process
-- run; `sched-console` is the write.
inputSys : Sys
inputSys =
  sys (cell (nat (suc (suc zero))) live ∷ [])
    ( proc zero ready [] []
        (pr (go (recv (pt inf) g0 (done {suc zero}))
              [] [] [] []))
    ∷ proc (suc zero) pstDone [] [] idle
    ∷ proc (suc (suc zero)) ready [] []
        (pr (go (send zero (fzero {zero}) (done {suc zero}))
              (consoleW ∷ []) [] [] []))
    ∷ [])

inputBody : String
inputBody =
  let d = proj₁ (drive driveFuel zero [] nothing inputSys) in
  showDrove d ++ " out " ++ showVal (inboxNat (final d) (suc zero))

-- B4c. A reply that reached the console is scrubbed by the flush.
-- pid 0 is the `flushT` of tag 0 that `arm1` writes after a
-- demonitoring `ignore`. The console at pid 1 is `pstDone`, `idle`,
-- and holds one message: the g1 reply on object 0. `consume` scrubs
-- tag 0 from every mailbox, the console's too, so `out` is `v-`.
-- `MuroBeam.Port.drive-console` is the theorem that pid 1 is still
-- `pstDone` and `idle` there; its inbox is not claimed to grow.
scrubW : Ref
scrubW = ref zero g1 g1 (selfKept g1)

scrubSys : Sys
scrubSys =
  sys (cell (nat zero) live ∷ [])
    ( proc zero ready [] []
        (pr (go (flushT zero (done {zero})) [] [] [] (zero ∷ [])))
    ∷ proc (suc zero) pstDone [] (msg scrubW ∷ []) idle
    ∷ [])

scrubBody : String
scrubBody =
  let d = proj₁ (drive driveFuel zero [] nothing scrubSys) in
  showDrove d ++ " out " ++ showVal (inboxNat (final d) (suc zero))

-- The older lines, then the scheduled ones. The driver prints this
-- and nothing else.
------------------------------------------------------------------------

report : String
report =
  line "trip" (showMaybe (emitPops tripPops s0)) ++
  line "stuck" (showStuck stuckRun) ++
  line "alloc" (showMaybe (emitAlloc idle0 zero g1 zero)) ++
  line "deref" (showMaybe (emitDeref liveG1 zero zero)) ++
  line "send" (showMaybe (emitSendRoot twoG1 zero zero (suc zero))) ++
  line "step" (showMaybe (emitEval emitZe zero)) ++
  line "collect" (showRan (emitCollect lone)) ++
  line "wide" wideBody ++
  line "down" (showMaybe (asRun (runDs downOps meetMail))) ++
  line "down-again" (showMaybe (asRun (runDs againOps meetMail))) ++
  line "down-done" (showMaybe (asRun (runDs doneOps meetEmpty))) ++
  line "abandon" (showMaybe (asRun (runDs abandonOps meetEmpty))) ++
  line "send-dead" (showMaybe (asRun (runDs sendOps meetEmpty))) ++
  line "settle-after-exit" (showMaybe (asRun (runDs settleAfterOps meetNormal))) ++
  line "sched-trip" (schedBody s0 []) ++
  line "sched-ignore" (schedBody ig0 []) ++
  line "sched-await" (schedBody aw0 []) ++
  line "sched-dead" (schedBody deadSys []) ++
  line "sched-stuck" (schedBody stuckSys []) ++
  line "sched-two" (schedBody twoSys []) ++
  line "sched-three" (schedBody threeSys []) ++
  line "sched-down" (schedBody (sys downH schedDownPs) (schedDown false ∷ [])) ++
  line "sched-down-again" (schedBody (sys downH schedDownPs) (schedDown true ∷ [])) ++
  line "sched-up" (schedBody upSys []) ++
  line "sched-stray" strayBody ++
  line "sched-empty" emptyBody ++
  line "sched-console" consoleBody ++
  line "sched-input" inputBody ++
  line "sched-scrub" scrubBody
