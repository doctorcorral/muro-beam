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
-- heap's freeness.
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
open import MuroBeam.PSyntax using (PTm; t[]; keep; done; send; recv; spawn; await; ignore; go)
open import MuroBeam.PRun using (mailHas)
open import MuroBeam.Process using
  ( Sys; sys; heap; Proc; proc; ready; idle; ev; pr; procs; eval1; runFor; msg )
  renaming (done to pstDone)
open import MuroBeam.Sched using
  ( drive; Drove; final; oc; evs; val; findHit
  ; Outcome; plain; plain-halted; plain-deadlock; plain-stuck; plain-fuel )

------------------------------------------------------------------------
-- Decimal, same division as book/show.muro. Eight digits is enough
-- for these examples. Fuel exhaustion, a remainder past 9, and a
-- digit past 9 print overflow, not a truncated or empty numeral.
-- Data.Nat.Show is not used: its text is not the book's, and this
-- walk stays on Data.Nat.Base.
------------------------------------------------------------------------

data Dig : Set where
  dig : ℕ → ℕ → Dig
  over : Dig

bump : ℕ → ℕ → Dig
bump q zero = dig q (suc zero)
bump q (suc zero) = dig q (suc (suc zero))
bump q (suc (suc zero)) = dig q (suc (suc (suc zero)))
bump q (suc (suc (suc zero))) = dig q (suc (suc (suc (suc zero))))
bump q (suc (suc (suc (suc zero)))) = dig q (suc (suc (suc (suc (suc zero)))))
bump q (suc (suc (suc (suc (suc zero))))) = dig q (suc (suc (suc (suc (suc (suc zero))))))
bump q (suc (suc (suc (suc (suc (suc zero)))))) = dig q (suc (suc (suc (suc (suc (suc (suc zero)))))))
bump q (suc (suc (suc (suc (suc (suc (suc zero))))))) = dig q (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
bump q (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = dig q (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
bump q (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = dig (suc q) zero
bump q (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = over

div10 : ℕ → Dig
div10 zero = dig zero zero
div10 (suc n) = add1 (div10 n)
  where
  add1 : Dig → Dig
  add1 over = over
  add1 (dig q r) = bump q r

-- Eight successors. A longer number prints overflow on both sides.
shFuel : ℕ
shFuel = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

consDigit : ℕ → Maybe (List ℕ) → Maybe (List ℕ)
consDigit _ nothing = nothing
consDigit r (just xs) = just (r ∷ xs)

digits : ℕ → ℕ → Maybe (List ℕ)
digits zero _ = nothing
digits (suc f) n with div10 n
... | over = nothing
... | dig zero r = just (r ∷ [])
... | dig (suc k) r = consDigit r (digits f (suc k))

showDigit : ℕ → Maybe String
showDigit zero = just "0"
showDigit (suc zero) = just "1"
showDigit (suc (suc zero)) = just "2"
showDigit (suc (suc (suc zero))) = just "3"
showDigit (suc (suc (suc (suc zero)))) = just "4"
showDigit (suc (suc (suc (suc (suc zero))))) = just "5"
showDigit (suc (suc (suc (suc (suc (suc zero)))))) = just "6"
showDigit (suc (suc (suc (suc (suc (suc (suc zero))))))) = just "7"
showDigit (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = just "8"
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = just "9"
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = nothing

revDigits : List ℕ → Maybe String
revDigits [] = just ""
revDigits (d ∷ rest) with showDigit d
... | nothing = nothing
... | just ch with revDigits rest
... | nothing = nothing
... | just pre = just (pre ++ ch)

showText : Maybe String → String
showText nothing = "overflow"
showText (just s) = s

forceRev : Maybe (List ℕ) → Maybe String
forceRev nothing = nothing
forceRev (just xs) = revDigits xs

showAt : ℕ → ℕ → String
showAt f n = showText (forceRev (digits f n))

showℕ : ℕ → String
showℕ n = showAt shFuel n

showPoint : Point → String
showPoint (fin n) = "fin(" ++ showℕ n ++ ")"
showPoint inf = "inf"

showGrade : Grade → String
showGrade (pt p) = "pt(" ++ showPoint p ++ ")"
showGrade (iv a b) = "iv(" ++ showPoint a ++ "," ++ showPoint b ++ ")"

showLe : ∀ {m n} → m ≤ n → String
showLe {zero} {n} z≤n = "le-zero(" ++ showℕ n ++ ")"
showLe {suc m} {suc n} (s≤s p) = "le-suc(" ++ showℕ m ++ "," ++ showℕ n ++ "," ++ showLe p ++ ")"
showLe {suc _} {zero} ()

showKept : ∀ {r c} → Kept r c → String
showKept (fin-kept {k} {n} le) = "fin-kept(" ++ showℕ k ++ "," ++ showℕ n ++ "," ++ showLe le ++ ")"
showKept ω-kept = "omega-kept"
showKept (iv-kept {a} {b}) = "iv-kept(" ++ showPoint a ++ "," ++ showPoint b ++ ")"

showKind : Kind → String
showKind Kmove = "Kmove"
showKind Kcopy = "Kcopy"

showWhy : Why → String
showWhy killed  = "killed"
showWhy crash   = "crash"
showWhy normal  = "normal"
showWhy abandon = "abandon"

showRef : Ref → String
showRef (ref o c r k) =
  "ref(" ++ showℕ o ++ "," ++ showGrade c ++ "," ++ showGrade r ++ "," ++ showKept k ++ ")"

showNatTail : List ℕ → String
showNatTail [] = ""
showNatTail (n ∷ rest) = " " ++ showℕ n ++ showNatTail rest

showNatBody : List ℕ → String
showNatBody [] = ""
showNatBody (n ∷ rest) = showℕ n ++ showNatTail rest

showEvent : Event → String
showEvent (tr-alloc i g) = "tr-alloc " ++ showℕ i ++ " " ++ showGrade g
showEvent (tr-spend i b a) = "tr-spend " ++ showℕ i ++ " " ++ showGrade b ++ " " ++ showGrade a
showEvent (tr-send s d r kd) = "tr-send " ++ showℕ s ++ " " ++ showℕ d ++ " " ++ showRef r ++ " " ++ showKind kd
showEvent (tr-recv i r) = "tr-recv " ++ showℕ i ++ " " ++ showRef r
showEvent (tr-spawn p c) = "tr-spawn " ++ showℕ p ++ " " ++ showℕ c
showEvent (tr-step i) = "tr-step " ++ showℕ i
showEvent (tr-collect ns) = "tr-collect(" ++ showNatBody ns ++ ")"
showEvent (tr-down o d w) =
  "tr-down " ++ showℕ o ++ " " ++ showℕ d ++ " " ++ showWhy w

showTail : List Event → String
showTail [] = ""
showTail (e ∷ rest) = ", " ++ showEvent e ++ showTail rest

showBody : List Event → String
showBody [] = ""
showBody (e ∷ rest) = showEvent e ++ showTail rest

showEvents : List Event → String
showEvents es = "[" ++ showBody es ++ "]"

-- Heap length, live cells, process count. Not payloads or control.
liveCount : List Obj → ℕ
liveCount [] = zero
liveCount (cell _ live ∷ os) = suc (liveCount os)
liveCount (cell _ free ∷ os) = liveCount os

showFp : Sys → String
showFp (sys h ps) =
  "h" ++ showℕ (length h) ++ "l" ++ showℕ (liveCount h) ++ "p" ++ showℕ (length ps)

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

showOc : ∀ {t} → Outcome t → String
showOc o with plain o
... | plain-halted    = "halted"
... | plain-deadlock  = "deadlock"
... | plain-stuck i   = "stuck " ++ showℕ i
... | plain-fuel      = "fuel"

showVal : Maybe ℕ → String
showVal nothing  = "v-"
showVal (just n) = "v" ++ showℕ n

showDrove : Drove → String
showDrove d =
  showOc (oc d) ++ " " ++ showEvents (evs d) ++ " " ++
  showFp (final d) ++ " " ++ showVal (val d)

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
  line "sched-empty" emptyBody
