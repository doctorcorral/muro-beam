------------------------------------------------------------------------
-- Run one pure image.
--
-- `runImage` is the pid-0 harness: `seq1` once, then `runFor`. The
-- value sits on the `saved` frame; `bind` and `done` are not taken.
--
-- `cliRun` is what the `muro-beam` binary calls. It `load`s the text
-- and runs `drive` at the fuel the caller passes. The Haskell main
-- in `scripts/build_runner.py` reads the path and the fuel. That
-- main is not an Agda module, so the audit still sees only `--safe`
-- files. A pure entry stops `stuck`: `seq1` pushes `saved` over
-- `seg`, and `bind1` does not resume that stack. The nat `drive`
-- kept is the value on that `rv`. The tag `fuel` is `outOfFuel`.
-- The tag `load` is a `fail` from `load`, and no schedule is run.
-- The line under the tag is the outcome, the events, the
-- fingerprint, and the kept nat, in the same spelling as
-- `MuroBeam.Conform.showDrove`. Decimals are `showNat`. On the
-- numerals these runs print, that is the same text as the book
-- printer. A numeral the book printer spells `overflow` is not a
-- value this line produces.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.RunImage where

open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product.Base using (proj₁)
open import Data.String.Base using (String; _++_; fromList)
open import Muro.Base using (Result; ok; fail)
open import Muro.Grade using (Grade; Point; fin; inf; pt; iv)

open import MuroBeam.Event using
  ( Event; Why; killed; crash; normal; abandon
  ; tr-alloc; tr-spend; tr-send; tr-recv; tr-spawn; tr-step; tr-collect; tr-down )
open import MuroBeam.Grade using (Kind; Kmove; Kcopy; Kept; fin-kept; ω-kept; iv-kept)
open import MuroBeam.Heap using
  ( Obj; Val; nat; suc↑; clo; Ref; ref; obj; status; live; free )
open import MuroBeam.Image using (showImage; showNat)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.Load using (load)
open import MuroBeam.Parse using (parse)
open import MuroBeam.PRun using (seq1)
open import MuroBeam.PTm using (lowerP)
open import MuroBeam.Sched using
  ( drive; Drove; oc; val; evs; final; plain; Outcome
  ; plain-halted; plain-deadlock; plain-stuck; plain-fuel )
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
-- pushes `saved` over `seg`, and `bind1` does not resume that stack,
-- so a pure entry can stop `stuck` with the nat already in `rv`.
-- The text is the outcome and the nat `drive` kept.

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

-- 32.
imgFuel : ℕ
imgFuel = dbl (dbl (dbl (dbl (dbl (suc zero)))))

ocText : ∀ {t} → Outcome t → String
ocText o with plain o
... | plain-halted   = "halted"
... | plain-deadlock = "deadlock"
... | plain-stuck i  = "stuck " ++ fromList (showNat i)
... | plain-fuel     = "fuel"

valText : Maybe ℕ → String
valText nothing  = "v-"
valText (just n) = "v" ++ fromList (showNat n)

driveImage : String → String
driveImage src with load src
... | fail e = "refuse: " ++ e
... | ok p   =
  let d = proj₁ (drive imgFuel zero [] nothing (lowerP p))
  in ocText (oc d) ++ " " ++ valText (val d)

------------------------------------------------------------------------
-- The line `muro-beam` prints. Same fields as `showDrove`: outcome,
-- events, fingerprint, kept nat. `seq` and `bind` emit no event.
-- `eval` emits `tr-step`. A halt emits `tr-collect`. A pure image
-- does not halt.
------------------------------------------------------------------------

natS : ℕ → String
natS n = fromList (showNat n)

liveCount : List Obj → ℕ
liveCount [] = zero
liveCount (o ∷ os) with status o
... | live = suc (liveCount os)
... | free = liveCount os

fpText : Sys → String
fpText s =
  "h" ++ natS (length (heap s)) ++ "l" ++ natS (liveCount (heap s))
  ++ "p" ++ natS (length (procs s))

showPoint : Point → String
showPoint (fin n) = "fin(" ++ natS n ++ ")"
showPoint inf = "inf"

showGrade : Grade → String
showGrade (pt p) = "pt(" ++ showPoint p ++ ")"
showGrade (iv a b) = "iv(" ++ showPoint a ++ "," ++ showPoint b ++ ")"

showLe : ∀ {m n} → m ≤ n → String
showLe {zero} {n} z≤n = "le-zero(" ++ natS n ++ ")"
showLe {suc m} {suc n} (s≤s p) = "le-suc(" ++ natS m ++ "," ++ natS n ++ "," ++ showLe p ++ ")"
showLe {suc _} {zero} ()

showKept : ∀ {r c} → Kept r c → String
showKept (fin-kept {k} {n} le) =
  "fin-kept(" ++ natS k ++ "," ++ natS n ++ "," ++ showLe le ++ ")"
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
  "ref(" ++ natS o ++ "," ++ showGrade c ++ "," ++ showGrade r ++ "," ++ showKept k ++ ")"

showNatTail : List ℕ → String
showNatTail [] = ""
showNatTail (n ∷ rest) = " " ++ natS n ++ showNatTail rest

showNatBody : List ℕ → String
showNatBody [] = ""
showNatBody (n ∷ rest) = natS n ++ showNatTail rest

showEvent : Event → String
showEvent (tr-alloc i g) = "tr-alloc " ++ natS i ++ " " ++ showGrade g
showEvent (tr-spend i b a) = "tr-spend " ++ natS i ++ " " ++ showGrade b ++ " " ++ showGrade a
showEvent (tr-send s d r kd) =
  "tr-send " ++ natS s ++ " " ++ natS d ++ " " ++ showRef r ++ " " ++ showKind kd
showEvent (tr-recv i r) = "tr-recv " ++ natS i ++ " " ++ showRef r
showEvent (tr-spawn p c) = "tr-spawn " ++ natS p ++ " " ++ natS c
showEvent (tr-step i) = "tr-step " ++ natS i
showEvent (tr-collect ns) = "tr-collect(" ++ showNatBody ns ++ ")"
showEvent (tr-down o d w) =
  "tr-down " ++ natS o ++ " " ++ natS d ++ " " ++ showWhy w

showTail : List Event → String
showTail [] = ""
showTail (e ∷ rest) = ", " ++ showEvent e ++ showTail rest

showBody : List Event → String
showBody [] = ""
showBody (e ∷ rest) = showEvent e ++ showTail rest

showEvents : List Event → String
showEvents es = "[" ++ showBody es ++ "]"

lineOf : Drove → String
lineOf d =
  ocText (oc d) ++ " " ++ showEvents (evs d) ++ " " ++
  fpText (final d) ++ " " ++ valText (val d)

-- `ok` is a finished schedule: halted, deadlock, or stuck.
-- `fuel` is `outOfFuel`, and the next line is the partial schedule.
-- `load` is the reason `load` returned. No schedule is run.
mark : ∀ {t} → Outcome t → String
mark o with plain o
... | plain-fuel     = "fuel"
... | plain-halted   = "ok"
... | plain-deadlock = "ok"
... | plain-stuck _  = "ok"

cliBody : Drove → String
cliBody d = mark (oc d) ++ "\n" ++ lineOf d

cliRun : String → ℕ → String
cliRun src fuel with load src
... | fail e = "load\n" ++ e
... | ok p   = cliBody (proj₁ (drive fuel zero [] nothing (lowerP p)))
