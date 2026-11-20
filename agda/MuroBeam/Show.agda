------------------------------------------------------------------------
-- Shared event and schedule printer.
--
-- The decimal walk and the event spelling are the ones
-- book/show.muro prints. Eight digits is enough for these
-- examples. Fuel exhaustion, a remainder past 9, and a digit
-- past 9 print overflow, not a truncated or empty numeral.
-- Data.Nat.Show is not used: its text is not the book's, and
-- this walk stays on Data.Nat.Base.
--
-- MuroBeam.Conform and MuroBeam.RunImage both open this
-- module, so the book comparison (`make conformance`) and the
-- `muro-beam` line cannot drift from each other. `cliRun`
-- prints `showDrove`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Show where

open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.String.Base using (String; _++_)

open import Muro.Grade using (Grade; Point; fin; inf; pt; iv)

open import MuroBeam.Event using
  ( Event; Why; killed; crash; normal; abandon
  ; tr-alloc; tr-spend; tr-send; tr-recv; tr-spawn; tr-step; tr-collect; tr-down )
open import MuroBeam.Grade using (Kind; Kmove; Kcopy; Kept; fin-kept; ω-kept; iv-kept)
open import MuroBeam.Heap using (Obj; cell; live; free; Ref; ref)
open import MuroBeam.Process using (Sys; sys)
open import MuroBeam.Sched using
  ( Drove; oc; val; evs; final; plain; Outcome
  ; plain-halted; plain-deadlock; plain-stuck; plain-fuel )

------------------------------------------------------------------------
-- Decimal, same division as book/show.muro. Eight digits is enough
-- for these examples. Fuel exhaustion, a remainder past 9, and a
-- digit past 9 print overflow, not a truncated or empty numeral.
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

showOc : ∀ {t} → Outcome t → String
showOc o with plain o
... | plain-halted    = "halted"
... | plain-deadlock  = "deadlock"
... | plain-stuck i   = "stuck " ++ showℕ i
... | plain-fuel      = "fuel"

showVal : Maybe ℕ → String
showVal nothing  = "v-"
showVal (just n) = "v" ++ showℕ n

-- The line `muro-beam` prints and the scheduled book lines share.
showDrove : Drove → String
showDrove d =
  showOc (oc d) ++ " " ++ showEvents (evs d) ++ " " ++
  showFp (final d) ++ " " ++ showVal (val d)
