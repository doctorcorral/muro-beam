------------------------------------------------------------------------
-- Closed traces for the MAlonzo comparison.
--
-- The strings are the encoding in book/show.muro. Nothing here is a
-- proof: the Haskell driver prints `report`, and the book prints the
-- same lines by normalising its show definitions. A refusal is the
-- word nothing. A successful Maybe Run is just and the events. collect
-- is total, so that line is ran.
--
-- Example and Lower are not imported. Both reach Unique. The cex term
-- is copied from Example, and lower is the three-line system Lower
-- builds for one closed term. PExample, Stray, and PWf stay out.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Conform where

open import Data.Fin.Base using () renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.String.Base using (String; _++_)

open import Muro.Grade using
  ( Grade; Point; fin; inf; pt; iv; g0; g1; gω; aff
  ; GTm; gvar; glam; gapp; gze )

open import MuroBeam.Emit using
  ( Run; ran; Pop; pop-spawn; pop-emit; pop-deliver; pop-recv
  ; emitPops; emitAlloc; emitDeref; emitSendRoot; emitEval; emitCollect )
open import MuroBeam.Event using
  ( Event; tr-alloc; tr-spend; tr-send; tr-recv; tr-spawn; tr-step; tr-collect )
open import MuroBeam.Grade using (Kept; fin-kept; ω-kept; iv-kept; selfKept; Kind; Kmove; Kcopy)
open import MuroBeam.Heap using (Obj; cell; Val; nat; Status; live; Ref; ref)
open import MuroBeam.PSyntax using (PTm; t[]; keep; done; send; recv; spawn; go)
open import MuroBeam.Process using (Sys; sys; proc; ready; idle; ev; pr; eval1; runFor)

------------------------------------------------------------------------
-- Decimal, same division as book/show.muro. Eight digits is enough
-- for these examples. Data.Nat.Show is not used: its text is not the
-- book's, and this walk stays on Data.Nat.Base.
------------------------------------------------------------------------

data Dig : Set where
  dig : ℕ → ℕ → Dig

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
bump q (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = dig q zero

div10 : ℕ → Dig
div10 zero = dig zero zero
div10 (suc n) = add1 (div10 n)
  where
  add1 : Dig → Dig
  add1 (dig q r) = bump q r

-- Eight successors. A longer number prints no digits on both sides.
shFuel : ℕ
shFuel = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

digits : ℕ → ℕ → List ℕ
digits zero _ = []
digits (suc f) n with div10 n
... | dig zero r = r ∷ []
... | dig (suc k) r = r ∷ digits f (suc k)

showDigit : ℕ → String
showDigit zero = "0"
showDigit (suc zero) = "1"
showDigit (suc (suc zero)) = "2"
showDigit (suc (suc (suc zero))) = "3"
showDigit (suc (suc (suc (suc zero)))) = "4"
showDigit (suc (suc (suc (suc (suc zero))))) = "5"
showDigit (suc (suc (suc (suc (suc (suc zero)))))) = "6"
showDigit (suc (suc (suc (suc (suc (suc (suc zero))))))) = "7"
showDigit (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = "8"
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = "9"
showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = "bad"

revDigits : List ℕ → String
revDigits [] = ""
revDigits (d ∷ rest) = revDigits rest ++ showDigit d

showℕ : ℕ → String
showℕ n = revDigits (digits shFuel n)

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

showTail : List Event → String
showTail [] = ""
showTail (e ∷ rest) = ", " ++ showEvent e ++ showTail rest

showBody : List Event → String
showBody [] = ""
showBody (e ∷ rest) = showEvent e ++ showTail rest

showEvents : List Event → String
showEvents es = "[" ++ showBody es ++ "]"

showMaybe : Maybe Run → String
showMaybe nothing = "nothing"
showMaybe (just (ran _ es)) = "just " ++ showEvents es

showRan : Run → String
showRan (ran _ es) = "ran " ++ showEvents es

-- eval1 returns a system, not a trace. just carries no events.
showStuck : Maybe Sys → String
showStuck nothing = "nothing"
showStuck (just _) = "just"

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
emitZe = sys [] (proc zero ready [] [] (ev (gze {zero}) [] []) ∷ [])

lone : Sys
lone = sys tripH0 (proc zero ready [] [] idle ∷ [])

------------------------------------------------------------------------
-- cex, copied from Example. One process, empty heap, empty env.
------------------------------------------------------------------------

lowerTm : ∀ {n} → GTm n → Sys
lowerTm t = sys [] (proc zero ready [] [] (ev t [] []) ∷ [])

cex : GTm zero
cex =
  glam g1 g0
    (gapp
      (glam gω g0 (gapp (gvar fzero) (gvar fzero)))
      (glam aff g0 (gvar (fsuc fzero))))

cexApp : GTm zero
cexApp = gapp cex gze

fuel6 : ℕ
fuel6 = suc (suc (suc (suc (suc (suc zero)))))

stuckRun : Maybe Sys
stuckRun = eval1 (runFor fuel6 (lowerTm cexApp)) zero

------------------------------------------------------------------------
-- Seven lines. The driver prints this and nothing else.
------------------------------------------------------------------------

report : String
report =
  line "trip" (showMaybe (emitPops tripPops s0)) ++
  line "stuck" (showStuck stuckRun) ++
  line "alloc" (showMaybe (emitAlloc idle0 zero g1 zero)) ++
  line "deref" (showMaybe (emitDeref liveG1 zero zero)) ++
  line "send" (showMaybe (emitSendRoot twoG1 zero zero (suc zero))) ++
  line "step" (showMaybe (emitEval emitZe zero)) ++
  line "collect" (showRan (emitCollect lone))
