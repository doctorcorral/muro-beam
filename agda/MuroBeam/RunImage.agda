------------------------------------------------------------------------
-- Run one pure image on pid 0. `seq1` once, then `runFor`. The
-- value sits on the `saved` frame; `bind` and `done` are not taken.
-- This is the test harness, not the CLI.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.RunImage where

open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.String.Base using (String; _++_; fromList)
open import Muro.Base using (Result; ok; fail)

open import MuroBeam.Heap using (Obj; Val; nat; suc↑; clo; Ref; obj)
open import MuroBeam.Image using (showImage; showNat)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.Load using (load)
open import MuroBeam.Parse using (parse)
open import MuroBeam.PRun using (seq1)
open import MuroBeam.PTm using (lowerP)
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
