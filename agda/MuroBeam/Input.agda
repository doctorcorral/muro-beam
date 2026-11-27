------------------------------------------------------------------------
-- B4b host input. What the host hands a format-4 image, and the
-- process term that delivers it.
--
-- The input is a list of naturals the host reads before the run
-- (`readInput`: decimal numerals separated by spaces, tabs, or line
-- breaks). `inputP` is the process the input port runs: for each
-- value, a `seq` that evaluates its numeral and a `send` of that slot
-- to pid 0, in order, then `done`. Nothing new enters `PTm`, `PStep`,
-- `checkP`, or the CEK: the port is an ordinary process, and a read
-- is the program's own `recv`. `MuroBeam.Port` puts this process at
-- pid 2 for a format-4 image.
--
-- What this module proves:
--   * `input-vals`: reading the sends back out of `inputP xs` gives
--     `xs`. Each send goes to pid 0 and carries the slot its `seq`
--     just bound, and the values are in the order the host read them.
-- Not proved: that `checkP` accepts `inputP xs` for every `xs` (the
-- port is not a loaded program; `inputP-ok` pins one list), or that a
-- run delivers every value before it stops.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Input where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.Fin.Base using (Fin) renaming (zero to fzero)
open import Data.List.Base using (List; []; _∷_; reverse)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
open import Data.Vec.Base using () renaming ([] to v[])
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.String.Base using (String; toList)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Result; ok; fail)

open import MuroBeam.BTm using (BTm; gze; gsu)
open import MuroBeam.PSyntax using (PTm; done; send; seq)
open import MuroBeam.PTm using (checkP)

------------------------------------------------------------------------
-- The port process.
------------------------------------------------------------------------

-- `gsu` over `gze`. The CEK evaluates it in about `2n + 1` steps and
-- allocates `n + 1` cells, so a large value costs fuel.
numeral : ∀ {n} → ℕ → BTm n
numeral zero    = gze
numeral (suc k) = gsu (numeral k)

-- Each value is bound by a `seq` with empty defs and sent from slot 0
-- to pid 0. The `seq` binder is ω (its continuation is a `send`, not
-- a reply root), so the send is `Kcopy`.
inputP : ∀ {n} → List ℕ → PTm n
inputP []       = done
inputP (x ∷ xs) = seq [] (numeral x) (send zero fzero (inputP xs))

------------------------------------------------------------------------
-- Reading the port back.
------------------------------------------------------------------------

unnum : ∀ {n} → BTm n → Maybe ℕ
unnum gze     = just zero
unnum (gsu e) = unnum e >>= λ k → just (suc k)
unnum _       = nothing

-- The values a port term sends, if it has the port shape: `seq` with
-- empty defs, then `send` to pid 0 of slot 0, then the rest.
inputVals : ∀ {n} → PTm n → Maybe (List ℕ)
inputVals done = just []
inputVals (seq [] e (send zero fzero k)) =
  unnum e >>= λ v → inputVals k >>= λ vs → just (v ∷ vs)
inputVals _ = nothing

unnum-numeral : ∀ {n} k → unnum {n} (numeral k) ≡ just k
unnum-numeral zero = refl
unnum-numeral {n} (suc k) rewrite unnum-numeral {n} k = refl

input-vals : ∀ {n} xs → inputVals {n} (inputP xs) ≡ just xs
input-vals []                = refl
input-vals {n} (x ∷ xs)
  rewrite unnum-numeral {n} x | input-vals {suc n} xs = refl

------------------------------------------------------------------------
-- What the host reads. Decimal digits, separated by one or more
-- spaces, tabs, carriage returns, or line feeds. Leading and trailing
-- separators are allowed, and an empty text is the empty list. Any
-- other character is `bad input`. Leading zeros are read as the
-- number (`007` is 7).
------------------------------------------------------------------------

digit : Char → Maybe ℕ
digit '0' = just 0
digit '1' = just 1
digit '2' = just 2
digit '3' = just 3
digit '4' = just 4
digit '5' = just 5
digit '6' = just 6
digit '7' = just 7
digit '8' = just 8
digit '9' = just 9
digit _   = nothing

isSep : Char → Bool
isSep ' '  = true
isSep '\t' = true
isSep '\n' = true
isSep '\r' = true
isSep _    = false

push : Maybe ℕ → List ℕ → List ℕ
push nothing  acc = acc
push (just n) acc = n ∷ acc

grow : Maybe ℕ → ℕ → ℕ
grow nothing  d = d
grow (just n) d = n * 10 + d

-- `cur` is the numeral being read, `acc` the finished ones reversed.
readGo : List Char → Maybe ℕ → List ℕ → Result (List ℕ)
readGo []       cur acc = ok (reverse (push cur acc))
readGo (c ∷ cs) cur acc with digit c
... | just d  = readGo cs (just (grow cur d)) acc
... | nothing with isSep c
... | true  = readGo cs nothing (push cur acc)
... | false = fail "bad input"

readInput : String → Result (List ℕ)
readInput s = readGo (toList s) nothing []

------------------------------------------------------------------------
-- One closed check. `checkP` is not run on the port at boot; this pin
-- says a two-value port, `3` then `0`, is a term `load` would accept.
------------------------------------------------------------------------

inputP-ok : checkP v[] (inputP {zero} (3 ∷ 0 ∷ [])) ≡ ok v[]
inputP-ok = refl
