------------------------------------------------------------------------
-- Process syntax. No scheduler, no heap step. Process imports this.
-- PTm does not import Process, so the two do not cycle.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.PSyntax where

open import Data.Bool.Base using (Bool; true; false; _∨_; if_then_else_)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product.Base using (_×_; _,_)

open import Muro.Grade using (Grade; GTm)

open import MuroBeam.Heap using (Ref; obj)

------------------------------------------------------------------------
-- Which slots of the parent environment the child receives.
-- keep hands the variable over. skip leaves it with the parent.
------------------------------------------------------------------------

data Thin : ℕ → ℕ → Set where
  t[]  : Thin zero zero
  keep : ∀ {m n} → Thin m n → Thin (suc m) (suc n)
  skip : ∀ {m n} → Thin m n → Thin m (suc n)

------------------------------------------------------------------------
-- Process term. The tagged forms are what spawn writes once the
-- reply reference has an object index. They are not surface syntax
-- a caller has to build, except as the states the traces step through.
------------------------------------------------------------------------

data PTm (n : ℕ) : Set where
  done    : PTm n
  send    : ℕ → Fin n → PTm n → PTm n
  recv    : Grade → Grade → PTm (suc n) → PTm n
  spawn   : ∀ {m} → Thin m n → PTm m → PTm n → PTm n
  seq     : GTm n → PTm (suc n) → PTm n
  await   : Fin n → PTm n → PTm n
  ignore  : Fin n → PTm n → PTm n
  nignore : Fin n → PTm n → PTm n
  awaitT  : ℕ → PTm n → PTm n
  ignoreT : ℕ → PTm n → PTm n
  flushT  : ℕ → PTm n → PTm n
  ncheckT : ℕ → PTm n → PTm n
  ndemonT : ℕ → PTm n → PTm n

-- The root of the parent continuation is the protocol consumer.
isProtoAt : ∀ {n} → ℕ → PTm n → Bool
isProtoAt i (await x _)   = toℕ x ≡ᵇ i
isProtoAt i (ignore x _)  = toℕ x ≡ᵇ i
isProtoAt i (nignore x _) = toℕ x ≡ᵇ i
isProtoAt _ _             = false

markProto : ∀ {n} → ℕ → ℕ → PTm n → PTm n
markProto i τ (await x k)   = if toℕ x ≡ᵇ i then awaitT τ k else await x k
markProto i τ (ignore x k)  = if toℕ x ≡ᵇ i then ignoreT τ k else ignore x k
markProto i τ (nignore x k) = if toℕ x ≡ᵇ i then ncheckT τ k else nignore x k
markProto _ _ p             = p

applyMoves : ∀ {n} → List (ℕ × ℕ) → PTm n → PTm n
applyMoves []              p = p
applyMoves ((i , τ) ∷ mv)  p = applyMoves mv (markProto i τ p)

------------------------------------------------------------------------
-- A flight is a message the sender has emitted and nobody has
-- delivered. The reference stays in the sender's control until then.
------------------------------------------------------------------------

data Flight : Set where
  flight : (dst : ℕ) (r : Ref) → Flight

flightRef : Flight → Ref
flightRef (flight _ r) = r

flightRefs : List Flight → List Ref
flightRefs []                    = []
flightRefs (flight _ r ∷ fs)     = r ∷ flightRefs fs

data Code : Set where
  go : ∀ {n} → PTm n → List Ref → List Flight → List ℕ → List ℕ → Code

codeEnv : Code → List Ref
codeEnv (go _ env _ _ _) = env

codeEth : Code → List Flight
codeEth (go _ _ eth _ _) = eth

codeDead : Code → List ℕ
codeDead (go _ _ _ d _) = d

codeDemo : Code → List ℕ
codeDemo (go _ _ _ _ m) = m

codeRefs : Code → List Ref
codeRefs (go _ env eth _ _) = env ++ flightRefs eth

hasTag : ℕ → List ℕ → Bool
hasTag _ []       = false
hasTag τ (x ∷ xs) = (x ≡ᵇ τ) ∨ hasTag τ xs
