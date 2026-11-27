------------------------------------------------------------------------
-- B4a host output and B4b host input. A format-3 image runs with
-- one host port, the console, at pid 1; a format-4 image adds the
-- input port at pid 2 (B4b, below). The console is an ordinary
-- `Proc`: state `pstDone`, control `idle`, no roots, and an empty
-- inbox. A `send`
-- to pid 1 is the existing `emit1` / `deliver1` pair, so a write is a
-- `PStep` and nothing new enters `PStep`, `checkP`, or the CEK.
-- `deliver1` appends to a `pstDone` inbox and `wake` leaves the state,
-- so the console stays `pstDone` and `drive` can still halt. What the
-- host prints is that inbox, in delivery order, read from the system
-- `drive` returns.
--
-- Pids: entry 0, console 1, so the first `spawn` is pid 2. A format 1
-- or 2 image has no console, and a send to pid 1 there is the
-- old behaviour (`blocked` when no process 1 exists).
--
-- What this module proves:
--   * `lowerIO-wf` / `lowerIO-safe`: the console layout is `WF`, and
--     every `PStep*` from it stays `WF`. Same statement as
--     `lowerP-safe`; the console holds no reference.
--   * `idle-quiet`: a `pstDone` process with `idle` control has no
--     enabled wrapper, whatever its inbox. The console is never
--     scheduled while it has that shape.
--   * `io-final-wf`: the system `drive` returns from `lowerIO` is
--     `WF`, so the inbox the host prints is read off a `WF` state.
-- Not proved: that every step keeps pid 1 `pstDone` and `idle`, that
-- its inbox only grows, or that a run delivers every flight before
-- it stops. Output after `fuel`, `deadlock`, or `stuck` is what was
-- delivered by then.
--
-- B4b host input. A format-4 image (`stdio`) is the console layout
-- plus one more process, the input port, at pid 2: state `ready`, no
-- roots, an empty inbox, and the control of the closed term
-- `MuroBeam.Input.inputP xs` over the values the host read. It sends
-- each value to pid 0 with the existing `seq` / `emit1` / `deliver1`
-- steps and then ends. A read is the program's own `recv`. Pids:
-- entry 0, console 1, input 2, so the first `spawn` is pid 3.
-- `lowerIn xs` is the layout with input `xs`; `lowerIO` is `lowerIn []`.
--   * `lowerIn-wf` / `lowerIn-safe` / `in-final-wf`: the same three
--     facts for every input. The port's control holds no reference
--     (`lowerIn-refs`), so the layout is `WF` with an empty heap.
--   * `input-at`: pid 2 of the `stdio` layout is `inputProc xs`, and
--     `MuroBeam.Input.input-vals` reads `xs` back out of its term.
-- Not proved: that the port's values all reach pid 0 before the run
-- stops, or anything about the order of the port's sends relative to
-- other senders to pid 0. A program that receives more values than
-- the host gave parks on an empty inbox.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Port where

open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans)

open import MuroBeam.Heap using (Obj; Ref; obj; nat; suc↑; clo; con; bnil; uniq-nil)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.Process using
  ( Sys; sys; heap; procs; Proc; proc; inbox; Msg; msg
  ; idle; ready; pr; refsOf; AllInv; residual-inv-refs; payloadAt )
  renaming (done to pstDone)
open import MuroBeam.PSyntax using (go)
open import MuroBeam.Input using (inputP)
open import MuroBeam.PRun using (PStep*)
open import MuroBeam.PTm using (CheckedP; lowerP)
open import MuroBeam.PWf using (psteps)
open import MuroBeam.Unique using (WF)
open import MuroBeam.Sched using
  ( K; k-deliver; k-seq; k-bind; k-spawn; k-emit; k-await; k-arm
  ; k-flush; k-npeek; k-ndemon; k-recv; k-done; k-eval
  ; emitK; firstHit; res; yes; no; enabled; spine
  ; drive; Drove; drv; Outcome; drive-sound )

------------------------------------------------------------------------
-- Which host ports an image asks for. Only the format number selects
-- them: 3 is the console layout, 4 is the console and the input port
-- (`stdio`), every other accepted format is none.
------------------------------------------------------------------------

data Ports : Set where
  none    : Ports
  console : Ports
  stdio   : Ports

portsOf : ℕ → Ports
portsOf (suc (suc (suc zero)))       = console
portsOf (suc (suc (suc (suc zero)))) = stdio
portsOf _                            = none

console-pid : ℕ
console-pid = suc zero

-- The console process. `pstDone` so `allDone` does not wait on it,
-- `idle` so no wrapper fires on it (`idle-quiet`).
consoleProc : Proc
consoleProc = proc console-pid pstDone [] [] idle

input-pid : ℕ
input-pid = suc (suc zero)

-- The input port (B4b). `ready`, so the scheduler runs it; its
-- control is the closed port term over the host's values, with an
-- empty environment, so it holds no reference at boot.
inputProc : List ℕ → Proc
inputProc xs = proc input-pid ready [] [] (pr (go (inputP {zero} xs) [] [] [] []))

-- `lowerP` plus the ports after the entry. `none` is `lowerP`. The
-- input `xs` only reaches the `stdio` layout.
lowerIn : List ℕ → Ports → CheckedP → Sys
lowerIn _  none    p = lowerP p
lowerIn _  console p = sys (heap (lowerP p)) (procs (lowerP p) ++ consoleProc ∷ [])
lowerIn xs stdio   p =
  sys (heap (lowerP p)) (procs (lowerP p) ++ consoleProc ∷ inputProc xs ∷ [])

-- The layout with no host input. Formats 1 to 3 never see input, and a
-- format-4 image run without any has a port that ends at once.
lowerIO : Ports → CheckedP → Sys
lowerIO pt p = lowerIn [] pt p

lowerIn-refs : ∀ xs pt p → refsOf (lowerIn xs pt p) ≡ []
lowerIn-refs xs none    p = refl
lowerIn-refs xs console p = refl
lowerIn-refs xs stdio   p = refl

lowerIn-wf : ∀ xs pt p → WF (lowerIn xs pt p)
lowerIn-wf xs none    p = bnil , uniq-nil
lowerIn-wf xs console p = bnil , uniq-nil
lowerIn-wf xs stdio   p = bnil , uniq-nil

-- Same shape as `lowerP-safe`. The `AllInv` conjunct holds of every
-- `Sys` (`residual-inv-refs`).
lowerIn-safe : ∀ {xs pt p s} → PStep* (lowerIn xs pt p) s → WF s × AllInv (refsOf s)
lowerIn-safe {xs} {pt} {p} {s} tr = psteps tr (lowerIn-wf xs pt p) , residual-inv-refs s

-- `drive` from any port layout ends on a `WF` system. The trace is
-- `drive-sound`; nothing here re-runs it.
in-final-wf : ∀ {n c ms v xs pt p t} {o : Outcome t} {es ms' v'} →
  proj₁ (drive n c ms v (lowerIn xs pt p)) ≡ drv t o es ms' v' →
  WF t
in-final-wf {n} {c} {ms} {v} {xs} {pt} {p} {t} {o} {es} {ms'} {v'} eq =
  proj₁ (lowerIn-safe {xs} {pt} {p}
    (drive-sound {n} {c} {ms} {v} {lowerIn xs pt p} {t} {o} {es} {ms'} {v'} eq))

-- The B4a statements, as the no-input case.
lowerIO-refs : ∀ pt p → refsOf (lowerIO pt p) ≡ []
lowerIO-refs pt p = lowerIn-refs [] pt p

lowerIO-wf : ∀ pt p → WF (lowerIO pt p)
lowerIO-wf pt p = lowerIn-wf [] pt p

lowerIO-safe : ∀ {pt p s} → PStep* (lowerIO pt p) s → WF s × AllInv (refsOf s)
lowerIO-safe {pt} {p} tr = lowerIn-safe {[]} {pt} {p} tr

io-final-wf : ∀ {n c ms v pt p t} {o : Outcome t} {es ms' v'} →
  proj₁ (drive n c ms v (lowerIO pt p)) ≡ drv t o es ms' v' →
  WF t
io-final-wf {n} {c} {ms} {v} {pt} {p} {t} {o} {es} {ms'} {v'} eq =
  in-final-wf {n} {c} {ms} {v} {[]} {pt} {p} {t} {o} {es} {ms'} {v'} eq

------------------------------------------------------------------------
-- A `pstDone` process with `idle` control is never scheduled.
------------------------------------------------------------------------

module _ (h : List Obj) (ps : List Proc) (i j : ℕ) (rs : List Ref) (ib : List Msg)
         (lk : lookup ps i ≡ just (proc j pstDone rs ib idle)) where

  quietK : ∀ k → emitK (sys h ps) i k ≡ nothing
  quietK k-deliver rewrite lk = refl
  quietK k-seq     rewrite lk = refl
  quietK k-bind    rewrite lk = refl
  quietK k-spawn   rewrite lk = refl
  quietK k-emit    rewrite lk = refl
  quietK k-await   rewrite lk = refl
  quietK k-arm     rewrite lk = refl
  quietK k-flush   rewrite lk = refl
  quietK k-npeek   rewrite lk = refl
  quietK k-ndemon  rewrite lk = refl
  quietK k-recv    rewrite lk = refl
  quietK k-done    rewrite lk = refl
  quietK k-eval    rewrite lk = refl

  quiet-first : ∀ ks → firstHit (sys h ps) i ks ≡ nothing
  quiet-first [] = refl
  quiet-first (k ∷ ks) with res (sys h ps) i k
  quiet-first (k ∷ ks) | yes r eq with trans (sym (quietK k)) eq
  quiet-first (k ∷ ks) | yes r eq | ()
  quiet-first (k ∷ ks) | no _ = quiet-first ks

  idle-quiet : enabled (sys h ps) i ≡ nothing
  idle-quiet rewrite quiet-first spine = refl

------------------------------------------------------------------------
-- What the host prints. One value per console message, in inbox
-- order. A `suc↑` chain is followed on fuel one past the heap length,
-- the same reading as `RunImage.readRef`.
------------------------------------------------------------------------

data OutV : Set where
  out-nat : ℕ → OutV
  out-clo : OutV
  out-con : ℕ → OutV
  out-bad : OutV

bumpO : OutV → OutV
bumpO (out-nat n) = out-nat (suc n)
bumpO _           = out-bad

readOut : List Obj → ℕ → ℕ → OutV
readOut _ zero    _ = out-bad
readOut h (suc f) i with payloadAt h i
... | just (nat n)   = out-nat n
... | just (suc↑ r)  = bumpO (readOut h f (obj r))
... | just (clo _ _) = out-clo
... | just (con t _) = out-con t
... | nothing        = out-bad

outMsgs : List Obj → List Msg → List OutV
outMsgs h []           = []
outMsgs h (msg r ∷ ms) = readOut h (suc (length h)) (obj r) ∷ outMsgs h ms

consoleOut : Sys → List OutV
consoleOut s with lookup (procs s) console-pid
... | nothing = []
... | just q  = outMsgs (heap s) (inbox q)

portOut : Ports → Sys → List OutV
portOut none    _ = []
portOut console s = consoleOut s
portOut stdio   s = consoleOut s

-- The console layout puts `consoleProc` at `console-pid`.
console-at : ∀ p → lookup (procs (lowerIO console p)) console-pid ≡ just consoleProc
console-at p = refl

-- So the console is quiet in the initial system.
console-quiet-0 : ∀ p → enabled (lowerIO console p) console-pid ≡ nothing
console-quiet-0 p =
  idle-quiet (heap (lowerIO console p)) (procs (lowerIO console p))
    console-pid console-pid [] [] (console-at p)

-- B4b. The `stdio` layout has the console at pid 1 too, quiet at boot.
stdio-console-at : ∀ xs p →
  lookup (procs (lowerIn xs stdio p)) console-pid ≡ just consoleProc
stdio-console-at xs p = refl

stdio-quiet-0 : ∀ xs p → enabled (lowerIn xs stdio p) console-pid ≡ nothing
stdio-quiet-0 xs p =
  idle-quiet (heap (lowerIn xs stdio p)) (procs (lowerIn xs stdio p))
    console-pid console-pid [] [] (stdio-console-at xs p)

-- And the input port at pid 2, running `inputP xs`.
input-at : ∀ xs p → lookup (procs (lowerIn xs stdio p)) input-pid ≡ just (inputProc xs)
input-at xs p = refl
