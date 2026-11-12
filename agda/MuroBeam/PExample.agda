------------------------------------------------------------------------
-- v1b traces.
--
--   * spawn, send a g1 reference, deliver it, recv it
--   * proper ignore: demonitor, then flush, including the schedule
--     where the reply is delivered in between those two steps
--   * naive ignore: demonitor without a flush leaves the reply
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.PExample where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Grade using (Grade; g0; g1)

open import MuroBeam.Grade using (selfKept)
open import MuroBeam.Heap using (Obj; cell; live; nat; Ref; ref; obj; count)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.PSyntax using
  ( Thin; t[]; keep; PTm; done; send; recv; spawn; ignore; nignore; await
  ; ignoreT; flushT; ncheckT; ndemonT; awaitT
  ; Flight; flight; Code; go; codeEnv )
open import MuroBeam.Process using
  ( Proc; proc; ready; waiting; Sys; sys; heap; procs; ctl; Ctl; pr
  ; inbox; state; Msg; msg; refsOf )
  renaming (done to pstDone)
open import MuroBeam.Stray using (ReplyDone; replied; no-stray-reply)
open import MuroBeam.PRun using
  ( spawn1; emit1; deliver1; recv1; arm1; flush1; await1; npeek1; ndemon1
  ; mailHas; deadAt; PStep; PStep*; p-spawn; p-emit; p-deliver; p-recv
  ; p-arm; p-flush; p-await; p-npeek; p-ndemon; pmore; pdone )

take : ∀ {A : Set} → A → Maybe A → A
take _ (just x) = x
take d nothing  = d

ρ : Ref
ρ = ref zero g1 g1 (selfKept g1)

ph : Ref
ph = ref (suc zero) g0 g0 (selfKept g0)

ph2 : Ref
ph2 = ref (suc (suc zero)) g0 g0 (selfKept g0)

h0 : List Obj
h0 = cell (nat zero) live ∷ []

h1 : List Obj
h1 = h0 ++ cell (nat zero) live ∷ []

h2 : List Obj
h2 = h1 ++ cell (nat zero) live ∷ []

nth : List Proc → ℕ → Proc
nth ps i with lookup ps i
... | just p  = p
... | nothing = proc zero ready [] [] (pr (go {0} (done {0}) [] [] [] []))

------------------------------------------------------------------------
-- spawn → emit g1 → deliver → recv
------------------------------------------------------------------------

trip : PTm 1
trip = spawn (keep t[]) (send zero fzero (done {1})) (recv g1 g0 (done {2}))

s0 : Sys
s0 = sys h0 (proc zero ready [] [] (pr (go trip (ρ ∷ []) [] [] [])) ∷ [])

s1 s2 s3 s4 : Sys
s1 = take s0 (spawn1 s0 zero)
s2 = take s0 (emit1 s1 (suc zero))
s3 = take s0 (deliver1 s2 (suc zero))
s4 = take s0 (recv1 s3 zero)

s1-expect : Sys
s1-expect =
  sys h1
    ( proc zero ready [] [] (pr (go (recv g1 g0 (done {2})) (ph ∷ []) [] [] []))
    ∷ proc (suc zero) ready [] [] (pr (go (send zero fzero (done {1})) (ρ ∷ []) [] [] []))
    ∷ [])

s2-expect : Sys
s2-expect =
  sys h2
    ( proc zero ready [] [] (pr (go (recv g1 g0 (done {2})) (ph ∷ []) [] [] []))
    ∷ proc (suc zero) ready [] []
        (pr (go {1} (done {1}) (ph2 ∷ []) (flight zero ρ ∷ []) [] []))
    ∷ [])

s3-expect : Sys
s3-expect =
  sys h2
    ( proc zero ready [] (msg ρ ∷ []) (pr (go (recv g1 g0 (done {2})) (ph ∷ []) [] [] []))
    ∷ proc (suc zero) ready [] [] (pr (go {1} (done {1}) (ph2 ∷ []) [] [] []))
    ∷ [])

s4-expect : Sys
s4-expect =
  sys h2
    ( proc zero ready [] [] (pr (go {2} (done {2}) (ρ ∷ ph ∷ []) [] [] []))
    ∷ proc (suc zero) ready [] [] (pr (go {1} (done {1}) (ph2 ∷ []) [] [] []))
    ∷ [])

trip-spawn : s1 ≡ s1-expect
trip-spawn = refl

trip-emit : s2 ≡ s2-expect
trip-emit = refl

trip-deliver : s3 ≡ s3-expect
trip-deliver = refl

trip-recv : s4 ≡ s4-expect
trip-recv = refl

trip-trace : PStep* s0 s4
trip-trace =
  pmore (p-spawn {s0} {zero} {s1} refl)
  (pmore (p-emit {s1} {suc zero} {s2} refl)
  (pmore (p-deliver {s2} {suc zero} {s3} refl)
  (pmore (p-recv {s3} {zero} {s4} refl)
  pdone)))

------------------------------------------------------------------------
-- Proper ignore. The reply is delivered after demonitor and before flush.
------------------------------------------------------------------------

ig : PTm 1
ig = spawn (keep t[]) (send zero fzero (done {1})) (ignore fzero (done {1}))

i0 : Sys
i0 = sys h0 (proc zero ready [] [] (pr (go ig (ρ ∷ []) [] [] [])) ∷ [])

i1 i2 i3 i4 i5 : Sys
i1 = take i0 (spawn1 i0 zero)
i2 = take i0 (emit1 i1 (suc zero))
i3 = take i0 (arm1 i1 zero)   -- demonitor before the reply is delivered
i4 = take i0 (deliver1 i2 (suc zero))
i5 = take i0 (flush1 i4 zero)

-- arm does not need the emit. Demonitor with the flight still in the child
-- is the same state as arming the spawned parent and then emitting.
-- The schedule below is: spawn, emit (flight live), demonitor, deliver, flush.

j1 j2 j3 j4 j5 : Sys
j1 = take i0 (spawn1 i0 zero)
j2 = take i0 (emit1 j1 (suc zero))
j3 = take i0 (arm1 j2 zero)
j4 = take i0 (deliver1 j3 (suc zero))
j5 = take i0 (flush1 j4 zero)

j1-expect : Sys
j1-expect =
  sys h1
    ( proc zero ready [] [] (pr (go (ignoreT zero (done {1})) (ph ∷ []) [] [] []))
    ∷ proc (suc zero) ready [] [] (pr (go (send zero fzero (done {1})) (ρ ∷ []) [] [] []))
    ∷ [])

ignore-spawn : j1 ≡ j1-expect
ignore-spawn = refl

-- After demonitor the flight is still there, and dead is not set.
j3-demo : Sys
j3-demo =
  sys h2
    ( proc zero ready [] [] (pr (go (flushT zero (done {1})) (ph ∷ []) [] [] (zero ∷ [])))
    ∷ proc (suc zero) ready [] []
        (pr (go {1} (done {1}) (ph2 ∷ []) (flight zero ρ ∷ []) [] []))
    ∷ [])

ignore-arm : j3 ≡ j3-demo
ignore-arm = refl

ignore-arm-not-dead : deadAt (procs j3) zero zero ≡ false
ignore-arm-not-dead = refl

-- Deliver between demonitor and flush still enqueues.
j4-inbox : mailHas (procs j4) zero zero ≡ true
j4-inbox = refl

j5-clear : mailHas (procs j5) zero zero ≡ false
j5-clear = refl

j5-dead : deadAt (procs j5) zero zero ≡ true
j5-dead = refl

j5-gone : count zero (refsOf j5) ≡ 0
j5-gone = refl

j5-fit : zero < length (heap j5)
j5-fit = s≤s z≤n

-- Flush completed the reply. Every later schedule stays clear of tag 0.
j5-done : ReplyDone j5 zero zero
j5-done = replied j5-gone j5-fit j5-dead

j5-stays : ∀ {t} → PStep* j5 t → mailHas (procs t) zero zero ≡ false
j5-stays tr = no-stray-reply tr j5-done

ignore-trace : PStep* i0 j5
ignore-trace =
  pmore (p-spawn {i0} {zero} {j1} refl)
  (pmore (p-emit {j1} {suc zero} {j2} refl)
  (pmore (p-arm {j2} {zero} {j3} refl)
  (pmore (p-deliver {j3} {suc zero} {j4} refl)
  (pmore (p-flush {j4} {zero} {j5} refl)
  pdone))))

-- Flush first. The in-flight reply is consumed before deliver runs,
-- so deliver has nothing to enqueue.
k4 k5 : Sys
k4 = take i0 (flush1 j3 zero)
k5 = take i0 (deliver1 k4 (suc zero))

ignore-flush-first : mailHas (procs k4) zero zero ≡ false
ignore-flush-first = refl

ignore-late-deliver : deliver1 k4 (suc zero) ≡ nothing
ignore-late-deliver = refl

k4-gone : count zero (refsOf k4) ≡ 0
k4-gone = refl

k4-fit : zero < length (heap k4)
k4-fit = s≤s z≤n

k4-dead : deadAt (procs k4) zero zero ≡ true
k4-dead = refl

k4-done : ReplyDone k4 zero zero
k4-done = replied k4-gone k4-fit k4-dead

k4-stays : ∀ {t} → PStep* k4 t → mailHas (procs t) zero zero ≡ false
k4-stays tr = no-stray-reply tr k4-done

------------------------------------------------------------------------
-- await consumes the delivered reply. An empty mailbox waits,
-- and deliver wakes the process.
------------------------------------------------------------------------

aw : PTm 1
aw = spawn (keep t[]) (send zero fzero (done {1})) (await fzero (done {1}))

a0 : Sys
a0 = sys h0 (proc zero ready [] [] (pr (go aw (ρ ∷ []) [] [] [])) ∷ [])

a1 a2 a3 a4 : Sys
a1 = take a0 (spawn1 a0 zero)
a2 = take a0 (emit1 a1 (suc zero))
a3 = take a0 (deliver1 a2 (suc zero))
a4 = take a0 (await1 a3 zero)

await-spawn-tag : ctl (nth (procs a1) zero) ≡ pr (go (awaitT zero (done {1})) (ph ∷ []) [] [] [])
await-spawn-tag = refl

await-before : mailHas (procs a3) zero zero ≡ true
await-before = refl

await-after : mailHas (procs a4) zero zero ≡ false
await-after = refl

await-dead : deadAt (procs a4) zero zero ≡ true
await-dead = refl

a4-gone : count zero (refsOf a4) ≡ 0
a4-gone = refl

a4-fit : zero < length (heap a4)
a4-fit = s≤s z≤n

a4-done : ReplyDone a4 zero zero
a4-done = replied a4-gone a4-fit await-dead

a4-stays : ∀ {t} → PStep* a4 t → mailHas (procs t) zero zero ≡ false
a4-stays tr = no-stray-reply tr a4-done

await-trace : PStep* a0 a4
await-trace =
  pmore (p-spawn {a0} {zero} {a1} refl)
  (pmore (p-emit {a1} {suc zero} {a2} refl)
  (pmore (p-deliver {a2} {suc zero} {a3} refl)
  (pmore (p-await {a3} {zero} {a4} refl)
  pdone)))

w2 w3 w4 : Sys
w2 = take a0 (await1 a2 zero)
w3 = take a0 (deliver1 w2 (suc zero))
w4 = take a0 (await1 w3 zero)

await-waits : state (nth (procs w2) zero) ≡ waiting
await-waits = refl

await-wakes : state (nth (procs w3) zero) ≡ ready
await-wakes = refl

await-then : mailHas (procs w4) zero zero ≡ false
await-then = refl

------------------------------------------------------------------------
-- Naive ignore. Demonitor does not flush. The flight survives it,
-- and the next deliver leaves the reply in the mailbox.
------------------------------------------------------------------------

nv : PTm 1
nv = spawn (keep t[]) (send zero fzero (done {1})) (nignore fzero (done {1}))

n0 : Sys
n0 = sys h0 (proc zero ready [] [] (pr (go nv (ρ ∷ []) [] [] [])) ∷ [])

n1 n2 n3 n4 n5 : Sys
n1 = take n0 (spawn1 n0 zero)
n2 = take n0 (emit1 n1 (suc zero))
n3 = take n0 (npeek1 n2 zero)
n4 = take n0 (ndemon1 n3 zero)
n5 = take n0 (deliver1 n4 (suc zero))

naive-tag : ctl (nth (procs n1) zero) ≡ pr (go (ncheckT zero (done {1})) (ph ∷ []) [] [] [])
naive-tag = refl

-- The empty `after 0` does not touch the child's flight.
naive-peek : ctl (nth (procs n3) zero) ≡ pr (go (ndemonT zero (done {1})) (ph ∷ []) [] [] [])
naive-peek = refl

naive-demon : ctl (nth (procs n4) zero) ≡ pr (go {1} (done {1}) (ph ∷ []) [] [] (zero ∷ []))
naive-demon = refl

naive-not-dead : deadAt (procs n4) zero zero ≡ false
naive-not-dead = refl

naive-leak : mailHas (procs n5) zero zero ≡ true
naive-leak = refl

naive-inbox : inbox (nth (procs n5) zero) ≡ msg ρ ∷ []
naive-inbox = refl

naive-trace : PStep* n0 n5
naive-trace =
  pmore (p-spawn {n0} {zero} {n1} refl)
  (pmore (p-emit {n1} {suc zero} {n2} refl)
  (pmore (p-npeek {n2} {zero} {n3} refl)
  (pmore (p-ndemon {n3} {zero} {n4} refl)
  (pmore (p-deliver {n4} {suc zero} {n5} refl)
  pdone))))
