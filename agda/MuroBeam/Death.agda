------------------------------------------------------------------------
-- Peer death for one monitor.
--
-- Two processes. One of them monitors the other. This is not a field
-- of Proc, and it is not a PStep: codeDead, deadInCtl, and deadAt stay
-- protocol tags. Stray, Unique, PWf, and Adequacy are unchanged.
--
-- An exit records the reason and does not emit. A failure exit sets
-- `dead`, which is the mark that consumes a later send. The failure
-- arm runs at the observer's receive, and only once that inbox is
-- empty: queued mail is `tr-recv` first, then one `tr-down`. A second
-- observation is nothing. `done` or abandon makes a later observation
-- a halt (empty events, arm not set). `:normal` is that halt when
-- either phase is settled, and a failure-arm down when neither is.
-- The arm is this transition. It does not run a protocol skeleton.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Death where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Grade using (g1)

open import MuroBeam.Event using
  ( Why; killed; crash; normal; abandon
  ; Event; tr-recv; tr-down )
open import MuroBeam.Grade using (selfKept)
open import MuroBeam.Heap using (Obj; cell; live; Val; nat; Ref; ref)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.Process using
  ( Sys; sys; heap; procs; Proc; proc; PState; ready; done
  ; roots; inbox; state; Msg; msg; idle )

------------------------------------------------------------------------
-- One meeting. Flags are the death facts. The heap and the process
-- list stay a Sys so a conformance line can still fingerprint them.
------------------------------------------------------------------------

data Phase : Set where
  ph-run ph-settled : Phase

record Meet : Set where
  constructor mt
  field
    base      : Sys
    watching  : Bool
    observer  : ℕ
    peer      : ℕ
    phaseS    : Phase
    phaseP    : Phase
    halted    : Bool
    exited    : Bool
    why       : Why
    dead      : Bool
    armed     : Bool
    noted     : Bool
    expect    : Why

open Meet public

data DRun : Set where
  dran : Meet → List Event → DRun

data DOp : Set where
  d-mon     : ℕ → ℕ → DOp
  d-exit    : ℕ → Why → DOp
  d-recv    : ℕ → DOp
  d-send    : ℕ → ℕ → DOp
  d-done    : ℕ → DOp
  d-abandon : ℕ → DOp
  d-settle  : ℕ → DOp

whyEq : Why → Why → Bool
whyEq killed  killed  = true
whyEq killed  crash   = false
whyEq killed  normal  = false
whyEq killed  abandon = false
whyEq crash   killed  = false
whyEq crash   crash   = true
whyEq crash   normal  = false
whyEq crash   abandon = false
whyEq normal  killed  = false
whyEq normal  crash   = false
whyEq normal  normal  = true
whyEq normal  abandon = false
whyEq abandon killed  = false
whyEq abandon crash   = false
whyEq abandon normal  = false
whyEq abandon abandon = true

phaseOn : Phase → Bool
phaseOn ph-run     = false
phaseOn ph-settled = true

-- Abandon is always a halt. An exit after `done` or abandon is a halt
-- because `halted` is set. `:normal` is a halt once either party has
-- settled. `killed` and `crash` are halts only when `halted` is already
-- set. Otherwise they are the failure arm.
haltWhy : Why → Phase → Phase → Bool → Bool
haltWhy abandon _ _ _ = true
haltWhy normal  s p h = h ∨ phaseOn s ∨ phaseOn p
haltWhy killed  _ _ h = h
haltWhy crash   _ _ h = h

present : List Proc → ℕ → Bool
present []       _       = false
present (_ ∷ _)  zero    = true
present (_ ∷ ps) (suc i) = present ps i

updProc : List Proc → ℕ → Proc → Maybe (List Proc)
updProc []       _       _ = nothing
updProc (_ ∷ ps) zero    q = just (q ∷ ps)
updProc (p ∷ ps) (suc i) q with updProc ps i q
... | nothing = nothing
... | just ps' = just (p ∷ ps')

putProcs : Meet → List Proc → Meet
putProcs m ps = record m { base = sys (heap (base m)) ps }

takeMail : Proc → Maybe (Ref × Proc)
takeMail p with inbox p
... | []          = nothing
... | msg r ∷ ms  =
  just (r , record p { inbox = ms ; roots = roots p ++ (r ∷ []) })

------------------------------------------------------------------------
-- Steps. Each one is structural on its list or on a finite match.
-- None of them calls itself.
------------------------------------------------------------------------

stepMon : Meet → ℕ → ℕ → Maybe Meet
stepMon m o p with watching m
... | true  = nothing
... | false with (o ≡ᵇ p) ∨ not (present (procs (base m)) o) ∨ not (present (procs (base m)) p)
... | true  = nothing
... | false = just (record m { watching = true ; observer = o ; peer = p })

stepExit : Meet → ℕ → Why → Maybe Meet
stepExit m i w with watching m
... | false = nothing
... | true with i ≡ᵇ peer m
... | false = nothing
... | true with exited m
... | true  = nothing
... | false with halted m
... | true  = just (record m { exited = true ; why = w })
... | false with haltWhy w (phaseS m) (phaseP m) false
... | true  = just (record m { exited = true ; why = w ; halted = true })
... | false = just (record m { exited = true ; why = w ; dead = true })

stepSettle : Meet → ℕ → Maybe Meet
stepSettle m i with i ≡ᵇ observer m
... | true  = just (record m { phaseS = ph-settled })
... | false with i ≡ᵇ peer m
... | true  = just (record m { phaseP = ph-settled })
... | false = nothing

stepDone : Meet → ℕ → Maybe Meet
stepDone m i with lookup (procs (base m)) i
... | nothing = nothing
... | just p with updProc (procs (base m)) i (record p { state = done })
... | nothing = nothing
... | just ps with watching m ∧ (i ≡ᵇ peer m)
... | true  = just (record (putProcs m ps) { halted = true })
... | false = just (putProcs m ps)

stepAbandon : Meet → ℕ → Maybe Meet
stepAbandon m i with watching m
... | false = nothing
... | true with i ≡ᵇ peer m
... | false = nothing
... | true with exited m
... | true  = nothing
... | false = just (record m { halted = true ; exited = true ; why = abandon ; dead = false })

-- Empty events. The put is not an error, and it is not a tr-send.
-- A peer that is not yet failure-dead is refused here. enqueue stays
-- on the existing send.
stepSend : Meet → ℕ → ℕ → Maybe DRun
stepSend m src dst with watching m
... | false = nothing
... | true with (src ≡ᵇ observer m) ∧ (dst ≡ᵇ peer m)
... | false = nothing
... | true with dead m
... | false = nothing
... | true  = just (dran m [])

-- Halt, or the one arm. `noted` refuses the second observation.
-- A receive with no exit and no halt parks: just, and no event.
observe : Meet → Maybe DRun
observe m with noted m
... | true  = nothing
... | false with halted m
... | true  = just (dran (record m { noted = true }) [])
... | false with exited m
... | false = just (dran m [])
... | true with haltWhy (why m) (phaseS m) (phaseP m) false
... | true  = just (dran (record m { noted = true ; halted = true }) [])
... | false with dead m ∧ whyEq (why m) (expect m)
... | true  =
  just (dran (record m { noted = true ; armed = true })
             (tr-down (observer m) (peer m) (why m) ∷ []))
... | false = nothing

-- Already-noted observation is nothing, for any other fields.
observe-noted : ∀ m → noted m ≡ true → observe m ≡ nothing
observe-noted m eq with noted m | eq
... | true  | refl = refl
... | false | ()

stepRecv : Meet → ℕ → Maybe DRun
stepRecv m i with watching m
... | false = nothing
... | true with i ≡ᵇ observer m
... | false = nothing
... | true with lookup (procs (base m)) i
... | nothing = nothing
... | just p with takeMail p
... | nothing = observe m
... | just (r , p') with updProc (procs (base m)) i p'
... | nothing = nothing
... | just ps  = just (dran (putProcs m ps) (tr-recv i r ∷ []))

mapMeet : Maybe Meet → Maybe DRun
mapMeet nothing  = nothing
mapMeet (just m) = just (dran m [])

stepD : DOp → Meet → Maybe DRun
stepD (d-mon o p)   m = mapMeet (stepMon m o p)
stepD (d-exit i w)  m = mapMeet (stepExit m i w)
stepD (d-recv i)    m = stepRecv m i
stepD (d-send s d)  m = stepSend m s d
stepD (d-done i)    m = mapMeet (stepDone m i)
stepD (d-abandon i) m = mapMeet (stepAbandon m i)
stepD (d-settle i)  m = mapMeet (stepSettle m i)

runDs : List DOp → Meet → Maybe DRun
runDs []       m = just (dran m [])
runDs (op ∷ ops) m with stepD op m
... | nothing           = nothing
... | just (dran m1 es) with runDs ops m1
... | nothing            = nothing
... | just (dran m2 es2) = just (dran m2 (es ++ es2))

------------------------------------------------------------------------
-- Projections. A refusal stays nothing, so an empty event list is
-- not the same fact as a refused step.
------------------------------------------------------------------------

evOf : Maybe DRun → Maybe (List Event)
evOf nothing            = nothing
evOf (just (dran _ es)) = just es

flag : (Meet → Bool) → Maybe DRun → Bool
flag _ nothing          = false
flag f (just (dran m _)) = f m

whyOf : Maybe DRun → Maybe Why
whyOf nothing           = nothing
whyOf (just (dran m _)) = just (why m)

stateAt : Maybe DRun → ℕ → Maybe PState
stateAt nothing            _ = nothing
stateAt (just (dran m _)) i with lookup (procs (base m)) i
... | nothing = nothing
... | just p  = just (state p)

------------------------------------------------------------------------
-- Closed meetings. The cell is the object the queued ref names.
-- Expectation defaults to killed. normal and crash override it.
------------------------------------------------------------------------

downρ : Ref
downρ = ref zero g1 g1 (selfKept g1)

downH : List Obj
downH = cell (nat zero) live ∷ []

pEmpty : Proc
pEmpty = proc zero ready [] [] idle

pMail : Proc
pMail = proc zero ready [] (msg downρ ∷ []) idle

pPeer : Proc
pPeer = proc (suc zero) ready [] [] idle

meetEmpty : Meet
meetEmpty =
  mt (sys downH (pEmpty ∷ pPeer ∷ []))
     false zero (suc zero) ph-run ph-run
     false false killed false false false killed

meetMail : Meet
meetMail = record meetEmpty { base = sys downH (pMail ∷ pPeer ∷ []) }

meetNormal : Meet
meetNormal = record meetEmpty { expect = normal }

meetMiss : Meet
meetMiss = record meetEmpty { expect = crash }

downOps : List DOp
downOps =
  d-mon zero (suc zero) ∷
  d-exit (suc zero) killed ∷
  d-recv zero ∷
  d-recv zero ∷ []

againOps : List DOp
againOps = downOps ++ (d-recv zero ∷ [])

doneOps : List DOp
doneOps =
  d-mon zero (suc zero) ∷
  d-done (suc zero) ∷
  d-exit (suc zero) killed ∷
  d-recv zero ∷ []

abandonOps : List DOp
abandonOps =
  d-mon zero (suc zero) ∷
  d-abandon (suc zero) ∷
  d-recv zero ∷ []

sendOps : List DOp
sendOps =
  d-mon zero (suc zero) ∷
  d-exit (suc zero) killed ∷
  d-send zero (suc zero) ∷ []

sendRecvOps : List DOp
sendRecvOps = sendOps ++ (d-recv zero ∷ [])

afterOps : List DOp
afterOps = downOps ++ (d-send zero (suc zero) ∷ [])

normalOps : List DOp
normalOps =
  d-mon zero (suc zero) ∷
  d-exit (suc zero) normal ∷
  d-recv zero ∷ []

settledOps : List DOp
settledOps =
  d-mon zero (suc zero) ∷
  d-settle (suc zero) ∷
  d-exit (suc zero) normal ∷
  d-recv zero ∷ []

settledSelfOps : List DOp
settledSelfOps =
  d-mon zero (suc zero) ∷
  d-settle zero ∷
  d-exit (suc zero) normal ∷
  d-recv zero ∷ []

missOps : List DOp
missOps =
  d-mon zero (suc zero) ∷
  d-exit (suc zero) killed ∷
  d-recv zero ∷ []

twiceOps : List DOp
twiceOps =
  d-mon zero (suc zero) ∷
  d-exit (suc zero) killed ∷
  d-exit (suc zero) crash ∷ []

liveSendOps : List DOp
liveSendOps =
  d-mon zero (suc zero) ∷
  d-send zero (suc zero) ∷ []

monTwice : List DOp
monTwice =
  d-mon zero (suc zero) ∷
  d-mon zero (suc zero) ∷ []

downEv : List Event
downEv = tr-recv zero downρ ∷ tr-down zero (suc zero) killed ∷ []

oneDown : List Event
oneDown = tr-down zero (suc zero) killed ∷ []

oneNormal : List Event
oneNormal = tr-down zero (suc zero) normal ∷ []

------------------------------------------------------------------------
-- The schedules. mix muro.check pins the same equations.
------------------------------------------------------------------------

down-events : evOf (runDs downOps meetMail) ≡ just downEv
down-events = refl

down-armed : flag armed (runDs downOps meetMail) ≡ true
down-armed = refl

down-dead : flag dead (runDs downOps meetMail) ≡ true
down-dead = refl

down-again : runDs againOps meetMail ≡ nothing
down-again = refl

down-done-events : evOf (runDs doneOps meetEmpty) ≡ just []
down-done-events = refl

down-done-armed : flag armed (runDs doneOps meetEmpty) ≡ false
down-done-armed = refl

down-done-halted : flag halted (runDs doneOps meetEmpty) ≡ true
down-done-halted = refl

down-done-dead : flag dead (runDs doneOps meetEmpty) ≡ false
down-done-dead = refl

down-done-state : stateAt (runDs doneOps meetEmpty) (suc zero) ≡ just done
down-done-state = refl

abandon-events : evOf (runDs abandonOps meetEmpty) ≡ just []
abandon-events = refl

abandon-armed : flag armed (runDs abandonOps meetEmpty) ≡ false
abandon-armed = refl

abandon-why : whyOf (runDs abandonOps meetEmpty) ≡ just abandon
abandon-why = refl

abandon-state : stateAt (runDs abandonOps meetEmpty) (suc zero) ≡ just ready
abandon-state = refl

send-dead-events : evOf (runDs sendOps meetEmpty) ≡ just []
send-dead-events = refl

send-dead-armed : flag armed (runDs sendOps meetEmpty) ≡ false
send-dead-armed = refl

send-dead-dead : flag dead (runDs sendOps meetEmpty) ≡ true
send-dead-dead = refl

send-then-down : evOf (runDs sendRecvOps meetEmpty) ≡ just oneDown
send-then-down = refl

send-after-arm : evOf (runDs afterOps meetMail) ≡ just downEv
send-after-arm = refl

normal-mid : evOf (runDs normalOps meetNormal) ≡ just oneNormal
normal-mid = refl

normal-mid-armed : flag armed (runDs normalOps meetNormal) ≡ true
normal-mid-armed = refl

normal-settled : evOf (runDs settledOps meetNormal) ≡ just []
normal-settled = refl

normal-settled-armed : flag armed (runDs settledOps meetNormal) ≡ false
normal-settled-armed = refl

normal-self : evOf (runDs settledSelfOps meetNormal) ≡ just []
normal-self = refl

normal-self-armed : flag armed (runDs settledSelfOps meetNormal) ≡ false
normal-self-armed = refl

unmatched : runDs missOps meetMiss ≡ nothing
unmatched = refl

exit-twice : runDs twiceOps meetEmpty ≡ nothing
exit-twice = refl

send-before-dead : runDs liveSendOps meetEmpty ≡ nothing
send-before-dead = refl

second-monitor : runDs monTwice meetEmpty ≡ nothing
second-monitor = refl

no-monitor : stepExit meetEmpty (suc zero) killed ≡ nothing
no-monitor = refl
