------------------------------------------------------------------------
-- Emitting wrappers. Each one calls the operation it names and
-- reports that step's events. A refusal is nothing, not an empty
-- trace. deliver, a parking recv, and the other quiet steps are
-- just and an empty list.
--
-- The placeholder a spawn or a move snocs is not tr-alloc.
-- deliver emits no event. tr-step is the pid only.
-- tr-collect lists the unmarked indices, increasing.
--
-- emitPops walks the Pop list first, as the book does, so the
-- recursive call is on that tail.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Emit where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (run)
open import Muro.Grade using (Grade)

open import MuroBeam.Event using
  ( Event; tr-alloc; tr-spend; tr-send; tr-recv; tr-spawn; tr-step; tr-collect )
open import MuroBeam.Grade using (isZeroGrade; kind; Kind)
open import MuroBeam.Heap using (Ref; obj; checked; residual; spendRef)
open import MuroBeam.Lib using (lookup)
open import MuroBeam.PSyntax using
  ( PTm; done; send; recv; spawn; seq; await; ignore; nignore
  ; awaitT; ignoreT; flushT; ncheckT; ndemonT
  ; Code; go )
open import MuroBeam.PRun using
  ( spawn1; emit1; emitCtl; deliver1; recv1; recvStep
  ; await1; arm1; flush1; npeek1; ndemon1
  ; seq1; bind1; done1 )
open import MuroBeam.Process using
  ( Sys; sys; heap; procs; Proc; ctl; inbox; state
  ; PState; ready; waiting
  ; Ctl; idle; ev; rv; pr
  ; Msg; msg
  ; alloc; deref; eval1; rootAt )
  renaming (send to sendRoot; done to pstDone)
open import MuroBeam.Collect using (markVec; collect)

------------------------------------------------------------------------
-- One step's system and its events.
------------------------------------------------------------------------

data Run : Set where
  ran : Sys → List Event → Run

data Pop : Set where
  pop-spawn   : ℕ → Pop
  pop-emit    : ℕ → Pop
  pop-deliver : ℕ → Pop
  pop-recv    : ℕ → Pop
  pop-await   : ℕ → Pop
  pop-arm     : ℕ → Pop
  pop-flush   : ℕ → Pop
  pop-npeek   : ℕ → Pop
  pop-ndemon  : ℕ → Pop
  pop-seq     : ℕ → Pop
  pop-bind    : ℕ → Pop
  pop-done    : ℕ → Pop
  pop-eval    : ℕ → Pop

data SendInfo : Set where
  sent : ℕ → Ref → Kind → SendInfo

------------------------------------------------------------------------
-- Unmarked indices, from i upward. A true bit is kept.
------------------------------------------------------------------------

freedIdx : List Bool → ℕ → List ℕ
freedIdx []            _ = []
freedIdx (true  ∷ bs)  i = freedIdx bs (suc i)
freedIdx (false ∷ bs)  i = i ∷ freedIdx bs (suc i)

------------------------------------------------------------------------
-- What a send would move or copy, read off the control before the step.
------------------------------------------------------------------------

peekRef : ℕ → Maybe Ref → Maybe SendInfo
peekRef _   nothing  = nothing
peekRef dst (just r) = peekZero dst r (isZeroGrade (residual r))
  where
  peekKind : ℕ → Ref → Maybe Kind → Maybe SendInfo
  peekKind _   _ nothing   = nothing
  peekKind dst r (just kd) = just (sent dst r kd)

  peekZero : ℕ → Ref → Bool → Maybe SendInfo
  peekZero _ _ true    = nothing
  peekZero dst r false = peekKind dst r (kind (checked r))

peekSlot : ℕ → ℕ → List Ref → Maybe SendInfo
peekSlot dst ix env = peekRef dst (lookup env ix)

peekTm : ∀ {n} → PTm n → List Ref → Maybe SendInfo
peekTm done              _   = nothing
peekTm (send dst x _)    env = peekSlot dst (toℕ x) env
peekTm (recv _ _ _)      _   = nothing
peekTm (spawn _ _ _)     _   = nothing
peekTm (seq _ _ _)       _   = nothing
peekTm (await _ _)       _   = nothing
peekTm (ignore _ _)      _   = nothing
peekTm (nignore _ _)     _   = nothing
peekTm (awaitT _ _)      _   = nothing
peekTm (ignoreT _ _)     _   = nothing
peekTm (flushT _ _)      _   = nothing
peekTm (ncheckT _ _)     _   = nothing
peekTm (ndemonT _ _)     _   = nothing

peekCode : Code → Maybe SendInfo
peekCode (go tm env _ _ _) = peekTm tm env

peekSend : Ctl → Maybe SendInfo
peekSend idle         = nothing
peekSend (ev _ _ _)   = nothing
peekSend (rv _ _ _)   = nothing
peekSend (pr c)       = peekCode c

------------------------------------------------------------------------
-- Wrappers. The state comes from the operation. The event is read
-- from the system the operation was given.
------------------------------------------------------------------------

emitDone : List Event → Maybe Sys → Maybe Run
emitDone _  nothing  = nothing
emitDone es (just t) = just (ran t es)

emitDeref : Sys → ℕ → ℕ → Maybe Run
emitDeref s i j = fromRef (rootAt s i j)
  where
  spent : Ref → Maybe Ref → Maybe Run
  spent _ nothing   = nothing
  spent r (just r2) =
    emitDone (tr-spend (obj r) (residual r) (residual r2) ∷ []) (deref run s i j)

  fromRef : Maybe Ref → Maybe Run
  fromRef nothing  = nothing
  fromRef (just r) = spent r (spendRef r)

emitAlloc : Sys → ℕ → Grade → ℕ → Maybe Run
emitAlloc s i g v =
  emitDone (tr-alloc (length (heap s)) g ∷ []) (alloc s i g v)

emitSendRoot : Sys → ℕ → ℕ → ℕ → Maybe Run
emitSendRoot s si sj ri = fromRoot (rootAt s si sj)
  where
  kinded : Ref → Maybe Kind → Maybe Run
  kinded _ nothing   = nothing
  kinded r (just kd) =
    emitDone (tr-send si ri r kd ∷ []) (sendRoot s si sj ri)

  zeroed : Ref → Bool → Maybe Run
  zeroed _ true  = nothing
  zeroed r false = kinded r (kind (checked r))

  fromRoot : Maybe Ref → Maybe Run
  fromRoot nothing  = nothing
  fromRoot (just r) = zeroed r (isZeroGrade (residual r))

emitEval : Sys → ℕ → Maybe Run
emitEval s i = emitDone (tr-step i ∷ []) (eval1 s i)

emitCollect : Sys → Run
emitCollect s =
  ran (collect s) (tr-collect (freedIdx (markVec s) zero) ∷ [])

-- Child pid is the length of the process list before the append.
emitSpawn : Sys → ℕ → Maybe Run
emitSpawn (sys h ps) i =
  emitDone (tr-spawn i (length ps) ∷ []) (spawn1 (sys h ps) i)

-- Named so a proof can case on the same term `emitEmit` reduces to
-- once the process is found. The events are the send `peekSend`
-- reads off the control before the step.
sendRun : ℕ → Sys → Maybe SendInfo → Maybe Run
sendRun _ _ nothing                = nothing
sendRun i t (just (sent dst r kd)) =
  just (ran t (tr-send i dst r kd ∷ []))

emitFromCtl : ℕ → Ctl → Maybe Sys → Maybe Run
emitFromCtl _ _ nothing  = nothing
emitFromCtl i c (just t) = sendRun i t (peekSend c)

-- The system in a successful send is the system `emitCtl` returned.
-- Case on the control. A `with` on neutral `peekSend` does not invert.
send-keeps : ∀ {i t t' es} (info : Maybe SendInfo) →
  sendRun i t info ≡ just (ran t' es) → t ≡ t'
send-keeps nothing ()
send-keeps (just (sent _ _ _)) refl = refl

from-ctl-sys : ∀ {i t' t es} (c : Ctl) →
  emitFromCtl i c (just t') ≡ just (ran t es) → t' ≡ t
from-ctl-sys idle ()
from-ctl-sys (ev _ _ _) ()
from-ctl-sys (rv _ _ _) ()
from-ctl-sys (pr (go done _ _ _ _)) ()
from-ctl-sys (pr (go (send dst x _) env _ _ _)) eq =
  send-keeps (peekSlot dst (toℕ x) env) eq
from-ctl-sys (pr (go (recv _ _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (spawn _ _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (seq _ _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (await _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (ignore _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (nignore _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (awaitT _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (ignoreT _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (flushT _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (ncheckT _ _) _ _ _ _)) ()
from-ctl-sys (pr (go (ndemonT _ _) _ _ _ _)) ()

emitEmit : Sys → ℕ → Maybe Run
emitEmit (sys h ps) i = fromProc (lookup ps i)
  where
  fromProc : Maybe Proc → Maybe Run
  fromProc nothing  = nothing
  fromProc (just p) = emitFromCtl i (ctl p) (emitCtl h ps i (ctl p))

emitDeliver : Sys → ℕ → Maybe Run
emitDeliver s i = emitDone [] (deliver1 s i)

-- A bound message is tr-recv. Parking ready on an empty inbox is
-- just and an empty list. `recvFromStep` is the term `emitRecv1`
-- reduces to after lookup.
recvFromStep : ℕ → List Msg → Maybe Sys → Maybe Run
recvFromStep _ _            nothing  = nothing
recvFromStep _ []           (just t) = just (ran t [])
recvFromStep i (msg r ∷ _)  (just t) = just (ran t (tr-recv i r ∷ []))

emitRecv1 : Sys → ℕ → Maybe Run
emitRecv1 (sys h ps) i = fromProc (lookup ps i)
  where
  fromProc : Maybe Proc → Maybe Run
  fromProc nothing  = nothing
  fromProc (just p) =
    recvFromStep i (inbox p) (recvStep h ps i p (ctl p) (state p) (inbox p))

-- Quiet process steps. `emitDone` above pairs events with a `Maybe Sys`.
-- These names are the per-pid wrappers. A repeated `done` is nothing
-- here: `done1` itself still succeeds on a process that is already
-- `pstDone`, and the scheduler must not stutter on that.

-- Direct matches, not `with`, so a proof that abstracts `lookup`
-- and `state` sees `doneState` and `done1` reduce.
stateDone : PState → Bool
stateDone pstDone = true
stateDone ready   = false
stateDone waiting = false

procDone : Maybe Proc → Bool
procDone nothing  = false
procDone (just p) = stateDone (state p)

doneState : Sys → ℕ → Bool
doneState (sys _ ps) i = procDone (lookup ps i)

guardDone : Bool → Maybe Sys → Maybe Run
guardDone true  _ = nothing
guardDone false m = emitDone [] m

emitAwait : Sys → ℕ → Maybe Run
emitAwait s i = emitDone [] (await1 s i)

emitArm : Sys → ℕ → Maybe Run
emitArm s i = emitDone [] (arm1 s i)

emitFlush : Sys → ℕ → Maybe Run
emitFlush s i = emitDone [] (flush1 s i)

emitNpeek : Sys → ℕ → Maybe Run
emitNpeek s i = emitDone [] (npeek1 s i)

emitNdemon : Sys → ℕ → Maybe Run
emitNdemon s i = emitDone [] (ndemon1 s i)

emitSeq : Sys → ℕ → Maybe Run
emitSeq s i = emitDone [] (seq1 s i)

emitBind : Sys → ℕ → Maybe Run
emitBind s i = emitDone [] (bind1 s i)

emitDone1 : Sys → ℕ → Maybe Run
emitDone1 s i = guardDone (doneState s i) (done1 s i)

emitPop : Sys → Pop → Maybe Run
emitPop s (pop-spawn i)   = emitSpawn s i
emitPop s (pop-emit i)    = emitEmit s i
emitPop s (pop-deliver i) = emitDeliver s i
emitPop s (pop-recv i)    = emitRecv1 s i
emitPop s (pop-await i)   = emitAwait s i
emitPop s (pop-arm i)     = emitArm s i
emitPop s (pop-flush i)   = emitFlush s i
emitPop s (pop-npeek i)   = emitNpeek s i
emitPop s (pop-ndemon i)  = emitNdemon s i
emitPop s (pop-seq i)     = emitSeq s i
emitPop s (pop-bind i)    = emitBind s i
emitPop s (pop-done i)    = emitDone1 s i
emitPop s (pop-eval i)    = emitEval s i

joinRun : List Event → Maybe Run → Maybe Run
joinRun _  nothing            = nothing
joinRun es (just (ran t es2)) = just (ran t (es ++ es2))

emitPops : List Pop → Sys → Maybe Run
emitPops []       s = just (ran s [])
emitPops (p ∷ ps) s = cont ps (emitPop s p)
  where
  cont : List Pop → Maybe Run → Maybe Run
  cont _  nothing            = nothing
  cont ps (just (ran t es))  = joinRun es (emitPops ps t)
