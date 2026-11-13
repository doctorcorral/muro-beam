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
open import MuroBeam.PRun using (spawn1; emit1; deliver1; recv1)
open import MuroBeam.Process using
  ( Sys; sys; heap; procs; Proc; ctl; inbox
  ; Ctl; idle; ev; rv; pr
  ; Msg; msg
  ; alloc; deref; eval1; rootAt )
  renaming (send to sendRoot)
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
peekTm (seq _ _)         _   = nothing
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

emitEmit : Sys → ℕ → Maybe Run
emitEmit (sys h ps) i = at (lookup ps i)
  where
  peeked : Sys → Maybe SendInfo → Maybe Run
  peeked _ nothing                = nothing
  peeked t (just (sent dst r kd)) =
    just (ran t (tr-send i dst r kd ∷ []))

  after : Ctl → Maybe Sys → Maybe Run
  after _ nothing  = nothing
  after c (just t) = peeked t (peekSend c)

  at : Maybe Proc → Maybe Run
  at nothing  = nothing
  at (just p) = after (ctl p) (emit1 (sys h ps) i)

emitDeliver : Sys → ℕ → Maybe Run
emitDeliver s i = emitDone [] (deliver1 s i)

-- A bound message is tr-recv. Parking ready on an empty inbox is
-- just and an empty list.
emitRecv1 : Sys → ℕ → Maybe Run
emitRecv1 (sys h ps) i = at (lookup ps i)
  where
  after : List Msg → Maybe Sys → Maybe Run
  after _            nothing  = nothing
  after []           (just t) = just (ran t [])
  after (msg r ∷ _)  (just t) = just (ran t (tr-recv i r ∷ []))

  at : Maybe Proc → Maybe Run
  at nothing  = nothing
  at (just p) = after (inbox p) (recv1 (sys h ps) i)

emitPop : Sys → Pop → Maybe Run
emitPop s (pop-spawn i)   = emitSpawn s i
emitPop s (pop-emit i)    = emitEmit s i
emitPop s (pop-deliver i) = emitDeliver s i
emitPop s (pop-recv i)    = emitRecv1 s i

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
