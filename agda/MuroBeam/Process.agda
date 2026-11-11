------------------------------------------------------------------------
-- Processes, mailboxes, and the run-mode steps that touch them.
-- Scheduling is one step of some process. There is no fairness.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Process where

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Mode; run; spec; evid)
open import Muro.Grade using (Grade; g0; g1; _≤ᵍ_)

open import MuroBeam.Grade using
  ( selfKept; isZeroGrade; isG1; kind; Kind; Kmove; Kcopy )
open import MuroBeam.Heap using
  ( Obj; cell; Status; live; Ref; ref; residual; checked; obj
  ; spendRef; spendRef-zero; residual-inv; ref-inv
  ; count; hasG1; Grade1Unique )
open import MuroBeam.Lib using (lookup; update; removeAt)

------------------------------------------------------------------------
-- Process and mailbox
------------------------------------------------------------------------

data PState : Set where
  ready waiting done : PState

data Msg : Set where
  msg : Ref → Msg

msgRef : Msg → Ref
msgRef (msg r) = r

record Proc : Set where
  constructor proc
  field
    pid   : ℕ
    state : PState
    roots : List Ref
    inbox : List Msg

open Proc public

record Sys : Set where
  constructor sys
  field
    heap  : List Obj
    procs : List Proc

open Sys public

mapRef : List Msg → List Ref
mapRef []           = []
mapRef (msg r ∷ ms) = r ∷ mapRef ms

refsP : Proc → List Ref
refsP p = roots p ++ mapRef (inbox p)

refsPs : List Proc → List Ref
refsPs []       = []
refsPs (p ∷ ps) = refsP p ++ refsPs ps

refsOf : Sys → List Ref
refsOf s = refsPs (procs s)

mapSys : List Obj → Maybe (List Proc) → Maybe Sys
mapSys _ nothing    = nothing
mapSys h (just ps)  = just (sys h ps)

------------------------------------------------------------------------
-- Indexing a root
------------------------------------------------------------------------

rootFrom : Maybe Proc → ℕ → Maybe Ref
rootFrom nothing  _ = nothing
rootFrom (just p) j = lookup (roots p) j

rootAt : Sys → ℕ → ℕ → Maybe Ref
rootAt s i j = rootFrom (lookup (procs s) i) j

------------------------------------------------------------------------
-- Dereference in run mode. Grade 0 is not a step.
------------------------------------------------------------------------

putHeadOf : Proc → List Proc → Maybe (List Ref) → Maybe (List Proc)
putHeadOf p ps nothing   = nothing
putHeadOf p ps (just rs) = just (record p { roots = rs } ∷ ps)

putHead : Proc → ℕ → Ref → List Proc → Maybe (List Proc)
putHead p j r' ps = putHeadOf p ps (update j r' (roots p))

putTail : Proc → Maybe (List Proc) → Maybe (List Proc)
putTail _ nothing   = nothing
putTail p (just ps) = just (p ∷ ps)

putRoot : List Proc → ℕ → ℕ → Ref → Maybe (List Proc)
putRoot []       _       _ _ = nothing
putRoot (p ∷ ps) zero    j r' = putHead p j r' ps
putRoot (p ∷ ps) (suc i) j r' = putTail p (putRoot ps i j r')

derefSpent : List Obj → List Proc → ℕ → ℕ → Ref → Maybe Ref → Maybe Sys
derefSpent h ps i j r nothing   = nothing
derefSpent h ps i j r (just r') = mapSys h (putRoot ps i j r')

derefAt : Sys → ℕ → ℕ → Maybe Ref → Maybe Sys
derefAt (sys h ps) i j nothing  = nothing
derefAt (sys h ps) i j (just r) = derefSpent h ps i j r (spendRef r)

deref : Mode → Sys → ℕ → ℕ → Maybe Sys
deref run  s i j = derefAt s i j (rootAt s i j)
deref spec _ _ _ = nothing
deref evid _ _ _ = nothing

grade0-not-dereferenced : ∀ s i j r →
  rootAt s i j ≡ just r →
  residual r ≡ g0 →
  deref run s i j ≡ nothing
grade0-not-dereferenced s i j r eq rz rewrite eq | spendRef-zero r rz = refl

------------------------------------------------------------------------
-- Send. A finite point, including g1, moves. ω and intervals are copied.
-- A zero residual is not sent.
------------------------------------------------------------------------

post : Proc → Ref → Proc
post p r = record p { inbox = inbox p ++ msg r ∷ [] }

dropRoot : Proc → Maybe (Ref × List Ref) → Maybe (Ref × Proc)
dropRoot p nothing          = nothing
dropRoot p (just (r , rs))  = just (r , record p { roots = rs })

takeRoot : Proc → ℕ → Maybe (Ref × Proc)
takeRoot p j = dropRoot p (removeAt j (roots p))

addMsgOn : List Proc → ℕ → Ref → Maybe Proc → Maybe (List Proc)
addMsgOn ps i r nothing  = nothing
addMsgOn ps i r (just p) = update i (post p r) ps

addMsg : List Proc → ℕ → Ref → Maybe (List Proc)
addMsg ps i r = addMsgOn ps i r (lookup ps i)

moveRecv : Ref → ℕ → List Obj → List Proc → Maybe Proc → Maybe Sys
moveRecv _ _ _ _  nothing  = nothing
moveRecv r ri h ps (just p) = mapSys h (update ri (post p r) ps)

moveOther : Ref → ℕ → ℕ → List Obj → List Proc → Maybe (List Proc) → Maybe Sys
moveOther _ _ _ _ _  nothing     = nothing
moveOther r si ri h _ (just ps1) = moveRecv r ri h ps1 (lookup ps1 ri)

moveToOn : Ref → Proc → ℕ → ℕ → List Obj → List Proc → Bool → Maybe Sys
moveToOn r sp' si ri h ps true  = mapSys h (update si (post sp' r) ps)
moveToOn r sp' si ri h ps false = moveOther r si ri h ps (update si sp' ps)

moveTo : Ref → Proc → ℕ → ℕ → List Obj → List Proc → Maybe Sys
moveTo r sp' si ri h ps = moveToOn r sp' si ri h ps (si ≡ᵇ ri)

copyTo : Ref → ℕ → List Obj → List Proc → Maybe Sys
copyTo r ri h ps = mapSys h (addMsg ps ri r)

dispatch : Bool → Maybe Kind → Ref → Proc → ℕ → ℕ → List Obj → List Proc → Maybe Sys
dispatch true  _          _ _ _ _ _ _  = nothing
dispatch false nothing    _ _ _ _ _ _  = nothing
dispatch false (just Kmove) r sp' si ri h ps = moveTo r sp' si ri h ps
dispatch false (just Kcopy) r _   _  ri h ps = copyTo r ri h ps

sendTaken : Maybe (Ref × Proc) → ℕ → ℕ → List Obj → List Proc → Maybe Sys
sendTaken nothing          _ _ _ _ = nothing
sendTaken (just (r , sp')) si ri h ps =
  dispatch (isZeroGrade (residual r)) (kind (checked r)) r sp' si ri h ps

sendFrom : Maybe Proc → ℕ → ℕ → ℕ → List Obj → List Proc → Maybe Sys
sendFrom nothing    _ _ _ _ _  = nothing
sendFrom (just sp) si sj ri h ps = sendTaken (takeRoot sp sj) si ri h ps

send : Sys → ℕ → ℕ → ℕ → Maybe Sys
send (sys h ps) si sj ri = sendFrom (lookup ps si) si sj ri h ps

-- Send moves or copies an existing reference, so every residual/checked
-- pair in the result is still a Ref, and the inequality still holds.
data AllInv : List Ref → Set where
  none : AllInv []
  keep : ∀ {r rs} → residual-inv r → AllInv rs → AllInv (r ∷ rs)

refs-inv : ∀ rs → AllInv rs
refs-inv []       = none
refs-inv (r ∷ rs) = keep (ref-inv r) (refs-inv rs)

send-preserves-residual : ∀ {s si sj ri t} →
  send s si sj ri ≡ just t →
  AllInv (refsOf t)
send-preserves-residual _ = refs-inv _

------------------------------------------------------------------------
-- Receive moves a message into the receiver's roots.
------------------------------------------------------------------------

recvInbox : List Obj → List Proc → ℕ → Proc → List Msg → Maybe Sys
recvInbox _ _ _ _ []             = nothing
recvInbox h ps i p (msg r ∷ ms)  =
  mapSys h (update i (record p { roots = roots p ++ r ∷ [] ; inbox = ms }) ps)

recvAt : List Obj → List Proc → ℕ → Maybe Proc → Maybe Sys
recvAt _ _ _ nothing  = nothing
recvAt h ps i (just p) = recvInbox h ps i p (inbox p)

recv : Sys → ℕ → Maybe Sys
recv (sys h ps) i = recvAt h ps i (lookup ps i)

------------------------------------------------------------------------
-- Allocate a fresh cell. The new root's residual equals its checked grade.
------------------------------------------------------------------------

addRootOn : List Proc → ℕ → Ref → Maybe Proc → Maybe (List Proc)
addRootOn ps i r nothing  = nothing
addRootOn ps i r (just p) = update i (record p { roots = roots p ++ r ∷ [] }) ps

addRoot : List Proc → ℕ → Ref → Maybe (List Proc)
addRoot ps i r = addRootOn ps i r (lookup ps i)

alloc : Sys → ℕ → Grade → ℕ → Maybe Sys
alloc (sys h ps) i g v =
  mapSys (h ++ cell v live ∷ [])
         (addRoot ps i (ref (length h) g g (selfKept g)))

------------------------------------------------------------------------
-- Reuse a spent grade-1 slot in place. The dynamic check demands that
-- the object currently has exactly one reference.
------------------------------------------------------------------------

poke : List Obj → ℕ → ℕ → List Obj
poke []       _       _ = []
poke (_ ∷ hs) zero    v = cell v live ∷ hs
poke (c ∷ hs) (suc k) v = c ∷ poke hs k v

length-poke : ∀ h k v → length (poke h k v) ≡ length h
length-poke []       _       _ = refl
length-poke (_ ∷ hs) zero    _ = refl
length-poke (_ ∷ hs) (suc k) v rewrite length-poke hs k v = refl

reuseOk : Sys → ℕ → ℕ → Grade → ℕ → Ref → Bool → Bool → Bool → Maybe Sys
reuseOk (sys h ps) i j g v r true true true =
  mapSys (poke h (obj r) v) (putRoot ps i j (ref (obj r) g g (selfKept g)))
reuseOk _ _ _ _ _ _ _ _ _ = nothing

reuseFrom : Sys → ℕ → ℕ → Grade → ℕ → Maybe Ref → Maybe Sys
reuseFrom s i j g v nothing  = nothing
reuseFrom s i j g v (just r) =
  reuseOk s i j g v r (isG1 (checked r)) (isZeroGrade (residual r))
          (count (obj r) (refsOf s) ≡ᵇ 1)

reuse : Sys → ℕ → ℕ → Grade → ℕ → Maybe Sys
reuse s i j g v = reuseFrom s i j g v (rootAt s i j)

------------------------------------------------------------------------
-- Every reference satisfies the residual inequality, whether or not a
-- step produced it. Steps only rearrange Refs or build them with Kept.
------------------------------------------------------------------------

residual-inv-refs : ∀ s → AllInv (refsOf s)
residual-inv-refs s = refs-inv (refsOf s)
