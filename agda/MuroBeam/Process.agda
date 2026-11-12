------------------------------------------------------------------------
-- Processes, mailboxes, and the run-mode steps that touch them.
-- Scheduling is one step of some process. There is no fairness.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Process where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_; _≤_)
open import Data.Product.Base using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (Mode; run; spec; evid)
open import Muro.Grade using (Grade; g0; g1; gω; aff; _≤ᵍ_; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch)

open import MuroBeam.Grade using
  ( selfKept; isZeroGrade; isG1; kind; Kind; Kmove; Kcopy )
open import MuroBeam.Heap using
  ( Obj; cell; Status; live; Val; nat; suc↑; clo; Ref; ref; residual; checked; obj
  ; payload; kids; childrenBelow; edgeRefs; Ordered; Below; b-nat
  ; spendRef; spendRef-zero; residual-inv; ref-inv
  ; count; hasG1; Grade1Unique
  ; repl )
open import MuroBeam.Lib using (lookup; update; removeAt; mapCons; ≤-refl; ≡ᵇ-sound)
open import MuroBeam.PSyntax using (Code; codeRefs; codeEth; flightRefs)

------------------------------------------------------------------------
-- Process and mailbox
------------------------------------------------------------------------

data PState : Set where
  ready waiting done : PState

data Msg : Set where
  msg : Ref → Msg

-- CEK frames. ar/mt carry syntax. fn and bd carry Refs.
data Frame : Set where
  ar : ∀ {n} → GTm n → Frame
  fn : Ref → Frame
  su : Frame
  mt : ∀ {n} → GTm n → GTm n → GTm (suc n) → Frame
  bd : List Ref → Frame
  -- Parked process code. The environment and the flights are both
  -- references. `seq` parks an empty environment, so the CEK
  -- environment stays the only copy while the term runs. `bind`
  -- moves the parked environment back. Counting it means a tag
  -- cannot hide there and reappear outside `refsOf`.
  saved : Code → Frame

frameRefs : Frame → List Ref
frameRefs (ar _)       = []
frameRefs (fn r)       = r ∷ []
frameRefs su           = []
frameRefs (mt _ _ _)   = []
frameRefs (bd env)     = env
frameRefs (saved c)    = codeRefs c

framesRefs : List Frame → List Ref
framesRefs []       = []
framesRefs (k ∷ ks) = frameRefs k ++ framesRefs ks

data Ctl : Set where
  idle : Ctl
  ev   : ∀ {n} → GTm n → List Ref → List Frame → Ctl
  rv   : Ref → List Ref → List Frame → Ctl
  pr   : Code → Ctl

ctlRefs : Ctl → List Ref
ctlRefs idle             = []
ctlRefs (ev _ env k)     = env ++ framesRefs k
ctlRefs (rv r env k)     = r ∷ env ++ framesRefs k
ctlRefs (pr c)           = codeRefs c

msgRef : Msg → Ref
msgRef (msg r) = r

record Proc : Set where
  constructor proc
  field
    pid   : ℕ
    state : PState
    roots : List Ref
    inbox : List Msg
    ctl   : Ctl

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

ctlRefsPs : List Proc → List Ref
ctlRefsPs []       = []
ctlRefsPs (p ∷ ps) = ctlRefs (ctl p) ++ ctlRefsPs ps

-- Edges and control, grouped so a heap of nats and idle control computes
-- back to the v0 root/message list: both prefixes are [].
preOf : List Obj → List Proc → List Ref
preOf h ps = edgeRefs h ++ ctlRefsPs ps

refsOf : Sys → List Ref
refsOf s = preOf (heap s) (procs s) ++ refsPs (procs s)

liveRefs : Sys → List Ref
liveRefs s = ctlRefsPs (procs s) ++ refsPs (procs s)

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

-- Root and mailbox updates do not touch control.
ctlEq-update : ∀ i ps q ps' →
  update i q ps ≡ just ps' →
  (∀ p → lookup ps i ≡ just p → ctl q ≡ ctl p) →
  ctlRefsPs ps' ≡ ctlRefsPs ps
ctlEq-update _ [] _ _ () _
ctlEq-update zero (p ∷ ps) q .(q ∷ ps) refl hyp rewrite hyp p refl = refl
ctlEq-update (suc i) (p ∷ ps) q ps' eq hyp = tail (update i q ps) eq refl
  where
  tail : (m : Maybe (List Proc)) → mapCons p m ≡ just ps' → update i q ps ≡ m →
         ctlRefsPs ps' ≡ ctlRefsPs (p ∷ ps)
  tail nothing () _
  tail (just qs) refl equ
    rewrite ctlEq-update i ps q qs equ (λ p' lk → hyp p' lk) = refl

ctlEq-putRoot : ∀ ps i j r' ps' →
  putRoot ps i j r' ≡ just ps' →
  ctlRefsPs ps' ≡ ctlRefsPs ps
ctlEq-putRoot [] _ _ _ _ ()
ctlEq-putRoot (p ∷ ps) zero j r' ps' eq = head (update j r' (roots p)) eq refl
  where
  head : (m : Maybe (List Ref)) → putHeadOf p ps m ≡ just ps' →
         update j r' (roots p) ≡ m →
         ctlRefsPs ps' ≡ ctlRefsPs (p ∷ ps)
  head nothing () _
  head (just _) refl _ = refl
ctlEq-putRoot (p ∷ ps) (suc i) j r' ps' eq = tail (putRoot ps i j r') eq refl
  where
  tail : (m : Maybe (List Proc)) → putTail p m ≡ just ps' →
         putRoot ps i j r' ≡ m →
         ctlRefsPs ps' ≡ ctlRefsPs (p ∷ ps)
  tail nothing () _
  tail (just qs) refl equ rewrite ctlEq-putRoot ps i j r' qs equ = refl

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
  mapSys (h ++ cell (nat v) live ∷ [])
         (addRoot ps i (ref (length h) g g (selfKept g)))

------------------------------------------------------------------------
-- Reuse a spent grade-1 slot in place. The dynamic check demands that
-- the object currently has exactly one reference.
------------------------------------------------------------------------

poke : List Obj → ℕ → ℕ → List Obj
poke []       _       _ = []
poke (_ ∷ hs) zero    v = cell (nat v) live ∷ hs
poke (c ∷ hs) (suc k) v = c ∷ poke hs k v

length-poke : ∀ h k v → length (poke h k v) ≡ length h
length-poke []       _       _ = refl
length-poke (_ ∷ hs) zero    _ = refl
length-poke (_ ∷ hs) (suc k) v rewrite length-poke hs k v = refl

pass : ∀ {A : Set} → Bool → Maybe A → Maybe A
pass true  m = m
pass false _ = nothing

-- A nat write has no children, so the ordered-heap test is true and the
-- v0 clause still reduces to the overwrite.
reuseOk : Sys → ℕ → ℕ → Grade → ℕ → Ref → Bool → Bool → Bool → Maybe Sys
reuseOk (sys h ps) i j g v r true true true =
  pass (childrenBelow (obj r) (nat v))
       (mapSys (poke h (obj r) v) (putRoot ps i j (ref (obj r) g g (selfKept g))))
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

------------------------------------------------------------------------
-- Overwriting a slot with a nat keeps the ordered-heap invariant.
------------------------------------------------------------------------

poke-hit : ∀ h k v o → lookup (poke h k v) k ≡ just o → o ≡ cell (nat v) live
poke-hit []             _       _ _ ()
poke-hit (_ ∷ _)        zero    v .(cell (nat v) live) refl = refl
poke-hit (_ ∷ hs)       (suc k) v o eq = poke-hit hs k v o eq

poke-else : ∀ h k v i → (i ≡ᵇ k) ≡ false → lookup (poke h k v) i ≡ lookup h i
poke-else []             _       _ _       _  = refl
poke-else (_ ∷ _)        zero    _ zero    ()
poke-else (_ ∷ hs)       zero    _ (suc _) _  = refl
poke-else (c ∷ _)        (suc _) _ zero    _  = refl
poke-else (_ ∷ hs)       (suc k) v (suc i) eq = poke-else hs k v i eq

poke-ordered : ∀ h k v → Ordered h → Ordered (poke h k v)
poke-ordered h k v ord i o eq = body h k v ord i o eq
  where
  body : ∀ h k v → Ordered h → ∀ i o →
         lookup (poke h k v) i ≡ just o → Below i (payload o)
  body [] _ _ _ _ _ ()
  body (_ ∷ _) zero v _ zero .(cell (nat v) live) refl = b-nat
  body (_ ∷ hs) zero v ord (suc i) o eq = ord (suc i) o eq
  body (c ∷ hs) (suc _) _ ord zero o eq = ord zero o eq
  body (_ ∷ hs) (suc k) v ord (suc i) o eq = side (i ≡ᵇ k) refl
    where
    side : (b : Bool) → (i ≡ᵇ k) ≡ b → Below (suc i) (payload o)
    side true eb =
      let hit = poke-hit hs k v o
                  (subst (λ j → lookup (poke hs k v) j ≡ just o) (≡ᵇ-sound i k eb) eq)
      in subst (λ o' → Below (suc i) (payload o')) (sym hit) b-nat
    side false eb = ord (suc i) o (trans (sym (poke-else hs k v i eb)) eq)

reuse-ordered : ∀ s i j g v t →
  Ordered (heap s) →
  reuse s i j g v ≡ just t →
  Ordered (heap t)
reuse-ordered (sys h ps) i j g v t ord eq = from (rootAt (sys h ps) i j) eq refl
  where
  from : (m : Maybe Ref) →
         reuse (sys h ps) i j g v ≡ just t →
         rootAt (sys h ps) i j ≡ m →
         Ordered (heap t)
  from nothing e rk rewrite rk with e
  ... | ()
  from (just r) e rk rewrite rk =
    gates (isG1 (checked r)) (isZeroGrade (residual r))
          (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) e refl refl refl
    where
    gates : (a b c : Bool) →
            reuseOk (sys h ps) i j g v r a b c ≡ just t →
            isG1 (checked r) ≡ a →
            isZeroGrade (residual r) ≡ b →
            (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) ≡ c →
            Ordered (heap t)
    gates false _ _ () _ _ _
    gates true false _ () _ _ _
    gates true true false () _ _ _
    gates true true true eG _ _ _ = landed (putRoot ps i j r') eG refl
      where
      r' : Ref
      r' = ref (obj r) g g (selfKept g)
      landed : (m : Maybe (List Proc)) →
               mapSys (poke h (obj r) v) m ≡ just t →
               putRoot ps i j r' ≡ m →
               Ordered (heap t)
      landed nothing () _
      landed (just _) refl _ = poke-ordered h (obj r) v ord

------------------------------------------------------------------------
-- One CBV step. Syntax stays on frames; values are Refs.
-- A g1 pointer is moved, never aliased. A nat is copied.
------------------------------------------------------------------------

anyG1 : List Ref → Bool
anyG1 []       = false
anyG1 (r ∷ rs) = isG1 (checked r) ∨ anyG1 rs

regrade : Ref → Grade → Ref
regrade r g = ref (obj r) g g (selfKept g)

badG1 : Grade → ℕ → List Ref → Bool
badG1 c o rs = isG1 c ∧ not (count o rs ≡ᵇ 1)

gradeAt : Maybe Ref → Grade
gradeAt nothing  = aff
gradeAt (just r) = checked r

predComp : List Ref → ∀ {n} → GTm n → Grade
predComp env (gvar x) = gradeAt (lookup env (toℕ x))
predComp _   _        = aff

payloadAt : List Obj → ℕ → Maybe Val
payloadAt []       _       = nothing
payloadAt (o ∷ _)  zero    = just (payload o)
payloadAt (_ ∷ os) (suc n) = payloadAt os n

setPayload : List Obj → ℕ → Val → List Obj
setPayload []       _       _ = []
setPayload (o ∷ os) zero    v = record o { payload = v } ∷ os
setPayload (o ∷ os) (suc n) v = o ∷ setPayload os n v

setProc : List Proc → ℕ → Ctl → Maybe (List Proc)
setProc []       _ _ = nothing
setProc (p ∷ ps) zero c = just (record p { ctl = c } ∷ ps)
setProc (p ∷ ps) (suc i) c = mapCons p (setProc ps i c)

install : List Obj → List Proc → ℕ → Ctl → Maybe Sys
install h ps i c = mapSys h (setProc ps i c)

freshRef : List Obj → Grade → Ref
freshRef h g = ref (length h) g g (selfKept g)

snoc : List Obj → Val → List Obj
snoc h v = h ++ cell v live ∷ []

useVar : List Obj → List Proc → ℕ → List Ref → List Frame → ℕ → Maybe Ref → Maybe Sys
useVar _ _ _ _ _ _ nothing = nothing
useVar h ps i env k ix (just r) = spent (spendRef r)
  where
  spent : Maybe Ref → Maybe Sys
  spent nothing = nothing
  spent (just r') = see (payloadAt h (obj r))
    where
    env' : List Ref
    env' = repl ix r' env
    ptr : Bool → Maybe Sys
    ptr true =
      pass (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1)
           (install (snoc h (nat zero)) ps i
             (rv r' (repl ix (freshRef h g0) env) k))
    ptr false = install h ps i (rv r' env' k)
    see : Maybe Val → Maybe Sys
    see (just (nat n)) =
      install (snoc h (nat n)) ps i (rv (freshRef h gω) env' k)
    see (just (suc↑ _)) = ptr (isG1 (checked r'))
    see (just (clo _ _)) = ptr (isG1 (checked r'))
    see nothing = nothing

evalTm : ∀ {n} → List Obj → List Proc → ℕ → GTm n → List Ref → List Frame → Maybe Sys
evalRet : List Obj → List Proc → ℕ → Ref → List Ref → List Frame → Maybe Sys

evalTm h ps i (gvar x) env k = useVar h ps i env k (toℕ x) (lookup env (toℕ x))
evalTm h ps i (gtyp _) env k =
  install (snoc h (nat zero)) ps i (rv (freshRef h gω) env k)
evalTm h ps i (gpi _ _ _) env k =
  install (snoc h (nat zero)) ps i (rv (freshRef h gω) env k)
evalTm h ps i (glam c t b) env k =
  pass (not (anyG1 env))
       (install (snoc h (clo env (_ , glam c t b))) ps i
         (rv (freshRef h gω) env k))
evalTm h ps i (gapp f a) env k = install h ps i (ev f env (ar a ∷ k))
evalTm h ps i gze env k =
  install (snoc h (nat zero)) ps i (rv (freshRef h gω) env k)
evalTm h ps i (gsu e) env k = install h ps i (ev e env (su ∷ k))
evalTm h ps i (gmatch e z s) env k = install h ps i (ev e env (mt e z s ∷ k))

beta : List Obj → List Proc → ℕ → Ref → Ref → List Ref → List Frame → Maybe Sys
beta h ps i ra rf env k = opened (payloadAt h (obj rf))
  where
  opened : Maybe Val → Maybe Sys
  opened (just (clo envC (_ , glam c _ body))) =
    pass (not (badG1 c (obj ra) (refsOf (sys h ps))))
    (pass (not (anyG1 envC))
      (install h ps i (ev body (regrade ra c ∷ envC) (bd env ∷ k))))
  opened _ = nothing

onMatch : List Obj → List Proc → ℕ → Ref → List Ref →
          ∀ {n} → GTm n → GTm n → GTm (suc n) → List Frame → Maybe Val → Maybe Sys
onMatch h ps i r env _ z _ k (just (nat zero)) = install h ps i (ev z env k)
onMatch _ _ _ _ _ _ _ _ _ (just (nat (suc _))) = nothing
onMatch h ps i r env e _ s k (just (suc↑ pred)) =
  pass (not (badG1 (predComp env e) (obj pred) (refsOf (sys h ps))))
       (install (setPayload h (obj r) (nat zero)) ps i
         (ev s (regrade pred (predComp env e) ∷ env) k))
onMatch _ _ _ _ _ _ _ _ _ (just (clo _ _)) = nothing
onMatch _ _ _ _ _ _ _ _ _ nothing = nothing

evalRet h ps i r env [] = nothing
evalRet h ps i r env (ar a ∷ k) = install h ps i (ev a env (fn r ∷ k))
evalRet h ps i r env (fn rf ∷ k) = beta h ps i r rf env k
evalRet h ps i r env (su ∷ k) =
  install (snoc h (suc↑ r)) ps i (rv (freshRef h gω) env k)
evalRet h ps i r env (mt e z s ∷ k) = onMatch h ps i r env e z s k (payloadAt h (obj r))
evalRet h ps i r env (bd env0 ∷ k) = install h ps i (rv r env0 k)
-- `saved` is resumed by the process layer, not by `eval1`.
evalRet _ _ _ _ _ (saved _ ∷ _) = nothing

evalHere : List Obj → List Proc → ℕ → Ctl → Maybe Sys
evalHere _ _ _ idle = nothing
evalHere h ps i (ev t env k) = evalTm h ps i t env k
evalHere h ps i (rv r env k) = evalRet h ps i r env k
evalHere _ _ _ (pr _) = nothing

eval1 : Sys → ℕ → Maybe Sys
eval1 (sys h ps) i = at (lookup ps i)
  where
  at : Maybe Proc → Maybe Sys
  at nothing  = nothing
  at (just p) = evalHere h ps i (ctl p)

-- Fuel-bounded evaluation. Structural on the fuel. Stops when eval1 does.
runFor : ℕ → Sys → Sys
runFor zero s = s
runFor (suc n) s with eval1 s zero
... | just t  = runFor n t
... | nothing = s
