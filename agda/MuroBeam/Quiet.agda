------------------------------------------------------------------------
-- B4c. A quiet process stays quiet.
--
-- `Quiet c ps` says pid `c` is in `ps` with state `pstDone` and
-- control `idle`: the shape of the B4a console. `pstep-q` is that
-- every `PStep` keeps it, and `psteps-q` lifts it to `PStep*`.
-- `MuroBeam.Port.console-stays` applies it to pid 1 of every console
-- layout.
--
-- The proof walks every step. The v0 ops and the CEK only touch the
-- process they run (`SetAt`), and a step at pid `c` needs control
-- other than `idle`, so it cannot be one (`NotQ`). `deliver1` and
-- `wake` append to an inbox and keep the state; `consume` (a flush)
-- maps `scrubProc` over all processes, which drops mail but keeps
-- state and control. So the inbox of a quiet process is not claimed
-- to grow, and neither are its roots stated empty here.
-- The case splits of the op lemmas follow the catch-all clauses in
-- `MuroBeam.PRun`; they mirror those definitions one for one.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Quiet where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong)

open import MuroBeam.Lib using (lookup; update; mapCons; ⊥; ⊥-elim)
open import MuroBeam.PRun using
  ( _>>=_; blankEdges; wake; setCtlSt; consume; scrubProc; placeholder; splitGo; blocked
  ; pullCtl; hasTag; deadInCtl; inboxHas; finishAwait; finishFlush; finishPeek; openCont
  ; spawn1; emit1; deliver1; recv1; await1; arm1; flush1; npeek1; ndemon1; seq1; bind1; done1
  ; PStep; PStep*; pdone; pmore; p-lift; p-spawn; p-emit; p-deliver; p-recv
  ; p-await; p-arm; p-flush; p-npeek; p-ndemon; p-seq; p-bind; p-done )
open import Muro.Base using (run)
open import MuroBeam.BTm using
  ( BTm; Arm; arm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch; gref; gcon; gcase )
open import MuroBeam.Grade using (isZeroGrade; isG1; kind; Kmove; Kcopy; selfKept)
open import MuroBeam.Heap using
  (Ref; ref; obj; checked; residual; nat; suc↑; clo; con; spendRef; childrenBelow; count)
open import MuroBeam.Lib using (removeAt)
open import MuroBeam.Process using
  ( Sys; sys; heap; procs; Proc; proc; state; ctl; roots; inbox; Msg; msg
  ; PState; ready; waiting; Ctl; idle; ev; rv; pr
  ; Frame; ar; fn; su; mt; ca; cs; bd; saved; seg
  ; setProc; mapSys; putRoot; post; install; snoc; pass; payloadAt; lookupDef
  ; rootAt; deref; alloc; reuse; eval1; evalTm; evalRet; evalHere
  ; useVar; beta; onMatch; onCase; pickArms; refsOf )
  renaming (done to pstDone; send to v0send; recv to v0recv)
open import MuroBeam.Collect using
  ( collect; clean; Step; step-deref; step-send; step-recv; step-alloc
  ; step-reuse; step-eval; step-collect )
open import MuroBeam.PSyntax using
  ( PTm; done; send; recv; spawn; seq; await; ignore; nignore
  ; awaitT; ignoreT; flushT; ncheckT; ndemonT
  ; go; flight; applyMoves; replyRoot )
open import MuroBeam.Process using (predComp; bindExact; badFields; setPayload; anyG1; badG1)
open import Data.Fin.Base using (toℕ)

------------------------------------------------------------------------
-- A quiet process: `pstDone` with `idle` control.
------------------------------------------------------------------------

QP : Proc → Set
QP p = state p ≡ pstDone × ctl p ≡ idle

-- Pid `c` exists and is quiet.
Quiet : ℕ → List Proc → Set
Quiet c ps = Σ Proc (λ p → lookup ps c ≡ just p × QP p)

-- The process at `i`, if any, is not quiet.
NotQ : ℕ → List Proc → Set
NotQ i ps = ∀ p → lookup ps i ≡ just p → QP p → ⊥

notQ : ∀ ps i {p} → lookup ps i ≡ just p → (ctl p ≡ idle → ⊥) → NotQ i ps
notQ ps i lk ne q lk' (_ , ci) with trans (sym lk) lk'
... | refl = ne ci

------------------------------------------------------------------------
-- Writers.
------------------------------------------------------------------------

setProc-q : ∀ ps i x ps' c → setProc ps i x ≡ just ps' → NotQ i ps → Quiet c ps → Quiet c ps'
setProc-q [] i x ps' c () nq Q
setProc-q (p ∷ ps) zero x .(_ ∷ ps) zero refl nq (q , lk , qp) = ⊥-elim (nq q lk qp)
setProc-q (p ∷ ps) zero x .(_ ∷ ps) (suc c) refl nq Q = Q
setProc-q (p ∷ ps) (suc i) x ps' c eq nq Q with setProc ps i x in e
setProc-q (p ∷ ps) (suc i) x ps' c () nq Q | nothing
setProc-q (p ∷ ps) (suc i) x .(p ∷ qs) zero refl nq Q | just qs = Q
setProc-q (p ∷ ps) (suc i) x .(p ∷ qs) (suc c) refl nq Q | just qs = setProc-q ps i x qs c e nq Q

update-q : ∀ ps i q ps' c → update i q ps ≡ just ps' →
           (∀ p → lookup ps i ≡ just p → QP p → QP q) → Quiet c ps → Quiet c ps'
update-q [] i q ps' c () h Q
update-q (p ∷ ps) zero q .(q ∷ ps) zero refl h (p' , lk , qp) = q , refl , h p' lk qp
update-q (p ∷ ps) zero q .(q ∷ ps) (suc c) refl h Q = Q
update-q (p ∷ ps) (suc i) q ps' c eq h Q with update i q ps in e
update-q (p ∷ ps) (suc i) q ps' c () h Q | nothing
update-q (p ∷ ps) (suc i) q .(p ∷ qs) zero refl h Q | just qs = Q
update-q (p ∷ ps) (suc i) q .(p ∷ qs) (suc c) refl h Q | just qs = update-q ps i q qs c e h Q

putRoot-q : ∀ ps i j r ps' c → putRoot ps i j r ≡ just ps' → Quiet c ps → Quiet c ps'
putRoot-q [] i j r ps' c () Q
putRoot-q (p ∷ ps) zero j r ps' c eq Q with update j r (roots p)
putRoot-q (p ∷ ps) zero j r ps' c () Q | nothing
putRoot-q (p ∷ ps) zero j r .(_ ∷ ps) zero refl (q , refl , qp) | just rs = _ , refl , qp
putRoot-q (p ∷ ps) zero j r .(_ ∷ ps) (suc c) refl Q | just rs = Q
putRoot-q (p ∷ ps) (suc i) j r ps' c eq Q with putRoot ps i j r in e
putRoot-q (p ∷ ps) (suc i) j r ps' c () Q | nothing
putRoot-q (p ∷ ps) (suc i) j r .(p ∷ qs) zero refl Q | just qs = Q
putRoot-q (p ∷ ps) (suc i) j r .(p ∷ qs) (suc c) refl Q | just qs = putRoot-q ps i j r qs c e Q

map-q : ∀ (f : Proc → Proc) → (∀ p → QP p → QP (f p)) → ∀ ps c → Quiet c ps → Quiet c (map f ps)
map-q f h [] c (_ , () , _)
map-q f h (p ∷ ps) zero (q , refl , qp) = f q , refl , h q qp
map-q f h (p ∷ ps) (suc c) Q = map-q f h ps c Q

snoc-q : ∀ ps x c → Quiet c ps → Quiet c (ps ++ x ∷ [])
snoc-q [] x c (_ , () , _)
snoc-q (p ∷ ps) x zero Q = Q
snoc-q (p ∷ ps) x (suc c) Q = snoc-q ps x c Q

mapSys-q : ∀ h m t c → mapSys h m ≡ just t → (∀ ps' → m ≡ just ps' → Quiet c ps') → Quiet c (procs t)
mapSys-q h nothing t c () k
mapSys-q h (just ps') .(sys h ps') c refl k = k ps' refl

wake-q : ∀ p → QP p → QP (wake p)
wake-q (proc j pstDone rs ib cl) qp = qp
wake-q (proc j ready rs ib cl) (() , _)
wake-q (proc j waiting rs ib cl) (() , _)

------------------------------------------------------------------------
-- v0 steps. They write roots and mailboxes, never state or control.
------------------------------------------------------------------------

nope : ∀ {A : Set} {t : A} → nothing ≡ just t → ⊥
nope ()

sameQ : ∀ ps i {p q} {q' : Proc} → lookup ps i ≡ just p → lookup ps i ≡ just q → QP q →
        (QP p → QP q') → QP q'
sameQ ps i lk lk' qp k with trans (sym lk) lk'
... | refl = k qp

-- `update` of the process `lookup` found, with state and control kept.
keepQ : ∀ ps i {p} {q' : Proc} → lookup ps i ≡ just p → (QP p → QP q') →
        ∀ q → lookup ps i ≡ just q → QP q → QP q'
keepQ ps i {p} {q'} lk k q lk' qp = sameQ ps i {p} {q} {q'} lk lk' qp k

deref-q : ∀ h ps i j t c → deref run (sys h ps) i j ≡ just t → Quiet c ps → Quiet c (procs t)
deref-q h ps i j t c eq Q with rootAt (sys h ps) i j
... | nothing = ⊥-elim (nope eq)
... | just r with spendRef r
... | nothing = ⊥-elim (nope eq)
... | just r' with putRoot ps i j r' in e
... | nothing = ⊥-elim (nope eq)
deref-q h ps i j .(sys h qs) c refl Q | just r | just r' | just qs = putRoot-q ps i j r' qs c e Q

recv-q : ∀ h ps i t c → v0recv (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
recv-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with inbox p
... | [] = ⊥-elim (nope eq)
... | msg r ∷ ms with update i (record p { roots = roots p ++ r ∷ [] ; inbox = ms }) ps in e
... | nothing = ⊥-elim (nope eq)
recv-q h ps i .(sys h qs) c refl Q | just p | msg r ∷ ms | just qs =
  update-q ps i p' qs c e (keepQ ps i {p} {p'} lk (λ x → x)) Q
  where p' = record p { roots = roots p ++ r ∷ [] ; inbox = ms }

alloc-q : ∀ h ps i g v t c → alloc (sys h ps) i g v ≡ just t → Quiet c ps → Quiet c (procs t)
alloc-q h ps i g v t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with update i (record p { roots = roots p ++ ref (length h) g g (selfKept g) ∷ [] }) ps in e
... | nothing = ⊥-elim (nope eq)
alloc-q h ps i g v .(sys _ qs) c refl Q | just p | just qs =
  update-q ps i p' qs c e (keepQ ps i {p} {p'} lk (λ x → x)) Q
  where p' = record p { roots = roots p ++ ref (length h) g g (selfKept g) ∷ [] }

reuse-q : ∀ h ps i j g v t c → reuse (sys h ps) i j g v ≡ just t → Quiet c ps → Quiet c (procs t)
reuse-q h ps i j g v t c eq Q with rootAt (sys h ps) i j
... | nothing = ⊥-elim (nope eq)
... | just r with isG1 (checked r) | isZeroGrade (residual r) | count (obj r) (refsOf (sys h ps)) ≡ᵇ 1
... | false | _ | _ = ⊥-elim (nope eq)
... | true | false | _ = ⊥-elim (nope eq)
... | true | true | false = ⊥-elim (nope eq)
... | true | true | true with putRoot ps i j (ref (obj r) g g (selfKept g)) in e
... | nothing = ⊥-elim (nope eq)
reuse-q h ps i j g v .(sys _ qs) c refl Q | just r | true | true | true | just qs =
  putRoot-q ps i j _ qs c e Q

collect-q : ∀ s c → Quiet c (procs s) → Quiet c (procs (collect s))
collect-q s c Q = map-q clean (λ p qp → qp) (procs s) c Q

-- The last write of most steps.
landQ : ∀ {h qs t c} → just (sys h qs) ≡ just t → Quiet c qs → Quiet c (procs t)
landQ refl Q = Q

send-q : ∀ h ps si sj ri t c → v0send (sys h ps) si sj ri ≡ just t → Quiet c ps → Quiet c (procs t)
send-q h ps si sj ri t c eq Q with lookup ps si in lk
... | nothing = ⊥-elim (nope eq)
... | just sp with removeAt sj (roots sp)
... | nothing = ⊥-elim (nope eq)
... | just (r , rs) with isZeroGrade (residual r)
... | true = ⊥-elim (nope eq)
... | false with kind (checked r)
... | nothing = ⊥-elim (nope eq)
... | just Kcopy with lookup ps ri in lk2
... | nothing = ⊥-elim (nope eq)
... | just q with update ri (post q r) ps in e
... | nothing = ⊥-elim (nope eq)
... | just qs = landQ eq (update-q ps ri (post q r) qs c e (keepQ ps ri {q} {post q r} lk2 (λ x → x)) Q)
send-q h ps si sj ri t c eq Q | just sp | just (r , rs) | false | just Kmove with si ≡ᵇ ri
... | true with update si (post (record sp { roots = rs }) r) ps in e
... | nothing = ⊥-elim (nope eq)
... | just qs =
  landQ eq (update-q ps si _ qs c e
    (keepQ ps si {sp} {post (record sp { roots = rs }) r} lk (λ x → x)) Q)
send-q h ps si sj ri t c eq Q | just sp | just (r , rs) | false | just Kmove | false
  with update si (record sp { roots = rs }) ps in e1
... | nothing = ⊥-elim (nope eq)
... | just ps1 with lookup ps1 ri in lk2
... | nothing = ⊥-elim (nope eq)
... | just q with update ri (post q r) ps1 in e2
... | nothing = ⊥-elim (nope eq)
... | just qs =
  landQ eq (update-q ps1 ri (post q r) qs c e2 (keepQ ps1 ri {q} {post q r} lk2 (λ x → x))
    (update-q ps si _ ps1 c e1 (keepQ ps si {sp} {record sp { roots = rs }} lk (λ x → x)) Q))

------------------------------------------------------------------------
-- The CEK step writes the control of the process it runs, and only
-- through `install`.
------------------------------------------------------------------------

SetAt : List Proc → ℕ → Sys → Set
SetAt ps i t = Σ Ctl (λ x → setProc ps i x ≡ just (procs t))

procsJ : ∀ {h qs t} → just (sys h qs) ≡ just t → qs ≡ procs t
procsJ refl = refl

inst : ∀ h ps i y t → install h ps i y ≡ just t → SetAt ps i t
inst h ps i y t eq with setProc ps i y in e
... | nothing = ⊥-elim (nope eq)
... | just qs = y , trans e (cong just (procsJ eq))

passJ : ∀ {A : Set} b (m : Maybe A) {t} → pass b m ≡ just t → m ≡ just t
passJ true  m eq = eq
passJ false m ()

useVar-i : ∀ h ps i env k ix mr t → useVar h ps i env k ix mr ≡ just t → SetAt ps i t
useVar-i h ps i env k ix nothing t ()
useVar-i h ps i env k ix (just r) t eq with spendRef r
... | nothing = ⊥-elim (nope eq)
... | just r' with payloadAt h (obj r)
... | nothing = ⊥-elim (nope eq)
... | just (nat n) = inst _ ps i _ t eq
... | just (suc↑ _) with isG1 (checked r')
...   | true  = inst _ ps i _ t (passJ _ _ eq)
...   | false = inst _ ps i _ t eq
useVar-i h ps i env k ix (just r) t eq | just r' | just (clo _ _) with isG1 (checked r')
...   | true  = inst _ ps i _ t (passJ _ _ eq)
...   | false = inst _ ps i _ t eq
useVar-i h ps i env k ix (just r) t eq | just r' | just (con _ _) with isG1 (checked r')
...   | true  = inst _ ps i _ t (passJ _ _ eq)
...   | false = inst _ ps i _ t eq

evalTm-i : ∀ {n} h ps i (e : BTm n) env k t → evalTm h ps i e env k ≡ just t → SetAt ps i t
evalTm-i h ps i (gvar x) env k t eq = useVar-i h ps i env k (toℕ x) (lookup env (toℕ x)) t eq
evalTm-i h ps i (gtyp _) env k t eq = inst _ ps i _ t eq
evalTm-i h ps i (gpi _ _ _) env k t eq = inst _ ps i _ t eq
evalTm-i h ps i (glam _ _ _) env k t eq = inst _ ps i _ t (passJ _ _ eq)
evalTm-i h ps i (gapp _ _) env k t eq = inst _ ps i _ t eq
evalTm-i h ps i gze env k t eq = inst _ ps i _ t eq
evalTm-i h ps i (gsu _) env k t eq = inst _ ps i _ t eq
evalTm-i h ps i (gmatch _ _ _) env k t eq = inst _ ps i _ t eq
evalTm-i h ps i (gcon _ []) env k t eq = inst _ ps i _ t eq
evalTm-i h ps i (gcon _ (_ ∷ _)) env k t eq = inst _ ps i _ t eq
evalTm-i h ps i (gcase _ _) env k t eq = inst _ ps i _ t eq
evalTm-i h ps i (gref d) env k t eq with lookupDef k d
... | just _  = inst _ ps i _ t eq
... | nothing = ⊥-elim (nope eq)

beta-i : ∀ h ps i ra rf env k t → beta h ps i ra rf env k ≡ just t → SetAt ps i t
beta-i h ps i ra rf env k t eq with payloadAt h (obj rf)
... | just (clo envC (_ , glam c _ body)) =
  inst h ps i _ t
    (passJ (not (anyG1 envC)) _
      (passJ (not (badG1 c (obj ra) (refsOf (sys h ps)))) _ eq))
... | just (clo _ (_ , gvar _)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gtyp _)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gpi _ _ _)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gapp _ _)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gze)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gsu _)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gmatch _ _ _)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gref _)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gcon _ _)) = ⊥-elim (nope eq)
... | just (clo _ (_ , gcase _ _)) = ⊥-elim (nope eq)
... | just (nat _) = ⊥-elim (nope eq)
... | just (suc↑ _) = ⊥-elim (nope eq)
... | just (con _ _) = ⊥-elim (nope eq)
... | nothing = ⊥-elim (nope eq)

onMatch-i : ∀ h ps i r env {n} (e z : BTm n) s k mv t →
            onMatch h ps i r env e z s k mv ≡ just t → SetAt ps i t
onMatch-i h ps i r env e z s k (just (nat zero)) t eq = inst _ ps i _ t eq
onMatch-i h ps i r env e z s k (just (nat (suc _))) t ()
onMatch-i h ps i r env e z s k (just (suc↑ _)) t eq = inst _ ps i _ t (passJ _ _ eq)
onMatch-i h ps i r env e z s k (just (clo _ _)) t ()
onMatch-i h ps i r env e z s k (just (con _ _)) t ()
onMatch-i h ps i r env e z s k nothing t ()

pickArms-i : ∀ h ps i r env {n} (e : BTm n) (as : List (Arm n)) k tg rs t →
             pickArms h ps i r env e as k tg rs ≡ just t → SetAt ps i t
pickArms-i h ps i r env e [] k tg rs t ()
pickArms-i h ps i r env e (arm atag binds body ∷ rest) k tg rs t eq
  with atag ≡ᵇ tg | bindExact binds (predComp env e) rs env
... | false | _ = pickArms-i h ps i r env e rest k tg rs t eq
... | true | nothing = ⊥-elim (nope eq)
... | true | just _ = inst _ ps i _ t (passJ _ _ eq)

onCase-i : ∀ h ps i r env {n} (e : BTm n) as k mv t →
           onCase h ps i r env e as k mv ≡ just t → SetAt ps i t
onCase-i h ps i r env e as k nothing t ()
onCase-i h ps i r env e as k (just (nat _)) t ()
onCase-i h ps i r env e as k (just (suc↑ _)) t ()
onCase-i h ps i r env e as k (just (clo _ _)) t ()
onCase-i h ps i r env e as k (just (con tg rs)) t eq = pickArms-i h ps i r env e as k tg rs t eq

evalRet-i : ∀ h ps i r env k t → evalRet h ps i r env k ≡ just t → SetAt ps i t
evalRet-i h ps i r env [] t ()
evalRet-i h ps i r env (ar _ ∷ k) t eq = inst _ ps i _ t eq
evalRet-i h ps i r env (fn rf ∷ k) t eq = beta-i h ps i r rf env k t eq
evalRet-i h ps i r env (su ∷ k) t eq = inst _ ps i _ t eq
evalRet-i h ps i r env (mt e z s ∷ k) t eq = onMatch-i h ps i r env e z s k (payloadAt h (obj r)) t eq
evalRet-i h ps i r env (ca _ _ [] ∷ k) t eq = inst _ ps i _ t eq
evalRet-i h ps i r env (ca _ _ (_ ∷ _) ∷ k) t eq = inst _ ps i _ t eq
evalRet-i h ps i r env (cs e as ∷ k) t eq = onCase-i h ps i r env e as k (payloadAt h (obj r)) t eq
evalRet-i h ps i r env (bd _ ∷ k) t eq = inst _ ps i _ t eq
evalRet-i h ps i r env (saved _ ∷ k) t ()
evalRet-i h ps i r env (seg _ ∷ k) t ()

eval-q : ∀ h ps i t c → eval1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
eval-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev e env k =
  setProc-q ps i (proj₁ sx) (procs t) c (proj₂ sx)
    (notQ ps i lk (λ ci → ev≢ (trans (sym cp) ci))) Q
  where sx = evalTm-i h ps i e env k t eq
        ev≢ : ev e env k ≡ idle → ⊥
        ev≢ ()
... | rv r env k =
  setProc-q ps i (proj₁ sx) (procs t) c (proj₂ sx)
    (notQ ps i lk (λ ci → rv≢ (trans (sym cp) ci))) Q
  where sx = evalRet-i h ps i r env k t eq
        rv≢ : rv r env k ≡ idle → ⊥
        rv≢ ()
... | pr _ = ⊥-elim (nope eq)

------------------------------------------------------------------------
-- Process steps. Each one reads the control of the process it runs,
-- and a quiet process has none of those controls.
------------------------------------------------------------------------

pr≢ : ∀ {c} → pr c ≡ idle → ⊥
pr≢ ()

rv≢ : ∀ {r env k} → rv r env k ≡ idle → ⊥
rv≢ ()

nqPr : ∀ ps i {p c} → lookup ps i ≡ just p → ctl p ≡ pr c → NotQ i ps
nqPr ps i lk cp = notQ ps i lk (λ ci → pr≢ (trans (sym cp) ci))

nqRv : ∀ ps i {p r env k} → lookup ps i ≡ just p → ctl p ≡ rv r env k → NotQ i ps
nqRv ps i lk cp = notQ ps i lk (λ ci → rv≢ (trans (sym cp) ci))

noQ : ∀ ps i → NotQ i ps → ∀ (q' : Proc) q → lookup ps i ≡ just q → QP q → QP q'
noQ ps i nq q' q lk qp = ⊥-elim (nq q lk qp)

setCtlSt-q : ∀ ps i x st ps' c → setCtlSt ps i x st ≡ just ps' → NotQ i ps → Quiet c ps → Quiet c ps'
setCtlSt-q [] i x st ps' c () nq Q
setCtlSt-q (p ∷ ps) zero x st .(_ ∷ ps) zero refl nq (q , lk , qp) = ⊥-elim (nq q lk qp)
setCtlSt-q (p ∷ ps) zero x st .(_ ∷ ps) (suc c) refl nq Q = Q
setCtlSt-q (p ∷ ps) (suc i) x st ps' c eq nq Q with setCtlSt ps i x st in e
setCtlSt-q (p ∷ ps) (suc i) x st ps' c () nq Q | nothing
setCtlSt-q (p ∷ ps) (suc i) x st .(p ∷ qs) zero refl nq Q | just qs = Q
setCtlSt-q (p ∷ ps) (suc i) x st .(p ∷ qs) (suc c) refl nq Q | just qs =
  setCtlSt-q ps i x st qs c e nq Q

setJ : ∀ {h ps i x t c} → (setProc ps i x >>= λ ps' → just (sys h ps')) ≡ just t →
       NotQ i ps → Quiet c ps → Quiet c (procs t)
setJ {h} {ps} {i} {x} {t} {c} eq nq Q with setProc ps i x in e
... | nothing = ⊥-elim (nope eq)
... | just qs = landQ eq (setProc-q ps i x qs c e nq Q)

setStJ : ∀ {h ps i x st t c} → (setCtlSt ps i x st >>= λ ps' → just (sys h ps')) ≡ just t →
         NotQ i ps → Quiet c ps → Quiet c (procs t)
setStJ {h} {ps} {i} {x} {st} {t} {c} eq nq Q with setCtlSt ps i x st in e
... | nothing = ⊥-elim (nope eq)
... | just qs = landQ eq (setCtlSt-q ps i x st qs c e nq Q)

updJ : ∀ {h ps i q t c} → (update i q ps >>= λ ps' → just (sys h ps')) ≡ just t →
       (∀ q0 → lookup ps i ≡ just q0 → QP q0 → QP q) → Quiet c ps → Quiet c (procs t)
updJ {h} {ps} {i} {q} {t} {c} eq k Q with update i q ps in e
... | nothing = ⊥-elim (nope eq)
... | just qs = landQ eq (update-q ps i q qs c e k Q)

updNQ : ∀ {h ps i q t c} → (update i q ps >>= λ ps' → just (sys h ps')) ≡ just t →
        NotQ i ps → Quiet c ps → Quiet c (procs t)
updNQ {h} {ps} {i} {q} {t} {c} eq nq Q = updJ {h} {ps} {i} {q} {t} {c} eq (noQ ps i nq q) Q

scrub-qp : ∀ τ ph p → QP p → QP (scrubProc τ ph p)
scrub-qp τ ph p (st , ct) rewrite ct = st , refl

-- `consume` scrubs every process, then writes the control of `i`.
consume-q : ∀ h ps i τ (finish : ℕ → Ctl → Maybe Ctl) t c → finish τ idle ≡ nothing →
            consume (sys h ps) i τ finish ≡ just t → Quiet c ps → Quiet c (procs t)
consume-q h ps i τ finish t c fi eq Q with lookup (map (scrubProc τ (placeholder h)) ps) i in lk
... | nothing = ⊥-elim (nope eq)
... | just p1 with finish τ (ctl p1) in fe
... | nothing = ⊥-elim (nope eq)
... | just c' =
  setStJ {h = snoc (blankEdges τ h) (nat zero)} {ps = map (scrubProc τ (placeholder h)) ps} {i = i} eq (notQ (map (scrubProc τ (placeholder h)) ps) i lk (λ ci → nope (trans (sym fi) (trans (cong (finish τ) (sym ci)) fe))))
    (map-q (scrubProc τ (placeholder h)) (scrub-qp τ (placeholder h)) ps c Q)

spawn-q : ∀ h ps i t c → spawn1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
spawn-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn th ch pa) env eth d dm) with splitGo zero (placeholder h) th env
...   | nothing = ⊥-elim (nope eq)
...   | just (ce , pe , mv) with setProc ps i (pr (go (applyMoves mv pa) pe eth d dm)) in e
...     | nothing = ⊥-elim (nope eq)
...     | just ps1 = landQ eq (snoc-q ps1 _ c (setProc-q ps i _ ps1 c e (nqPr ps i lk cp) Q))

emit-q : ∀ h ps i t c → emit1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
emit-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send j x k) env eth d dm) with lookup env (toℕ x)
...   | nothing = ⊥-elim (nope eq)
...   | just r with isZeroGrade (residual r)
...     | true = ⊥-elim (nope eq)
...     | false with blocked ps j (obj r)
...       | true = ⊥-elim (nope eq)
...       | false with kind (checked r)
...         | nothing = ⊥-elim (nope eq)
...         | just Kmove = setJ {h = snoc h (nat zero)} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q
...         | just Kcopy = setJ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q

deliver-q : ∀ h ps i t c → deliver1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
deliver-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with pullCtl (ctl p) in pc
...   | nothing = ⊥-elim (nope eq)
...   | just (flight j r , c1) with setProc ps i c1 in e1
...     | nothing = ⊥-elim (nope eq)
...     | just ps1 with lookup ps1 j in lk2
...       | nothing = ⊥-elim (nope eq)
...       | just q with hasTag (obj r) (deadInCtl (ctl q))
...         | true = landQ eq (setProc-q ps i c1 ps1 c e1 (notQ ps i lk (λ ci → nope (trans (sym (cong pullCtl ci)) pc))) Q)
...         | false =
  updJ {h = h} {ps = ps1} {i = j} eq (keepQ ps1 j {q} {wake (post q r)} lk2 (wake-q (post q r)))
    (setProc-q ps i c1 ps1 c e1 (notQ ps i lk (λ ci → nope (trans (sym (cong pullCtl ci)) pc))) Q)

recvP-q : ∀ h ps i t c → recv1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
recvP-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ k) env eth d dm) with inbox p
...   | msg r ∷ ms = updNQ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q
...   | [] with state p
...     | ready = updNQ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q
...     | waiting = ⊥-elim (nope eq)
...     | pstDone = ⊥-elim (nope eq)

await-q : ∀ h ps i t c → await1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
await-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT τ k) env eth d dm) with inboxHas (inbox p) τ
...   | true = consume-q h ps i τ finishAwait t c refl eq Q
...   | false with state p
...     | ready = setStJ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q
...     | waiting = ⊥-elim (nope eq)
...     | pstDone = ⊥-elim (nope eq)

arm-q : ∀ h ps i t c → arm1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
arm-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT τ k) env eth d dm) = setJ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q

flush-q : ∀ h ps i t c → flush1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
flush-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT τ k) env eth d dm) = consume-q h ps i τ finishFlush t c refl eq Q

npeek-q : ∀ h ps i t c → npeek1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
npeek-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT τ k) env eth d dm) with inboxHas (inbox p) τ
...   | true = consume-q h ps i τ finishPeek t c refl eq Q
...   | false = setJ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q

ndemon-q : ∀ h ps i t c → ndemon1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
ndemon-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT τ k) env eth d dm) = setJ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q

seq-q : ∀ h ps i t c → seq1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
seq-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go done _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq ds e k) env eth d dm) = setJ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q

done-q : ∀ h ps i t c → done1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
done-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | rv _ _ _ = ⊥-elim (nope eq)
... | pr (go (send _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (recv _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (spawn _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (seq _ _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (await _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (nignore _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (awaitT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ignoreT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (flushT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ncheckT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go (ndemonT _ _) _ _ _ _) = ⊥-elim (nope eq)
... | pr (go done _ eth d dm) = updNQ {h = h} {ps = ps} {i = i} eq (nqPr ps i lk cp) Q

bind-q : ∀ h ps i t c → bind1 (sys h ps) i ≡ just t → Quiet c ps → Quiet c (procs t)
bind-q h ps i t c eq Q with lookup ps i in lk
... | nothing = ⊥-elim (nope eq)
... | just p with ctl p in cp
... | idle = ⊥-elim (nope eq)
... | ev _ _ _ = ⊥-elim (nope eq)
... | pr _ = ⊥-elim (nope eq)
... | rv r env [] = ⊥-elim (nope eq)
... | rv r env ((ar _) ∷ _) = ⊥-elim (nope eq)
... | rv r env ((fn _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (su ∷ _) = ⊥-elim (nope eq)
... | rv r env ((mt _ _ _) ∷ _) = ⊥-elim (nope eq)
... | rv r env ((ca _ _ _) ∷ _) = ⊥-elim (nope eq)
... | rv r env ((cs _ _) ∷ _) = ⊥-elim (nope eq)
... | rv r env ((bd _) ∷ _) = ⊥-elim (nope eq)
... | rv r env ((seg _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ []) = setJ {h = h} {ps = ps} {i = i} eq (nqRv ps i lk cp) Q
... | rv r env (saved (go k cenv eth d dm) ∷ (ar _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ (fn _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ su ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ (mt _ _ _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ (ca _ _ _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ (cs _ _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ (bd _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ (saved _) ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ seg _ ∷ _ ∷ _) = ⊥-elim (nope eq)
... | rv r env (saved (go k cenv eth d dm) ∷ seg _ ∷ []) with openCont k
...   | false = ⊥-elim (nope eq)
...   | true with replyRoot k
...     | false = setJ {h = h} {ps = ps} {i = i} eq (nqRv ps i lk cp) Q
...     | true with isG1 (checked r) | count (obj r) (refsOf (sys h ps)) ≡ᵇ 1
...       | true | _ = setJ {h = h} {ps = ps} {i = i} eq (nqRv ps i lk cp) Q
...       | false | false = ⊥-elim (nope eq)
...       | false | true = setJ {h = h} {ps = ps} {i = i} eq (nqRv ps i lk cp) Q


------------------------------------------------------------------------
-- Every `PStep` keeps a quiet pid quiet.
------------------------------------------------------------------------

pstep-q : ∀ {s t} c → PStep s t → Quiet c (procs s) → Quiet c (procs t)
pstep-q {sys h ps} c (p-lift (step-deref {i = i} {j = j} eq)) Q = deref-q h ps i j _ c eq Q
pstep-q {sys h ps} c (p-lift (step-send {i = i} {j = j} {k = k} eq)) Q = send-q h ps i j k _ c eq Q
pstep-q {sys h ps} c (p-lift (step-recv {i = i} eq)) Q = recv-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-lift (step-alloc {i = i} {g = g} {v = v} eq)) Q = alloc-q h ps i g v _ c eq Q
pstep-q {sys h ps} c (p-lift (step-reuse {i = i} {j = j} {g = g} {v = v} eq)) Q = reuse-q h ps i j g v _ c eq Q
pstep-q {sys h ps} c (p-lift (step-eval {i = i} eq)) Q = eval-q h ps i _ c eq Q
pstep-q {s} c (p-lift step-collect) Q = collect-q s c Q
pstep-q {sys h ps} c (p-spawn {i = i} eq) Q = spawn-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-emit {i = i} eq) Q = emit-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-deliver {i = i} eq) Q = deliver-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-recv {i = i} eq) Q = recvP-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-await {i = i} eq) Q = await-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-arm {i = i} eq) Q = arm-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-flush {i = i} eq) Q = flush-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-npeek {i = i} eq) Q = npeek-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-ndemon {i = i} eq) Q = ndemon-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-seq {i = i} eq) Q = seq-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-bind {i = i} eq) Q = bind-q h ps i _ c eq Q
pstep-q {sys h ps} c (p-done {i = i} eq) Q = done-q h ps i _ c eq Q

psteps-q : ∀ {s t} c → PStep* s t → Quiet c (procs s) → Quiet c (procs t)
psteps-q c pdone Q = Q
psteps-q c (pmore st tr) Q = psteps-q c tr (pstep-q c st Q)

