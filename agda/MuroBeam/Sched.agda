------------------------------------------------------------------------
-- Round-robin driver. Fuel, a cursor, and a list of meetings beside
-- the system. There is no fairness theorem and no coinductive loop.
--
-- `drive` returns the final system, so `drive-sound` can name it.
-- The `PStep*` is built with the steps: every process pop is one
-- `PStep`, and `halted` adds `step-collect`. A meeting update is not
-- a `PStep`. `tr-down` is that extra event. `observe` never writes
-- the process system; `stepDone` may set `halted` and then the base
-- is put back.
--
-- `done1` still succeeds on a process that is already `pstDone`.
-- `emitDone1` refuses that stutter, so it is not an `At` step. A
-- deadlock is "no `At` step for any pid", which is that test, not
-- the stutter. `emit` is taken through `emitEmit`: a send the
-- wrapper cannot name is not an `At` step. The other wrappers are
-- `emitDone` of the operation, so a refusal is the operation's
-- refusal.
--
-- Collect runs only at halt. `Outcome.halted` stores the pre-collect
-- system, the proof it was all `pstDone`, and `t ≡ collect pre`.
-- Heap emptiness is `done-collect-empty` on that pre-state when its
-- `liveRefs` are empty. It is not a consequence of `halted` alone.
--
-- The value is the first nat read from a delivered message, or from
-- pid 0's `rv` once that return is parked on `saved` or an empty
-- continuation. An intermediate return under `su` or `fn` is not the
-- answer. `suc↑` is followed the way `RunImage.readRef` does.
-- `done1` clears the environment, so the nat is taken before that.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Sched where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import MuroBeam.Collect using (Step; step-collect; step-eval; collect; clean; markVec)
open import MuroBeam.Death using (Meet; base; observe; stepDone; DRun; dran; observer; noted)
open import MuroBeam.Emit using
  ( Run; ran; Pop
  ; pop-spawn; pop-emit; pop-deliver; pop-recv
  ; pop-await; pop-arm; pop-flush; pop-npeek; pop-ndemon
  ; pop-seq; pop-bind; pop-done; pop-eval
  ; emitPop; emitSpawn; emitEmit; emitDeliver; emitRecv1
  ; emitAwait; emitArm; emitFlush; emitNpeek; emitNdemon
  ; emitSeq; emitBind; emitDone1; emitEval; emitDone
  ; emitFromCtl; recvFromStep; peekSend; freedIdx
  ; SendInfo; sent )
open import MuroBeam.Event using (Event; tr-collect)
open import MuroBeam.Heap using (Obj; Val; nat; suc↑; clo; Ref; obj)
open import MuroBeam.Lib using (lookup; ⊥; ⊥-elim; ¬_)
open import MuroBeam.PRun using
  ( PStep; PStep*; pdone; pmore; p-lift
  ; p-spawn; p-emit; p-deliver; p-recv
  ; p-await; p-arm; p-flush; p-npeek; p-ndemon
  ; p-seq; p-bind; p-done
  ; spawn1; emit1; emitCtl; deliver1; recv1; recvStep
  ; await1; arm1; flush1; npeek1; ndemon1
  ; seq1; bind1; done1; doneStep )
open import MuroBeam.Process using
  ( Sys; sys; heap; procs; Proc; proc; state; ctl; inbox
  ; PState; ready; waiting
  ; Ctl; idle; ev; rv; pr
  ; Frame; saved
  ; Msg; msg
  ; payloadAt; eval1 )
  renaming (done to pstDone)

------------------------------------------------------------------------
-- One enabled wrapper. `At` is a step the scheduler would take.
------------------------------------------------------------------------

data K : Set where
  k-deliver : K
  k-seq     : K
  k-bind    : K
  k-spawn   : K
  k-emit    : K
  k-await   : K
  k-arm     : K
  k-flush   : K
  k-npeek   : K
  k-ndemon  : K
  k-recv    : K
  k-done    : K
  k-eval    : K

spine : List K
spine =
  k-deliver ∷ k-seq ∷ k-bind ∷ k-spawn ∷ k-emit ∷
  k-await ∷ k-arm ∷ k-flush ∷ k-npeek ∷ k-ndemon ∷
  k-recv ∷ k-done ∷ k-eval ∷ []

popK : ℕ → K → Pop
popK i k-deliver = pop-deliver i
popK i k-seq     = pop-seq i
popK i k-bind    = pop-bind i
popK i k-spawn   = pop-spawn i
popK i k-emit    = pop-emit i
popK i k-await   = pop-await i
popK i k-arm     = pop-arm i
popK i k-flush   = pop-flush i
popK i k-npeek   = pop-npeek i
popK i k-ndemon  = pop-ndemon i
popK i k-recv    = pop-recv i
popK i k-done    = pop-done i
popK i k-eval    = pop-eval i

emitK : Sys → ℕ → K → Maybe Run
emitK s i k-deliver = emitDeliver s i
emitK s i k-seq     = emitSeq s i
emitK s i k-bind    = emitBind s i
emitK s i k-spawn   = emitSpawn s i
emitK s i k-emit    = emitEmit s i
emitK s i k-await   = emitAwait s i
emitK s i k-arm     = emitArm s i
emitK s i k-flush   = emitFlush s i
emitK s i k-npeek   = emitNpeek s i
emitK s i k-ndemon  = emitNdemon s i
emitK s i k-recv    = emitRecv1 s i
emitK s i k-done    = emitDone1 s i
emitK s i k-eval    = emitEval s i

-- `emitPop` of the pop `popK` builds is the same wrapper.
same : ∀ s i k → emitPop s (popK i k) ≡ emitK s i k
same s i k-deliver = refl
same s i k-seq     = refl
same s i k-bind    = refl
same s i k-spawn   = refl
same s i k-emit    = refl
same s i k-await   = refl
same s i k-arm     = refl
same s i k-flush   = refl
same s i k-npeek   = refl
same s i k-ndemon  = refl
same s i k-recv    = refl
same s i k-done    = refl
same s i k-eval    = refl

record Hit (s : Sys) (i : ℕ) : Set where
  constructor hit
  field
    kind    : K
    run     : Run
    agrees  : emitK s i kind ≡ just run

open Hit public

-- A wrapper result, with the equality `with` would otherwise lose.
data Res (s : Sys) (i : ℕ) (k : K) : Set where
  yes : (r : Run) → emitK s i k ≡ just r → Res s i k
  no  : emitK s i k ≡ nothing → Res s i k

res : ∀ s i k → Res s i k
res s i k with emitK s i k in eq
... | just r  = yes r eq
... | nothing = no eq

firstHit : (s : Sys) → (i : ℕ) → List K → Maybe (Hit s i)
firstHit s i [] = nothing
firstHit s i (k ∷ ks) with res s i k
... | yes r eq = just (hit k r eq)
... | no _     = firstHit s i ks

-- Plan's `enabled`. Eliminating the `Maybe` keeps the equality
-- `firstHit ≡ nothing` usable by `rewrite`, which a `with` loses.
enabled : Sys → ℕ → Maybe Pop
enabled s i = enable (firstHit s i spine)
  where
  enable : Maybe (Hit s i) → Maybe Pop
  enable nothing = nothing
  enable (just h) = just (popK i (kind h))

data InK : K → List K → Set where
  hereK  : ∀ {k ks} → InK k (k ∷ ks)
  thereK : ∀ {k j ks} → InK k ks → InK k (j ∷ ks)

memK : ∀ k → InK k spine
memK k-deliver = hereK
memK k-seq     = thereK hereK
memK k-bind    = thereK (thereK hereK)
memK k-spawn   = thereK (thereK (thereK hereK))
memK k-emit    = thereK (thereK (thereK (thereK hereK)))
memK k-await   = thereK (thereK (thereK (thereK (thereK hereK))))
memK k-arm     = thereK (thereK (thereK (thereK (thereK (thereK hereK)))))
memK k-flush   = thereK (thereK (thereK (thereK (thereK (thereK (thereK hereK))))))
memK k-npeek   = thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK hereK)))))))
memK k-ndemon  = thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK hereK))))))))
memK k-recv    = thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK hereK)))))))))
memK k-done    = thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK hereK))))))))))
memK k-eval    = thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK (thereK hereK)))))))))))

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
just≢nothing ()

hit-quiet : ∀ s i ks k → firstHit s i ks ≡ nothing → InK k ks → emitK s i k ≡ nothing
hit-quiet s i [] k eq ()
hit-quiet s i (k0 ∷ ks) k eq mem with res s i k0
hit-quiet s i (k0 ∷ ks) k eq mem | yes _ _ = ⊥-elim (just≢nothing eq)
hit-quiet s i (k0 ∷ ks) .k0 eq hereK | no eqK = eqK
hit-quiet s i (k0 ∷ ks) k eq (thereK m) | no _ =
  hit-quiet s i ks k eq m

data FH (s : Sys) (i : ℕ) : Set where
  fh-yes : (h : Hit s i) → firstHit s i spine ≡ just h → FH s i
  fh-no  : firstHit s i spine ≡ nothing → FH s i

fh : ∀ s i → FH s i
fh s i with firstHit s i spine in eq
... | just h  = fh-yes h eq
... | nothing = fh-no eq

en-yes : ∀ {s i h} →
  firstHit s i spine ≡ just h →
  enabled s i ≡ just (popK i (kind h))
en-yes eq rewrite eq = refl

en-hit : ∀ s i → enabled s i ≡ nothing → firstHit s i spine ≡ nothing
en-hit s i eq with fh s i
... | fh-no eqF     = eqF
... | fh-yes h eqH = ⊥-elim (just≢nothing (trans (sym (en-yes eqH)) eq))

-- `enabled i ≡ nothing` means every wrapper refuses.
enabled-quiet : ∀ {s i} → enabled s i ≡ nothing → ∀ k → emitK s i k ≡ nothing
enabled-quiet {s} {i} eq k = hit-quiet s i spine k (en-hit s i eq) (memK k)

data At (i : ℕ) : Sys → Sys → Set where
  at : ∀ {s t es} (k : K) → emitK s i k ≡ just (ran t es) → At i s t

-- The stuttering `p-done` is not an `At`. Neither is an `emit1` that
-- `emitEmit` refuses.
enabled-blocked : ∀ {s i t} → enabled s i ≡ nothing → ¬ At i s t
enabled-blocked {s} {i} eq (at k op) = just≢nothing (trans (sym op) (enabled-quiet eq k))

------------------------------------------------------------------------
-- A wrapper that returns a system is a `PStep`.
--
-- The link lemmas are `abstract`. Each exported equation is a plain
-- call. The `with` sits in a local `go`, so a caller does not unfold
-- it. Unfolding a `with` on `spawn1` makes Agda invert `_>>=_` and
-- lose the record fields. The type is the part `pop-pstep` needs.
------------------------------------------------------------------------

ran-sys : ∀ {a b ea eb} → just (ran a ea) ≡ just (ran b eb) → a ≡ b
ran-sys refl = refl

abstract
  deliver-ran : ∀ {h ps i t es} →
    emitDeliver (sys h ps) i ≡ just (ran t es) → deliver1 (sys h ps) i ≡ just t
  deliver-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitDeliver (sys h ps) i ≡ just (ran t es) → deliver1 (sys h ps) i ≡ just t
    go eq1 with deliver1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  eval-ran : ∀ {h ps i t es} →
    emitEval (sys h ps) i ≡ just (ran t es) → eval1 (sys h ps) i ≡ just t
  eval-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitEval (sys h ps) i ≡ just (ran t es) → eval1 (sys h ps) i ≡ just t
    go eq1 with eval1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  spawn-ran : ∀ {h ps i t es} →
    emitSpawn (sys h ps) i ≡ just (ran t es) → spawn1 (sys h ps) i ≡ just t
  spawn-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitSpawn (sys h ps) i ≡ just (ran t es) → spawn1 (sys h ps) i ≡ just t
    go eq1 with spawn1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  await-ran : ∀ {h ps i t es} →
    emitAwait (sys h ps) i ≡ just (ran t es) → await1 (sys h ps) i ≡ just t
  await-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitAwait (sys h ps) i ≡ just (ran t es) → await1 (sys h ps) i ≡ just t
    go eq1 with await1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  arm-ran : ∀ {h ps i t es} →
    emitArm (sys h ps) i ≡ just (ran t es) → arm1 (sys h ps) i ≡ just t
  arm-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitArm (sys h ps) i ≡ just (ran t es) → arm1 (sys h ps) i ≡ just t
    go eq1 with arm1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  flush-ran : ∀ {h ps i t es} →
    emitFlush (sys h ps) i ≡ just (ran t es) → flush1 (sys h ps) i ≡ just t
  flush-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitFlush (sys h ps) i ≡ just (ran t es) → flush1 (sys h ps) i ≡ just t
    go eq1 with flush1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  npeek-ran : ∀ {h ps i t es} →
    emitNpeek (sys h ps) i ≡ just (ran t es) → npeek1 (sys h ps) i ≡ just t
  npeek-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitNpeek (sys h ps) i ≡ just (ran t es) → npeek1 (sys h ps) i ≡ just t
    go eq1 with npeek1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  ndemon-ran : ∀ {h ps i t es} →
    emitNdemon (sys h ps) i ≡ just (ran t es) → ndemon1 (sys h ps) i ≡ just t
  ndemon-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitNdemon (sys h ps) i ≡ just (ran t es) → ndemon1 (sys h ps) i ≡ just t
    go eq1 with ndemon1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  seq-ran : ∀ {h ps i t es} →
    emitSeq (sys h ps) i ≡ just (ran t es) → seq1 (sys h ps) i ≡ just t
  seq-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitSeq (sys h ps) i ≡ just (ran t es) → seq1 (sys h ps) i ≡ just t
    go eq1 with seq1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  bind-ran : ∀ {h ps i t es} →
    emitBind (sys h ps) i ≡ just (ran t es) → bind1 (sys h ps) i ≡ just t
  bind-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitBind (sys h ps) i ≡ just (ran t es) → bind1 (sys h ps) i ≡ just t
    go eq1 with bind1 (sys h ps) i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _  = cong just (ran-sys eq1)

  -- `emitEmit` is `emitFromCtl` of `emitCtl`, and `emitFromCtl` keeps
  -- the system only when `peekSend` names the flight. Abstract both
  -- Maybes. Do not invert `emitCtl`.
  fromEmit : ∀ {i c t es} (m : Maybe Sys) →
    emitFromCtl i c m ≡ just (ran t es) → m ≡ just t
  fromEmit {i} {c} {t} {es} m eq = go m eq
    where
    go : (m : Maybe Sys) → emitFromCtl i c m ≡ just (ran t es) → m ≡ just t
    go m eq1 with m
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _ with peekSend c
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just (sent _ _ _) = cong just (ran-sys eq1)

  emit-ran : ∀ {h ps i t es} →
    emitEmit (sys h ps) i ≡ just (ran t es) → emit1 (sys h ps) i ≡ just t
  emit-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitEmit (sys h ps) i ≡ just (ran t es) → emit1 (sys h ps) i ≡ just t
    go eq1 with lookup ps i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just (proc _ _ _ _ c) = fromEmit (emitCtl h ps i c) eq1

  -- `emitRecv1` reads the inbox the step was given. Split that list so
  -- `recvFromStep` reduces, then abstract the step result.
  fromRecv : ∀ {i t es} (ib : List Msg) (m : Maybe Sys) →
    recvFromStep i ib m ≡ just (ran t es) → m ≡ just t
  fromRecv {i} {t} {es} ib m eq = go ib m eq
    where
    go : (ib : List Msg) (m : Maybe Sys) →
      recvFromStep i ib m ≡ just (ran t es) → m ≡ just t
    go ib m eq1 with m
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just _ with ib
    ... | [] = cong just (ran-sys eq1)
    ... | msg _ ∷ _ = cong just (ran-sys eq1)

  recv-ran : ∀ {h ps i t es} →
    emitRecv1 (sys h ps) i ≡ just (ran t es) → recv1 (sys h ps) i ≡ just t
  recv-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitRecv1 (sys h ps) i ≡ just (ran t es) → recv1 (sys h ps) i ≡ just t
    go eq1 with lookup ps i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just (proc pid st ro ib c) =
        fromRecv ib (recvStep h ps i (proc pid st ro ib c) c st ib) eq1

  -- `done1` still succeeds on `pstDone`. `emitDone1` refuses that, so
  -- the ready and waiting arms are the only ones that reach `doneStep`.
  done-ran : ∀ {h ps i t es} →
    emitDone1 (sys h ps) i ≡ just (ran t es) → done1 (sys h ps) i ≡ just t
  done-ran {h} {ps} {i} {t} {es} eq = go eq
    where
    go : emitDone1 (sys h ps) i ≡ just (ran t es) → done1 (sys h ps) i ≡ just t
    go eq1 with lookup ps i
    ... | nothing = ⊥-elim (nothing≢just eq1)
    ... | just (proc pid st ro ib c) with st
    ... | pstDone = ⊥-elim (nothing≢just eq1)
    ... | ready = end (doneStep h ps i (proc pid ready ro ib c) c) eq1
      where
      end : (m : Maybe Sys) →
        emitDone [] m ≡ just (ran t es) → m ≡ just t
      end m eq2 with m
      ... | nothing = ⊥-elim (nothing≢just eq2)
      ... | just _  = cong just (ran-sys eq2)
    ... | waiting = end (doneStep h ps i (proc pid waiting ro ib c) c) eq1
      where
      end : (m : Maybe Sys) →
        emitDone [] m ≡ just (ran t es) → m ≡ just t
      end m eq2 with m
      ... | nothing = ⊥-elim (nothing≢just eq2)
      ... | just _  = cong just (ran-sys eq2)

pop-pstep : ∀ {s p t es} → emitPop s p ≡ just (ran t es) → PStep s t
pop-pstep {sys h ps} {pop-spawn i} {t} {es} eq =
  p-spawn (spawn-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-emit i} {t} {es} eq =
  p-emit (emit-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-deliver i} {t} {es} eq =
  p-deliver (deliver-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-recv i} {t} {es} eq =
  p-recv (recv-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-await i} {t} {es} eq =
  p-await (await-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-arm i} {t} {es} eq =
  p-arm (arm-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-flush i} {t} {es} eq =
  p-flush (flush-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-npeek i} {t} {es} eq =
  p-npeek (npeek-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-ndemon i} {t} {es} eq =
  p-ndemon (ndemon-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-seq i} {t} {es} eq =
  p-seq (seq-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-bind i} {t} {es} eq =
  p-bind (bind-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-done i} {t} {es} eq =
  p-done (done-ran {h} {ps} {i} {t} {es} eq)
pop-pstep {sys h ps} {pop-eval i} {t} {es} eq =
  p-lift (step-eval (eval-ran {h} {ps} {i} {t} {es} eq))

------------------------------------------------------------------------
-- Round-robin, then a full scan so a missed pid is not a deadlock.
------------------------------------------------------------------------

modStep : ℕ → ℕ → ℕ
modStep m n = if m <ᵇ n then suc m else zero

modSuc : ℕ → ℕ → ℕ
modSuc _ zero = zero
modSuc zero (suc _) = zero
modSuc (suc c) (suc n) = modStep (modSuc c (suc n)) n

wrap : ℕ → ℕ → ℕ
wrap i zero = zero
wrap i (suc n) = modSuc i (suc n)

record Found (s : Sys) : Set where
  constructor found
  field
    pid : ℕ
    got : Hit s pid

open Found public

scan : ℕ → ℕ → ℕ → (s : Sys) → Maybe (Found s)
scan zero _ _ _ = nothing
scan (suc k) i n s with firstHit s i spine
... | just h  = just (found i h)
... | nothing = scan k (wrap (suc i) n) n s

pick : ℕ → Sys → Maybe (ℕ × Pop)
pick c s = picked (length (procs s))
  where
  picked : ℕ → Maybe (ℕ × Pop)
  picked n with scan n (modSuc c n) n s
  ... | nothing = nothing
  ... | just f  = just (pid f , popK (pid f) (kind (got f)))

range : ℕ → List ℕ
range zero = []
range (suc n) = range n ++ (n ∷ [])

scanHits : List ℕ → (s : Sys) → Maybe (Found s)
scanHits [] s = nothing
scanHits (i ∷ is) s = onHit (firstHit s i spine)
  where
  onHit : Maybe (Hit s i) → Maybe (Found s)
  onHit (just h) = just (found i h)
  onHit nothing = scanHits is s

-- Every pid, from 0. This is the deadlock test, not the cursor.
findHit : (s : Sys) → Maybe (Found s)
findHit s = scanHits (range (length (procs s))) s

data In (i : ℕ) : List ℕ → Set where
  here  : ∀ {j js} → i ≡ j → In i (j ∷ js)
  there : ∀ {j js} → In i js → In i (j ∷ js)

++-in-l : ∀ {i xs ys} → In i xs → In i (xs ++ ys)
++-in-l (here eq) = here eq
++-in-l (there m) = there (++-in-l m)

++-in-r : ∀ {i} xs {ys} → In i ys → In i (xs ++ ys)
++-in-r [] m = m
++-in-r (j ∷ js) m = there (++-in-r js m)

pred≤ : ∀ {m n} → suc m ≤ suc n → m ≤ n
pred≤ (s≤s le) = le

split≤ : ∀ {i n} → i ≤ n → suc i ≤ n ⊎ i ≡ n
split≤ {zero} {zero} z≤n = inj₂ refl
split≤ {zero} {suc n} z≤n = inj₁ (s≤s z≤n)
split≤ {suc i} {zero} ()
split≤ {suc i} {suc n} (s≤s le) with split≤ le
... | inj₁ lt = inj₁ (s≤s lt)
... | inj₂ eq = inj₂ (cong suc eq)

range-in : ∀ i n → suc i ≤ n → In i (range n)
range-in i zero ()
range-in i (suc n) (s≤s le) with split≤ le
... | inj₁ lt = ++-in-l (range-in i n lt)
... | inj₂ eq = ++-in-r (range n) (here eq)

scan-hit : ∀ {s i is h} →
  firstHit s i spine ≡ just h →
  scanHits (i ∷ is) s ≡ just (found i h)
scan-hit eq rewrite eq = refl

scan-skip : ∀ {s i is} →
  firstHit s i spine ≡ nothing →
  scanHits (i ∷ is) s ≡ scanHits is s
scan-skip eq rewrite eq = refl

mutual
  hits-rest : ∀ {s j js i} →
    firstHit s j spine ≡ nothing →
    scanHits (j ∷ js) s ≡ nothing →
    In i (j ∷ js) →
    firstHit s i spine ≡ nothing
  hits-rest eqF eq (here p) rewrite p = eqF
  hits-rest {s} {j} {js} {i} eqF eq (there m) =
    hits-none s js (trans (sym (scan-skip eqF)) eq) i m

  hits-none : ∀ s is →
    scanHits is s ≡ nothing → ∀ i → In i is → firstHit s i spine ≡ nothing
  hits-none s [] eq i ()
  hits-none s (j ∷ js) eq i mem with fh s j
  ... | fh-yes h eqH = ⊥-elim (just≢nothing (trans (sym (scan-hit eqH)) eq))
  ... | fh-no eqF    = hits-rest eqF eq mem

hit-off : ∀ s i → firstHit s i spine ≡ nothing → enabled s i ≡ nothing
hit-off s i eq rewrite eq = refl

live-none : ∀ s → findHit s ≡ nothing → ∀ i → suc i ≤ length (procs s) → enabled s i ≡ nothing
live-none s eq i lt =
  hit-off s i (hits-none s (range (length (procs s))) eq i (range-in i (length (procs s)) lt))

-- Deadlock is every pid refusing a wrapper, not a cursor that skipped one.
deadlock-real : ∀ s → findHit s ≡ nothing →
  ∀ i → suc i ≤ length (procs s) → ∀ {t} → ¬ At i s t
deadlock-real s eq i lt bad = enabled-blocked (live-none s eq i lt) bad

------------------------------------------------------------------------
-- Halt, stuck, and the carried value.
------------------------------------------------------------------------

allDone : List Proc → Bool
allDone [] = true
allDone (p ∷ ps) with state p
... | pstDone = allDone ps
... | ready   = false
... | waiting = false

allDone-map : ∀ ps → allDone (map clean ps) ≡ allDone ps
allDone-map [] = refl
allDone-map (p ∷ ps) with state p
... | pstDone = allDone-map ps
... | ready   = refl
... | waiting = refl

allDone-collect : ∀ s → allDone (procs s) ≡ true → allDone (procs (collect s)) ≡ true
allDone-collect s eq rewrite allDone-map (procs s) = eq

data Outcome (t : Sys) : Set where
  halted    : (pre : Sys) → allDone (procs pre) ≡ true → t ≡ collect pre → Outcome t
  deadlock  : (∀ i → suc i ≤ length (procs t) → ∀ {u} → ¬ At i t u) → Outcome t
  stuck     : ℕ → (∀ i → suc i ≤ length (procs t) → ∀ {u} → ¬ At i t u) → Outcome t
  outOfFuel : Outcome t

-- Final processes are `pstDone` when the outcome says so.
-- `clean` keeps the state, and halt collects.
procs-done : ∀ {t} → Outcome t → Set
procs-done {t} (halted pre eq col) = allDone (procs t) ≡ true
procs-done (deadlock _) = ⊤
procs-done (stuck _ _) = ⊤
procs-done outOfFuel = ⊤

procs-done-holds : ∀ {t} (o : Outcome t) → procs-done o
procs-done-holds {t} (halted pre eq col) rewrite col = allDone-collect pre eq
procs-done-holds (deadlock _) = tt
procs-done-holds (stuck _ _) = tt
procs-done-holds outOfFuel = tt

data Plain : Set where
  plain-halted plain-deadlock plain-fuel : Plain
  plain-stuck : ℕ → Plain

plain : ∀ {t} → Outcome t → Plain
plain (halted _ _ _) = plain-halted
plain (deadlock _) = plain-deadlock
plain (stuck i _) = plain-stuck i
plain outOfFuel = plain-fuel

bump : Maybe ℕ → Maybe ℕ
bump (just n) = just (suc n)
bump nothing = nothing

readNat : List Obj → ℕ → ℕ → Maybe ℕ
readNat _ zero _ = nothing
readNat h (suc f) ix with payloadAt h ix
... | just (nat n) = just n
... | just (suc↑ r) = bump (readNat h f (obj r))
... | just (clo _ _) = nothing
... | nothing = nothing

payloadNat : List Obj → Ref → Maybe ℕ
payloadNat h r = readNat h (suc (length h)) (obj r)

inboxNat : Sys → ℕ → Maybe ℕ
inboxNat (sys h ps) i with lookup ps i
... | nothing = nothing
... | just p with inbox p
... | [] = nothing
... | msg r ∷ _ = payloadNat h r

notePop : Sys → Pop → Maybe ℕ
notePop s (pop-recv i) = inboxNat s i
notePop _ _ = nothing

noteRv : Sys → Maybe ℕ
noteRv (sys h ps) with lookup ps zero
... | nothing = nothing
... | just p with ctl p
... | rv r _ [] = payloadNat h r
... | rv r _ (saved _ ∷ _) = payloadNat h r
... | _ = nothing

keep : Maybe ℕ → Maybe ℕ → Maybe ℕ
keep (just n) _ = just n
keep nothing v = v

------------------------------------------------------------------------
-- Meetings stay beside the system. `stepDone` and `observe` update
-- flags. The base is the process system again afterwards.
------------------------------------------------------------------------

align : Sys → Meet → Meet
align t m = record m { base = t }

alignAll : Sys → List Meet → List Meet
alignAll t ms = map (align t) ms

inboxEmpty : Sys → ℕ → Bool
inboxEmpty (sys _ ps) i with lookup ps i
... | nothing = true
... | just p with inbox p
... | [] = true
... | _ ∷ _ = false

useful : Meet → Meet → List Event → Bool
useful m m1 es with es
... | _ ∷ _ = true
... | [] with noted m
... | true = false
... | false with noted m1
... | true = true
... | false = false

onDone : Sys → ℕ → Meet → Meet
onDone t i m with stepDone (record m { base = t }) i
... | nothing = record m { base = t }
... | just m1 = record m1 { base = t }

observeRecv : Sys → ℕ → Meet → Meet × List Event
observeRecv t i m with i ≡ᵇ observer m
... | false = m , []
... | true with inboxEmpty t i
... | false = m , []
... | true with observe m
... | nothing = m , []
... | just (dran m1 es) with useful m m1 es
... | false = m , []
... | true = record m1 { base = t } , es

react : Sys → Pop → Meet → Meet × List Event
react t (pop-spawn _) m = align t m , []
react t (pop-emit _) m = align t m , []
react t (pop-deliver _) m = align t m , []
react t (pop-recv i) m = observeRecv t i (align t m)
react t (pop-await _) m = align t m , []
react t (pop-arm _) m = align t m , []
react t (pop-flush _) m = align t m , []
react t (pop-npeek _) m = align t m , []
react t (pop-ndemon _) m = align t m , []
react t (pop-seq _) m = align t m , []
react t (pop-bind _) m = align t m , []
react t (pop-done i) m = onDone t i m , []
react t (pop-eval _) m = align t m , []

settle : Sys → Pop → List Meet → List Meet × List Event
settle t p [] = [] , []
settle t p (m ∷ ms) =
  let m1 , e1 = react t p m
      ms1 , e2 = settle t p ms
  in (m1 ∷ ms1) , (e1 ++ e2)

look : Sys → Meet → Maybe (Meet × List Event)
look s m with inboxEmpty s (observer m)
... | false = nothing
... | true with observe (record m { base = s })
... | nothing = nothing
... | just (dran m1 es) with useful m m1 es
... | false = nothing
... | true = just (record m1 { base = s } , es)

pending : Sys → List Meet → Maybe (List Meet × List Event)
pending s [] = nothing
pending s (m ∷ ms) with look s m
... | just (m1 , es) = just (m1 ∷ alignAll s ms , es)
... | nothing with pending s ms
... | nothing = nothing
... | just (ms1 , es) = just (align s m ∷ ms1 , es)

refusing : Proc → Bool
refusing p with state p
... | waiting = false
... | pstDone = false
... | ready with ctl p
... | idle = false
... | ev _ _ _ = true
... | rv _ _ _ = true
... | pr _ = true

firstRefuse : List Proc → ℕ → Maybe ℕ
firstRefuse [] _ = nothing
firstRefuse (p ∷ ps) i with refusing p
... | true = just i
... | false = firstRefuse ps (suc i)

------------------------------------------------------------------------
-- The run. Fuel is the decreasing argument.
------------------------------------------------------------------------

record Drove : Set where
  constructor drv
  field
    final : Sys
    oc    : Outcome final
    evs   : List Event
    meets : List Meet
    val   : Maybe ℕ

open Drove public

Drive : Sys → Set
Drive s = Σ Drove (λ d → PStep* s (final d))

consE : ∀ {s} → List Event → Drive s → Drive s
consE es (d , tr) = record d { evs = es ++ evs d } , tr

prepend : ∀ {s t} → PStep s t → Drive t → Drive s
prepend st (d , tr) = d , pmore st tr

-- Case on the wrapper here. `same` does not reduce on a variable,
-- and inside `drive`'s `where` the two sides are not the same term.
stepOf : ∀ {s i t es} (k : K) →
  emitK s i k ≡ just (ran t es) → PStep s t
stepOf {sys h ps} {i} k-deliver eq = pop-pstep {sys h ps} {pop-deliver i} eq
stepOf {sys h ps} {i} k-seq     eq = pop-pstep {sys h ps} {pop-seq i} eq
stepOf {sys h ps} {i} k-bind    eq = pop-pstep {sys h ps} {pop-bind i} eq
stepOf {sys h ps} {i} k-spawn   eq = pop-pstep {sys h ps} {pop-spawn i} eq
stepOf {sys h ps} {i} k-emit    eq = pop-pstep {sys h ps} {pop-emit i} eq
stepOf {sys h ps} {i} k-await   eq = pop-pstep {sys h ps} {pop-await i} eq
stepOf {sys h ps} {i} k-arm     eq = pop-pstep {sys h ps} {pop-arm i} eq
stepOf {sys h ps} {i} k-flush   eq = pop-pstep {sys h ps} {pop-flush i} eq
stepOf {sys h ps} {i} k-npeek   eq = pop-pstep {sys h ps} {pop-npeek i} eq
stepOf {sys h ps} {i} k-ndemon  eq = pop-pstep {sys h ps} {pop-ndemon i} eq
stepOf {sys h ps} {i} k-recv    eq = pop-pstep {sys h ps} {pop-recv i} eq
stepOf {sys h ps} {i} k-done    eq = pop-pstep {sys h ps} {pop-done i} eq
stepOf {sys h ps} {i} k-eval    eq = pop-pstep {sys h ps} {pop-eval i} eq

haltOf : List Meet → Maybe ℕ → (s : Sys) → allDone (procs s) ≡ true → Drive s
haltOf ms v s eq =
  let t = collect s
  in drv t (halted s eq refl)
       (tr-collect (freedIdx (markVec s) zero) ∷ [])
       (alignAll t ms) v
     , pmore (p-lift step-collect) pdone

drive : ℕ → ℕ → List Meet → Maybe ℕ → (s : Sys) → Drive s
drive zero c ms v s = drv s outOfFuel [] (alignAll s ms) v , pdone
drive (suc fuel) c ms v s with allDone (procs s) in eq
... | true  = haltOf ms v s eq
... | false = go
  where
  n = length (procs s)

  classify : findHit s ≡ nothing → Outcome s
  classify eq with firstRefuse (procs s) zero
  ... | just i = stuck i (deadlock-real s eq)
  ... | nothing = deadlock (deadlock-real s eq)

  use : ∀ {i} → Hit s i → Drive s
  use {i} (hit k (ran t es) eq) = after (settle t (popK i k) ms)
    where
    st = stepOf k eq
    v1 = keep (keep v (notePop s (popK i k))) (noteRv t)
    after : List Meet × List Event → Drive s
    after (ms1 , extra) = consE (es ++ extra) (prepend st (drive fuel (suc i) ms1 v1 t))

  stop : findHit s ≡ nothing → Drive s
  stop eq with pending s ms
  ... | just (ms1 , extra) = consE extra (drive fuel c ms1 v s)
  ... | nothing = drv s (classify eq) [] (alignAll s ms) (keep v (noteRv s)) , pdone

  fallback : Drive s
  fallback with findHit s in eq
  ... | just f   = use (got f)
  ... | nothing  = stop eq

  go : Drive s
  go with scan n (modSuc c n) n s
  ... | just f = use (got f)
  ... | nothing = fallback

-- `drive` returns `Drive s`: the final `Drove` paired with a `PStep*`
-- from the start to `final`. `drive-sound` is that second component,
-- transported along `final d ≡ t`. It does not rebuild the trace.
-- The content is the steps `drive` constructs: `use` prepends the
-- wrapper step, `haltOf` prepends `step-collect`, and a meeting
-- update prepends nothing.
drive-sound : ∀ {n c ms v s t} {o : Outcome t} {es ms' v'} →
  proj₁ (drive n c ms v s) ≡ drv t o es ms' v' → PStep* s t
drive-sound {n} {c} {ms} {v} {s} eq =
  subst (PStep* s) (final-eq eq) (proj₂ (drive n c ms v s))
  where
  final-eq : ∀ {d t} {o : Outcome t} {es ms' v'} →
    d ≡ drv t o es ms' v' → final d ≡ t
  final-eq refl = refl
