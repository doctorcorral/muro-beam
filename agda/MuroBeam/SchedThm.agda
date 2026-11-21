------------------------------------------------------------------------
-- What a driven run preserves.
--
-- `drive-sound` in `MuroBeam.Sched` projects the `PStep*` that `drive`
-- packages with the final system. It does not rebuild the trace.
-- There is no bounded-wait fact. `AllInv` is `residual-inv-refs`,
-- which holds of every system, so it is not a property of `drive`
-- and it is not stated here. `no-stray-reply` needs `ReplyDone` at
-- the start. Heap emptiness is `done-collect-empty` when `drive`
-- returns `halted` and `liveRefs` of that pre-collect system are
-- empty. It is not a consequence of the word halted alone.
--
-- `emit1` returning a system is not proved to be `emitEmit` returning
-- that system. `At` is the wrapper that succeeded. A `done1` of a
-- process that is already `pstDone` is not an `At` step. `¬ At` is
-- not `¬ PStep`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.SchedThm where

open import Data.Bool.Base using (false; true)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List; _∷_) renaming ([] to nil)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Vec.Base using ([])
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; subst; cong)

open import Muro.Base using (ok)
open import Muro.Grade using (g0; g1)

open import MuroBeam.Adequacy using (AllFree; done-collect-empty)
open import MuroBeam.Collect using (collect)
open import MuroBeam.Grade using (selfKept)
open import MuroBeam.Heap using (Obj; cell; nat; suc↑; live; Ref; ref; count)
open import MuroBeam.Process using
  ( Sys; sys; heap; proc; ready; idle; pr; procs; refsOf; liveRefs; msg )
  renaming (done to pstDone)
open import MuroBeam.PRun using (mailHas; deadAt)
open import MuroBeam.PSyntax using (PTm; t[]; done; spawn; recv; send; go)
open import MuroBeam.PTm using
  ( CheckedP; checkedP; checkP; lowerP
  ; spawnAwait; spawnAwait-ok; spawnIgnore; spawnIgnore-ok
  ; spawnNignore; spawnNignore-ok )
open import MuroBeam.PWf using (psteps)
open import MuroBeam.RunImage using (imgFuel)
open import MuroBeam.Sched using
  ( drive; final; oc; val; plain; plain-halted; plain-deadlock; plain-stuck
  ; halted; allDone; drive-fuel )
open import MuroBeam.Show using (showDrove)
open import MuroBeam.Stray using (ReplyDone; replied; no-stray-reply)
open import MuroBeam.Unique using (WF)

------------------------------------------------------------------------
-- Safety along the trace `drive` builds.
------------------------------------------------------------------------

drive-wf : ∀ {n c ms v s} →
  WF s → WF (final (proj₁ (drive n c ms v s)))
drive-wf {n} {c} {ms} {v} {s} wf =
  psteps (proj₂ (drive n c ms v s)) wf

drive-stray : ∀ {n c ms v s i τ} →
  ReplyDone s i τ →
  mailHas (procs (final (proj₁ (drive n c ms v s)))) i τ ≡ false
drive-stray {n} {c} {ms} {v} {s} d =
  no-stray-reply (proj₂ (drive n c ms v s)) d

-- `halted pre doneEq col` is the outcome `drive` returned. `col` is
-- `final ≡ collect pre`. Emptiness is the pre-state's live refs, not
-- a fact the word halted has on its own.
halted-empty :
  ∀ {n c ms v s pre}
    {doneEq : allDone (procs pre) ≡ true}
    {col : final (proj₁ (drive n c ms v s)) ≡ collect pre} →
    oc (proj₁ (drive n c ms v s)) ≡ halted pre doneEq col →
    liveRefs pre ≡ nil →
    AllFree (heap (final (proj₁ (drive n c ms v s))))
-- `col` is the equality stored in the `halted` outcome. Matching that
-- outcome does not compute: `oc (proj₁ (drive …))` stays stuck, and
-- `rewrite` then ill-types the outcome equality. `subst` moves
-- emptiness from `collect pre` onto `final`.
halted-empty {pre = pre} {col = col} _ emp =
  subst (λ t → AllFree (heap t)) (sym col) (done-collect-empty pre emp)

------------------------------------------------------------------------
-- Closed programs. `checkP` accepts spawn of `done`, `lowerP` is that
-- one process, and `drive` halts. The deadlock is a ready `recv` on
-- an empty inbox: it parks, then nothing is enabled. The stuck
-- program is a `send` whose environment is empty.
------------------------------------------------------------------------

driveFuel : ℕ
driveFuel =
  suc (suc (suc (suc
  (suc (suc (suc (suc
  (suc (suc (suc (suc
  (suc (suc (suc (suc zero)))))))))))))))

twoTm : PTm zero
twoTm = spawn t[] done done

twoOk : checkP [] twoTm ≡ ok []
twoOk = refl

twoP : CheckedP
twoP = checkedP twoTm twoOk

twoSys : Sys
twoSys = sys nil (proc zero ready nil nil (pr (go twoTm nil nil nil nil)) ∷ nil)

two-lower : lowerP twoP ≡ twoSys
two-lower = refl

two-halted :
  plain (oc (proj₁ (drive driveFuel zero nil nothing (lowerP twoP))))
    ≡ plain-halted
two-halted = refl

threeTm : PTm zero
threeTm = spawn t[] done (spawn t[] done done)

threeOk : checkP [] threeTm ≡ ok []
threeOk = refl

threeP : CheckedP
threeP = checkedP threeTm threeOk

three-halted :
  plain (oc (proj₁ (drive driveFuel zero nil nothing (lowerP threeP))))
    ≡ plain-halted
three-halted = refl

-- Regression pins for three closed schedules at `driveFuel`.
-- `*-halted` pins the outcome, `*-val` pins the kept nat, and
-- `*-line` pins the `showDrove` text. Each one is `refl` on that
-- program. None of them is a theorem about an arbitrary image.
-- `await-img`, `ignore-img`, and `nignore-img` are the fuel bridge:
-- the same `showDrove` line at `imgFuel`. The content pins are the
-- `*-line` equations.
--
-- Closed `refl` pins for `spawnAwait` at `driveFuel`. They do not
-- prove the regrade, the move, or the await. `bind-spawn-tag` in
-- `MuroBeam.PRun` is the step from a promoting `bind1` to the tagged
-- parent, and it still assumes the tail of the environment splits.
-- These pins do not discharge that assumption. The kept nat on this
-- program is zero, the cell the child was given.
awaitP : CheckedP
awaitP = checkedP spawnAwait spawnAwait-ok

await-halted :
  plain (oc (proj₁ (drive driveFuel zero nil nothing (lowerP awaitP))))
    ≡ plain-halted
await-halted = refl

await-val :
  val (proj₁ (drive driveFuel zero nil nothing (lowerP awaitP)))
    ≡ just zero
await-val = refl

-- The same program with `ignore` in place of `await`. This pin is
-- `refl` too. It does not prove `arm1` or `flush1`. The kept nat is
-- still the seq payload.
ignoreP : CheckedP
ignoreP = checkedP spawnIgnore spawnIgnore-ok

ignore-halted :
  plain (oc (proj₁ (drive driveFuel zero nil nothing (lowerP ignoreP))))
    ≡ plain-halted
ignore-halted = refl

ignore-val :
  val (proj₁ (drive driveFuel zero nil nothing (lowerP ignoreP)))
    ≡ just zero
ignore-val = refl

-- The printed line is `showDrove`. No newline: the Haskell main adds one.
-- Both runs move the fresh cell and collect every index.
await-line :
  showDrove (proj₁ (drive driveFuel zero nil nothing (lowerP awaitP)))
    ≡ "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) Kmove, tr-collect(0 1 2 3)] h4l0p2 v0"
await-line = refl

ignore-line :
  showDrove (proj₁ (drive driveFuel zero nil nothing (lowerP ignoreP)))
    ≡ "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) Kmove, tr-collect(0 1 2 3)] h4l0p2 v0"
ignore-line = refl

-- `imgFuel` is 1000. A halted run at `driveFuel` is the same Drove there.
fuel-≤ : driveFuel ≤ imgFuel
fuel-≤ =
  s≤s (s≤s (s≤s (s≤s
  (s≤s (s≤s (s≤s (s≤s
  (s≤s (s≤s (s≤s (s≤s
  (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))

await-fuel :
  proj₁ (drive imgFuel zero nil nothing (lowerP awaitP))
    ≡ proj₁ (drive driveFuel zero nil nothing (lowerP awaitP))
await-fuel =
  drive-fuel driveFuel imgFuel zero nil nothing (lowerP awaitP) fuel-≤ await-halted

-- Fuel bridge to `await-line`. The content pin is `await-line`.
await-img : showDrove (proj₁ (drive imgFuel zero nil nothing (lowerP awaitP)))
          ≡ showDrove (proj₁ (drive driveFuel zero nil nothing (lowerP awaitP)))
await-img = cong showDrove await-fuel

ignore-fuel :
  proj₁ (drive imgFuel zero nil nothing (lowerP ignoreP))
    ≡ proj₁ (drive driveFuel zero nil nothing (lowerP ignoreP))
ignore-fuel =
  drive-fuel driveFuel imgFuel zero nil nothing (lowerP ignoreP) fuel-≤ ignore-halted

-- Fuel bridge to `ignore-line`. The content pin is `ignore-line`.
ignore-img : showDrove (proj₁ (drive imgFuel zero nil nothing (lowerP ignoreP)))
           ≡ showDrove (proj₁ (drive driveFuel zero nil nothing (lowerP ignoreP)))
ignore-img = cong showDrove ignore-fuel

-- Spawn parent `nignore`. The reply is not flushed, so the fingerprint
-- is not the await line. Halting at 16 is the same fact as the other
-- two replies.
nignoreP : CheckedP
nignoreP = checkedP spawnNignore spawnNignore-ok

nignore-halted :
  plain (oc (proj₁ (drive driveFuel zero nil nothing (lowerP nignoreP))))
    ≡ plain-halted
nignore-halted = refl

nignore-val :
  val (proj₁ (drive driveFuel zero nil nothing (lowerP nignoreP)))
    ≡ just zero
nignore-val = refl

nignore-fuel :
  proj₁ (drive imgFuel zero nil nothing (lowerP nignoreP))
    ≡ proj₁ (drive driveFuel zero nil nothing (lowerP nignoreP))
nignore-fuel =
  drive-fuel driveFuel imgFuel zero nil nothing (lowerP nignoreP) fuel-≤ nignore-halted

nignore-line :
  showDrove (proj₁ (drive driveFuel zero nil nothing (lowerP nignoreP)))
    ≡ "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) Kmove, tr-collect(1 2)] h3l1p2 v0"
nignore-line = refl

-- Fuel bridge to `nignore-line`. The content pin is `nignore-line`.
nignore-img : showDrove (proj₁ (drive imgFuel zero nil nothing (lowerP nignoreP)))
            ≡ showDrove (proj₁ (drive driveFuel zero nil nothing (lowerP nignoreP)))
nignore-img = cong showDrove nignore-fuel

deadTm : PTm zero
deadTm = recv g1 g0 (done {suc zero})

deadSys : Sys
deadSys =
  sys nil
    (proc zero ready nil nil (pr (go deadTm nil nil nil nil)) ∷ nil)

dead-lock :
  plain (oc (proj₁ (drive driveFuel zero nil nothing deadSys)))
    ≡ plain-deadlock
dead-lock = refl

stuckTm : PTm (suc zero)
stuckTm = send zero (fzero {zero}) (done {suc zero})

stuckSys : Sys
stuckSys =
  sys nil
    (proc zero ready nil nil (pr (go stuckTm nil nil nil nil)) ∷ nil)

stuck-at :
  plain (oc (proj₁ (drive driveFuel zero nil nothing stuckSys)))
    ≡ plain-stuck zero
stuck-at = refl

------------------------------------------------------------------------
-- A delivered `suc↑` is one more than the nat it points at. The book
-- `readNat` must apply the same bump, or this value disagrees.
------------------------------------------------------------------------

up0 : Ref
up0 = ref zero g0 g0 (selfKept g0)

up1 : Ref
up1 = ref (suc zero) g0 g0 (selfKept g0)

upH : List Obj
upH = cell (nat zero) live ∷ cell (suc↑ up0) live ∷ nil

upSys : Sys
upSys =
  sys upH
    (proc zero ready nil (msg up1 ∷ nil)
      (pr (go (recv g0 g0 (done {suc zero})) nil nil nil nil))
    ∷ nil)

up-val :
  val (proj₁ (drive driveFuel zero nil nothing upSys)) ≡ just (suc zero)
up-val = refl

------------------------------------------------------------------------
-- ReplyDone, then a step that can still deliver a different object.
-- Tag 0 is dead and unreferenced. The child holds a g0 placeholder,
-- so it cannot emit, and its ether is empty, so it cannot deliver.
-- `mailHas` of tag 0 stays false. That is `drive-stray` on this run.
------------------------------------------------------------------------

ph1 : Ref
ph1 = ref (suc zero) g0 g0 (selfKept g0)

strayH : List Obj
strayH = cell (nat zero) live ∷ cell (nat zero) live ∷ nil

straySys : Sys
straySys =
  sys strayH
    ( proc zero ready nil nil
        (pr (go (done {zero}) nil nil (zero ∷ nil) nil))
    ∷ proc (suc zero) ready nil nil
        (pr (go (send zero (fzero {zero}) (done {suc zero}))
              (ph1 ∷ nil) nil nil nil))
    ∷ nil)

stray-done : ReplyDone straySys zero zero
stray-done = replied refl (s≤s z≤n) refl

stray-clear :
  mailHas (procs (final (proj₁ (drive driveFuel zero nil nothing straySys)))) zero zero
    ≡ false
stray-clear = drive-stray {driveFuel} {zero} {nil} {nothing} stray-done

------------------------------------------------------------------------
-- Halt of a system whose live refs are already empty. The orphan cell
-- is freed. `empty-halt` names the `halted` outcome `drive` returns.
------------------------------------------------------------------------

emptyH : List Obj
emptyH = cell (nat zero) live ∷ nil

emptySys : Sys
emptySys = sys emptyH (proc zero pstDone nil nil idle ∷ nil)

empty-live : liveRefs emptySys ≡ nil
empty-live = refl

empty-halt :
  oc (proj₁ (drive driveFuel zero nil nothing emptySys))
    ≡ halted emptySys refl refl
empty-halt = refl

empty-free :
  AllFree (heap (final (proj₁ (drive driveFuel zero nil nothing emptySys))))
empty-free =
  halted-empty {n = driveFuel} {c = zero} {ms = nil} {v = nothing}
    {s = emptySys} {pre = emptySys} empty-halt empty-live
