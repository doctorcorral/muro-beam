------------------------------------------------------------------------
-- What a driven run preserves.
--
-- `drive-sound` in `MuroBeam.Sched` is the `PStep*` to the final
-- system. These lemmas read that trace. There is no bounded-wait
-- fact. `AllInv` is `residual-inv-refs`, which holds of every system.
-- `no-stray-reply` needs `ReplyDone` at the start. Heap emptiness
-- needs `liveRefs` of the pre-collect system to be empty.
--
-- `emit1` returning a system is not proved to be `emitEmit` returning
-- that system. `At` is the wrapper that succeeded. A `done1` of a
-- process that is already `pstDone` is not an `At` step.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.SchedThm where

open import Data.Bool.Base using (false)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List; _∷_) renaming ([] to nil)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Vec.Base using ([])
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (ok)
open import Muro.Grade using (g0; g1)

open import MuroBeam.Adequacy using (AllFree; done-collect-empty)
open import MuroBeam.Collect using (collect)
open import MuroBeam.Process using
  ( Sys; sys; heap; proc; ready; pr; procs; refsOf; AllInv
  ; residual-inv-refs; liveRefs )
open import MuroBeam.PRun using (mailHas)
open import MuroBeam.PSyntax using (PTm; t[]; done; spawn; recv; send; go)
open import MuroBeam.PTm using (CheckedP; checkedP; checkP; lowerP)
open import MuroBeam.PWf using (psteps)
open import MuroBeam.Sched using
  ( drive; final; oc; plain; plain-halted; plain-deadlock; plain-stuck )
open import MuroBeam.Stray using (ReplyDone; no-stray-reply)
open import MuroBeam.Unique using (WF)

------------------------------------------------------------------------
-- Safety along the trace `drive` builds.
------------------------------------------------------------------------

drive-wf : ∀ {n c ms v s} →
  WF s → WF (final (proj₁ (drive n c ms v s)))
drive-wf {n} {c} {ms} {v} {s} wf =
  psteps (proj₂ (drive n c ms v s)) wf

drive-inv : ∀ {n c ms v s} →
  AllInv (refsOf (final (proj₁ (drive n c ms v s))))
drive-inv {n} {c} {ms} {v} {s} =
  residual-inv-refs (final (proj₁ (drive n c ms v s)))

drive-stray : ∀ {n c ms v s i τ} →
  ReplyDone s i τ →
  mailHas (procs (final (proj₁ (drive n c ms v s)))) i τ ≡ false
drive-stray {n} {c} {ms} {v} {s} d =
  no-stray-reply (proj₂ (drive n c ms v s)) d

halted-empty : ∀ {pre t} →
  t ≡ collect pre → liveRefs pre ≡ nil → AllFree (heap t)
halted-empty {pre} col emp rewrite col = done-collect-empty pre emp

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
