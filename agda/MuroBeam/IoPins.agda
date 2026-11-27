------------------------------------------------------------------------
-- B4a closed pins for the console images.
--
-- Each string is the text of one `examples/images/out-*.mbi` file,
-- trailing newline included. Agda does not open the files.
-- `ioImage` is `loadIO`, then `drive` at `imgFuel` on `lowerIO`, then
-- the console lines and the `showDrove` summary: the same text
-- `muro-beam` prints after its tag line. The pins are `refl`, so a
-- change to `loadIO`, `lowerIO`, the scheduler, or the printer that
-- moves one of these lines fails `make agda`, not only the GHC jobs.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.IoPins where

open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import MuroBeam.RunImage using (ioImage; droveImage)

-- `send 1 0` of an ω `seq` slot: `emit1` with `Kcopy`, then `deliver1`
-- into the console. One output line, then `halted`. The console is
-- the second process (`p2`), and its message keeps the cell live.
outoneSrc : String
outoneSrc =
  "(muro-beam-image 3 (boundary 1) (entry (seq (gsu (gsu gze)) (send 1 0 (done)))))\n"

outone-io : ioImage outoneSrc ≡
  "2\nhalted [tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-send 0 1 ref(2,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h3l3p2 v2"
outone-io = refl

-- Two sends, in program order. The inbox is delivery order, so the
-- lines are `0` then `1`.
outtwoSrc : String
outtwoSrc =
  "(muro-beam-image 3 (boundary 1) (entry (seq gze (seq (gsu gze) (send 1 1 (send 1 0 (done)))))))\n"

outtwo-io : ioImage outtwoSrc ≡
  "0\n1\nhalted [tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-send 0 1 ref(0,pt(inf),pt(inf),omega-kept) Kcopy, tr-send 0 1 ref(2,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h3l3p2 v0"
outtwo-io = refl

-- Format 3 with a `(defs …)` section: `plus 2 3` written to the console.
outplusSrc : String
outplusSrc =
  "(muro-beam-image 3 (boundary 1) (defs (glam ((iv 0 1) 0) (glam ((iv 0 1) 0) (gmatch (gvar 1) (gvar 0) (gsu (gapp (gapp (gref 0) (gvar 0)) (gvar 1))))))) (entry (seq (gapp (gapp (gref 0) (gsu (gsu gze))) (gsu (gsu (gsu gze)))) (send 1 0 (done)))))\n"

outplus-io : ioImage outplusSrc ≡
  "5\nhalted [tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-send 0 1 ref(16,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect(0 1 2 3 4 9 10 11 12 13 14)] h17l6p2 v5"
outplus-io = refl

-- A spawned child writes. The console is pid 1, so the child is pid 2
-- (`tr-spawn 0 2`) and the send is `tr-send 2 1`.
outchildSrc : String
outchildSrc =
  "(muro-beam-image 3 (boundary 1) (entry (seq (gsu gze) (spawn (keep t[]) (send 1 0 (done)) (done)))))\n"

outchild-io : ioImage outchildSrc ≡
  "1\nhalted [tr-step 0, tr-step 0, tr-step 0, tr-spawn 0 2, tr-send 2 1 ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect(2)] h3l2p3 v1"
outchild-io = refl

-- The child sends to pid 0. pid 0 receives (`recv (w 0)`) and writes
-- the received value to the console.
outrelaySrc : String
outrelaySrc =
  "(muro-beam-image 3 (boundary 1) (entry (seq (gsu (gsu (gsu gze))) (spawn (keep t[]) (send 0 0 (done)) (recv (w 0) (send 1 0 (done)))))))\n"

outrelay-io : ioImage outrelaySrc ≡
  "3\nhalted [tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-spawn 0 2, tr-send 2 0 ref(3,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(3,pt(inf),pt(inf),omega-kept), tr-send 0 1 ref(3,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect(4)] h5l4p3 v3"
outrelay-io = refl

-- A constructor value prints as `con <tag>`.
outconSrc : String
outconSrc =
  "(muro-beam-image 3 (boundary 1) (entry (seq (gcon 1 gze) (send 1 0 (done)))))\n"

outcon-io : ioImage outconSrc ≡
  "con 1\nhalted [tr-step 0, tr-step 0, tr-step 0, tr-send 0 1 ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h2l2p2 v-"
outcon-io = refl

-- A closure prints as `closure`.
outcloSrc : String
outcloSrc =
  "(muro-beam-image 3 (boundary 1) (entry (seq (glam (w 0) (gvar 0)) (send 1 0 (done)))))\n"

outclo-io : ioImage outcloSrc ≡
  "closure\nhalted [tr-step 0, tr-send 0 1 ref(0,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h1l1p2 v-"
outclo-io = refl

-- A format-3 pure entry `(seq e (done))`: no write, no output line,
-- the same `stuck 0` as format 1, with the console as `p2`.
outnoneSrc : String
outnoneSrc =
  "(muro-beam-image 3 (boundary 1) (entry (seq (gsu gze) (done))))\n"

outnone-io : ioImage outnoneSrc ≡
  "stuck 0 [tr-step 0, tr-step 0, tr-step 0] h2l2p2 v1"
outnone-io = refl

-- The same send in a format-1 image. There is no pid 1, so `emit1`
-- is `blocked` and pid 0 stops `stuck`. No output line: the console
-- is opt-in.
outv1Src : String
outv1Src =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gsu gze) (send 1 0 (done)))))\n"

outv1-io : ioImage outv1Src ≡
  "stuck 0 [tr-step 0, tr-step 0, tr-step 0] h2l2p1 v1"
outv1-io = refl

-- The console is output only. Nothing sends to pid 0, so a `recv`
-- entry parks and the schedule is a `deadlock`.
outrecvSrc : String
outrecvSrc =
  "(muro-beam-image 3 (boundary 1) (entry (recv (w 0) (done))))\n"

outrecv-io : ioImage outrecvSrc ≡
  "deadlock [] h0l0p2 v-"
outrecv-io = refl

-- A spawn reply sent to the console instead of the parent. `checkP`
-- accepts it: the child's send is one use of the moved slot, and
-- pids are not checked. The console takes the `Kmove` reply and
-- prints it. The parent's `await` never sees the tag, so the run is
-- a `deadlock`.
outreplySrc : String
outreplySrc =
  "(muro-beam-image 3 (boundary 1) (entry (seq gze (spawn (keep t[]) (send 1 0 (done)) (await 0 (done))))))\n"

outreply-io : ioImage outreplySrc ≡
  "0\ndeadlock [tr-step 0, tr-spawn 0 2, tr-send 2 1 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) Kmove] h3l3p3 v0"
outreply-io = refl

-- Format 1 is not the console layout: `ioImage` of the format-1 file
-- is the pre-B4 `droveImage` line.
outv1-drove : ioImage outv1Src ≡ droveImage outv1Src
outv1-drove = refl
