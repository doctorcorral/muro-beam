------------------------------------------------------------------------
-- B4b closed pins for the input images.
--
-- Each `…Src` is the text of one `examples/images/in-*.mbi` file and
-- each `…In` the text of one `examples/images/in-*.in` file, trailing
-- newlines included. Agda does not open the files. `ioImageIn` is
-- `loadIO`, the port gate, `readInput`, then `drive` at `imgFuel` on
-- `lowerIn`, then the console lines and the `showDrove` summary: the
-- text `muro-beam IMAGE --input FILE` prints after its tag line.
-- The input port is pid 2, so its steps are `tr-step 2` and its sends
-- `tr-send 2 0`. The pins are `refl`, so a change to the port, the
-- reader, the scheduler, or the printer that moves a line fails
-- `make agda`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.InPins where

open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import MuroBeam.RunImage using (ioImage; ioImageIn)

inechoSrc : String
inechoSrc =
  "(muro-beam-image 4 (boundary 1) (entry (recv (w 0) (send 1 0 (done)))))\n"

intwoSrc : String
intwoSrc =
  "(muro-beam-image 4 (boundary 1) (entry (recv (w 0) (recv (w 0) (send 1 1 (send 1 0 (done)))))))\n"

insuccSrc : String
insuccSrc =
  "(muro-beam-image 4 (boundary 1) (entry (recv (w 0) (seq (gsu (gvar 0)) (send 1 0 (done))))))\n"

inpredSrc : String
inpredSrc =
  "(muro-beam-image 4 (boundary 1) (entry (recv (w 0) (seq (gmatch (gvar 0) gze (gvar 0)) (send 1 0 (done))))))\n"

inshortSrc : String
inshortSrc =
  "(muro-beam-image 4 (boundary 1) (entry (recv (w 0) (send 1 0 (recv (w 0) (send 1 0 (done)))))))\n"

inchildSrc : String
inchildSrc =
  "(muro-beam-image 4 (boundary 1) (entry (seq (gsu gze) (spawn (keep t[]) (send 1 0 (done)) (recv (w 0) (send 1 0 (done)))))))\n"

innoneSrc : String
innoneSrc =
  "(muro-beam-image 4 (boundary 1) (entry (seq (gsu gze) (send 1 0 (done)))))\n"

inv3Src : String
inv3Src =
  "(muro-beam-image 3 (boundary 1) (entry (recv (w 0) (send 1 0 (done)))))\n"

inechoIn : String
inechoIn =
  "7\n"

intwoIn : String
intwoIn =
  "3 5\n"

insuccIn : String
insuccIn =
  "4\n"

inpredIn : String
inpredIn =
  "3\n"

inshortIn : String
inshortIn =
  "4\n"

inextraIn : String
inextraIn =
  "1 2\n"

inchildIn : String
inchildIn =
  "9\n"

inv3In : String
inv3In =
  "7\n"

inbadIn : String
inbadIn =
  "7 x\n"

-- One value. The port evaluates `7` (15 steps of pid 2), sends it to
-- pid 0 (`Kcopy`), pid 0 receives it and writes it to the console.
inecho-io : ioImageIn inechoSrc inechoIn ≡
  "7\nhalted [tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(7,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(7,pt(inf),pt(inf),omega-kept), tr-send 0 1 ref(7,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h8l8p3 v7"
inecho-io = refl

-- Two values, in the order the host read them. pid 0 writes the
-- first one received (slot 1) first.
intwo-io : ioImageIn intwoSrc intwoIn ≡
  "3\n5\nhalted [tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(3,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(3,pt(inf),pt(inf),omega-kept), tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(9,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(9,pt(inf),pt(inf),omega-kept), tr-send 0 1 ref(3,pt(inf),pt(inf),omega-kept) Kcopy, tr-send 0 1 ref(9,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h10l10p3 v3"
intwo-io = refl

-- The received value is a nat: `gsu` of it is computed on pid 0.
insucc-io : ioImageIn insuccSrc insuccIn ≡
  "5\nhalted [tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(4,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(4,pt(inf),pt(inf),omega-kept), tr-step 0, tr-step 0, tr-step 0, tr-send 0 1 ref(5,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h6l6p3 v4"
insucc-io = refl

-- `gmatch` on the received value: the predecessor of `3`.
inpred-io : ioImageIn inpredSrc inpredIn ≡
  "2\nhalted [tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(3,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(3,pt(inf),pt(inf),omega-kept), tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-send 0 1 ref(2,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect(3)] h4l3p3 v3"
inpred-io = refl

-- The program receives two values and the host gave one. The first
-- is written; the second `recv` parks on an empty inbox, the port has
-- ended, and the run is a `deadlock`.
inshort-io : ioImageIn inshortSrc inshortIn ≡
  "4\ndeadlock [tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(4,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(4,pt(inf),pt(inf),omega-kept), tr-send 0 1 ref(4,pt(inf),pt(inf),omega-kept) Kcopy] h5l5p3 v4"
inshort-io = refl

-- More input than receives. The second value is delivered after pid
-- 0 has ended and stays in its inbox; the run still halts.
inextra-io : ioImageIn inechoSrc inextraIn ≡
  "1\nhalted [tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(1,pt(inf),pt(inf),omega-kept), tr-send 0 1 ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(4,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h5l5p3 v1"
inextra-io = refl

-- Pids with both ports: entry 0, console 1, input 2, so the child is
-- pid 3 (`tr-spawn 0 3`). The child's write and pid 0's echo of the
-- input reach the console in delivery order.
inchild-io : ioImageIn inchildSrc inchildIn ≡
  "1\n9\nhalted [tr-step 0, tr-step 2, tr-step 0, tr-step 2, tr-step 0, tr-step 2, tr-step 2, tr-spawn 0 3, tr-step 2, tr-send 3 1 ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-step 2, tr-send 2 0 ref(12,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(12,pt(inf),pt(inf),omega-kept), tr-send 0 1 ref(12,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect(2)] h13l12p4 v1"
inchild-io = refl

-- Format 3 has no input port: input to it is refused.
inv3-io : ioImageIn inv3Src inv3In ≡
  "refuse: no input port"
inv3-io = refl

-- A character that is neither a digit nor a separator is refused.
inbad-io : ioImageIn inechoSrc inbadIn ≡
  "refuse: bad input"
inbad-io = refl

-- A format-4 image run without input: the port ends at once. A
-- program that writes and does not read is unaffected.
innone-io : ioImage innoneSrc ≡
  "1\nhalted [tr-step 0, tr-step 0, tr-step 0, tr-send 0 1 ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h2l2p3 v1"
innone-io = refl

-- `ioImageIn` with an empty text is the same run (`cli-in-empty` is
-- the general statement for `cliRunIn`).
innone-empty : ioImageIn innoneSrc "" ≡ ioImage innoneSrc
innone-empty = refl

-- A reading program with no input deadlocks: nothing ever reaches
-- pid 0. The port is `p3` and has already ended.
inecho-empty : ioImage inechoSrc ≡ "deadlock [] h0l0p3 v-"
inecho-empty = refl
