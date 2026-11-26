------------------------------------------------------------------------
-- B1d closed pins for the data images.
--
-- Each string is the text of one file in `examples/images`, trailing
-- newline included. Agda does not open the files. `echoImage` and
-- `runImage` are what `scripts/run_image.py` calls, and `driveImage`
-- is the outcome and kept nat `muro-beam` prints. The pins are `refl`,
-- so a change to the parser, `decideB`, or the CEK that moves one of
-- these lines fails `make agda`, not only the GHC jobs.
--
--   * a tag hit with the wrong arity is stuck. `pickArms` does not
--     fall through to a later arm with the same tag.
--   * with two arms on the same tag and arity, the first one wins.
--   * two fields: the last field is `gvar 0`, the first is `gvar 1`.
--   * `gmatch` on a `con` is stuck, like `gcase` on a nat.
--   * a g1 variable scrutinee is moved before the `cs` frame reads
--     `predComp`, so its fields bind at g0 and a use of one is stuck.
--     `gmatch` on a `suc↑` does the same (`gmatch-g1`). An ω
--     scrutinee binds and runs.
--   * `badFields` refuses an aliased g1 field. No image reaches that
--     branch (see above), so the pin is a hand-built heap.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.DataPins where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.Nat.Base using (zero; suc)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Muro.Base using (ok; fail)
open import Muro.Grade using (g1)

open import MuroBeam.BTm using (BTm; gvar; Arm; arm)
open import MuroBeam.Grade using (selfKept)
open import MuroBeam.Heap using (Obj; cell; live; Ref; ref; nat; con)

open import MuroBeam.Lib using (lookup)
open import MuroBeam.Load using (load)
open import MuroBeam.PRun using (seq1)
open import MuroBeam.PTm using (lowerP)
open import MuroBeam.Process using
  ( Sys; procs; ctl; Ctl; rv; Frame; cs; eval1; runFor
  ; Proc; proc; ready; sys )
open import MuroBeam.RunImage using (runImage; driveImage; echoImage; imgFuel)

-- The pid-0 control stops on a `cs` frame: the scrutinee is a value
-- and `onCase` returned `nothing`. That is the `gcase` step itself,
-- not an earlier β or allocation.
onCs : Ctl → Bool
onCs (rv _ _ (cs _ _ ∷ _)) = true
onCs _ = false

stopsOnCase : String → Bool
stopsOnCase src with load src
... | fail _ = false
... | ok p with seq1 (lowerP p) zero
... | nothing = false
... | just s with runFor imgFuel s
... | s2 with lookup (procs s2) zero
... | nothing = false
... | just q = onCs (ctl q)

-- examples/images/con0.mbi
con0Src : String
con0Src =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcon 0) (done))))\n"

con0-echo : echoImage con0Src ≡ con0Src
con0-echo = refl

con0-run : runImage con0Src imgFuel ≡ "con 0"
con0-run = refl

con0-drive : driveImage con0Src ≡ "stuck 0 v-"
con0-drive = refl

-- examples/images/con1.mbi
con1Src : String
con1Src =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcon 1 gze) (done))))\n"

con1-echo : echoImage con1Src ≡ con1Src
con1-echo = refl

con1-run : runImage con1Src imgFuel ≡ "con 1"
con1-run = refl

con1-drive : driveImage con1Src ≡ "stuck 0 v-"
con1-drive = refl

-- examples/images/con2.mbi
con2Src : String
con2Src =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcon 0 gze (gsu gze)) (done))))\n"

con2-echo : echoImage con2Src ≡ con2Src
con2-echo = refl

con2-run : runImage con2Src imgFuel ≡ "con 0"
con2-run = refl

con2-drive : driveImage con2Src ≡ "stuck 0 v-"
con2-drive = refl

-- examples/images/case0.mbi
case0Src : String
case0Src =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcase (gcon 0) (garm 0 0 gze)) (done))))\n"

case0-echo : echoImage case0Src ≡ case0Src
case0-echo = refl

case0-run : runImage case0Src imgFuel ≡ "nat 0"
case0-run = refl

case0-drive : driveImage case0Src ≡ "stuck 0 v0"
case0-drive = refl

-- examples/images/case1.mbi
case1Src : String
case1Src =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcase (gcon 1 gze) (garm 1 1 (gvar 0))) (done))))\n"

case1-echo : echoImage case1Src ≡ case1Src
case1-echo = refl

case1-run : runImage case1Src imgFuel ≡ "nat 0"
case1-run = refl

case1-drive : driveImage case1Src ≡ "stuck 0 v0"
case1-drive = refl

-- examples/images/case2-last.mbi
case2LastSrc : String
case2LastSrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcase (gcon 0 gze (gsu gze)) (garm 0 2 (gvar 0))) (done))))\n"

case2-last-echo : echoImage case2LastSrc ≡ case2LastSrc
case2-last-echo = refl

case2-last-run : runImage case2LastSrc imgFuel ≡ "nat 1"
case2-last-run = refl

case2-last-drive : driveImage case2LastSrc ≡ "stuck 0 v1"
case2-last-drive = refl

-- examples/images/case2-first.mbi
case2FirstSrc : String
case2FirstSrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcase (gcon 0 gze (gsu gze)) (garm 0 2 (gvar 1))) (done))))\n"

case2-first-echo : echoImage case2FirstSrc ≡ case2FirstSrc
case2-first-echo = refl

case2-first-run : runImage case2FirstSrc imgFuel ≡ "nat 0"
case2-first-run = refl

case2-first-drive : driveImage case2FirstSrc ≡ "stuck 0 v0"
case2-first-drive = refl

-- examples/images/case-first.mbi
caseFirstSrc : String
caseFirstSrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcase (gcon 1 gze) (garm 1 1 (gsu (gvar 0))) (garm 1 1 (gvar 0))) (done))))\n"

case-first-echo : echoImage caseFirstSrc ≡ caseFirstSrc
case-first-echo = refl

case-first-run : runImage caseFirstSrc imgFuel ≡ "nat 1"
case-first-run = refl

case-first-drive : driveImage caseFirstSrc ≡ "stuck 0 v1"
case-first-drive = refl

-- examples/images/case-miss.mbi
caseMissSrc : String
caseMissSrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcase (gcon 0) (garm 1 0 gze)) (done))))\n"

case-miss-echo : echoImage caseMissSrc ≡ caseMissSrc
case-miss-echo = refl

case-miss-run : runImage caseMissSrc imgFuel ≡ "stuck"
case-miss-run = refl

case-miss-drive : driveImage caseMissSrc ≡ "stuck 0 v-"
case-miss-drive = refl

case-miss-at-case : stopsOnCase caseMissSrc ≡ true
case-miss-at-case = refl

-- examples/images/case-arity.mbi
caseAritySrc : String
caseAritySrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcase (gcon 0) (garm 0 1 (gvar 0)) (garm 0 0 gze)) (done))))\n"

case-arity-echo : echoImage caseAritySrc ≡ caseAritySrc
case-arity-echo = refl

case-arity-run : runImage caseAritySrc imgFuel ≡ "stuck"
case-arity-run = refl

case-arity-drive : driveImage caseAritySrc ≡ "stuck 0 v-"
case-arity-drive = refl

case-arity-at-case : stopsOnCase caseAritySrc ≡ true
case-arity-at-case = refl

-- examples/images/gmatch-con.mbi
gmatchConSrc : String
gmatchConSrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gmatch (gcon 0) gze (gvar 0)) (done))))\n"

gmatch-con-echo : echoImage gmatchConSrc ≡ gmatchConSrc
gmatch-con-echo = refl

gmatch-con-run : runImage gmatchConSrc imgFuel ≡ "stuck"
gmatch-con-run = refl

gmatch-con-drive : driveImage gmatchConSrc ≡ "stuck 0 v-"
gmatch-con-drive = refl

-- examples/images/case-w.mbi
caseWSrc : String
caseWSrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gapp (glam (w 0) (gcase (gvar 0) (garm 0 1 (gvar 0)))) (gcon 0 gze)) (done))))\n"

case-w-echo : echoImage caseWSrc ≡ caseWSrc
case-w-echo = refl

case-w-run : runImage caseWSrc imgFuel ≡ "nat 0"
case-w-run = refl

case-w-drive : driveImage caseWSrc ≡ "stuck 0 v0"
case-w-drive = refl

-- examples/images/case-g1.mbi
caseG1Src : String
caseG1Src =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gapp (glam (1 0) (gcase (gvar 0) (garm 0 1 (gvar 0)))) (gcon 0 gze)) (done))))\n"

case-g1-echo : echoImage caseG1Src ≡ caseG1Src
case-g1-echo = refl

case-g1-run : runImage caseG1Src imgFuel ≡ "stuck"
case-g1-run = refl

case-g1-drive : driveImage caseG1Src ≡ "stuck 0 v-"
case-g1-drive = refl

-- examples/images/empty-gcase.mbi
emptyGcaseSrc : String
emptyGcaseSrc =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gcase gze) (done))))\n"

empty-gcase-echo : echoImage emptyGcaseSrc ≡ emptyGcaseSrc
empty-gcase-echo = refl

empty-gcase-run : runImage emptyGcaseSrc imgFuel ≡ "refuse: empty gcase"
empty-gcase-run = refl

empty-gcase-drive : driveImage emptyGcaseSrc ≡ "refuse: empty gcase"
empty-gcase-drive = refl

-- `case-g1` above: `useVar` moves the g1 pointer and leaves a g0 ref
-- in the binder's slot, so `predComp` at the `cs` frame is g0, the
-- field is bound at g0, and `gvar 0` in the arm is stuck. `gmatch` on
-- a `suc↑` does the same; that rule predates B1d. `decideB` accepts
-- both terms. `case-w` is the same term with an ω binder and runs.
gmatchG1Src : String
gmatchG1Src =
  "(muro-beam-image 1 (boundary 1) (entry (seq (gapp (glam (1 0) (gmatch (gvar 0) gze (gvar 0))) (gsu gze)) (done))))\n"

gmatch-g1-run : runImage gmatchG1Src imgFuel ≡ "stuck"
gmatch-g1-run = refl

------------------------------------------------------------------------
-- `badFields` on a hand-built heap. Object 0 is the field, object 1
-- is `con 0 [field]`. The control is returning the scrutinee into a
-- `cs` frame whose binder is checked g1, so `predComp` is g1. With
-- the field only in the constructor, `eval1` takes the arm. With a
-- second reference to the field in the environment, `count` of
-- object 0 is 2 and `badFields` refuses the step.
------------------------------------------------------------------------

private
  fld scr : Ref
  fld = ref 0 g1 g1 (selfKept g1)
  scr = ref (suc zero) g1 g1 (selfKept g1)

  hp : List Obj
  hp = cell (nat zero) live ∷ cell (con 0 (fld ∷ [])) live ∷ []

  arms1 : List (Arm 1)
  arms1 = arm 0 1 (gvar fzero) ∷ []

  atCs : List Ref → Proc
  atCs env = proc 0 ready [] [] (rv scr env (cs (gvar fzero) arms1 ∷ []))

  stepped : Maybe Sys → Bool
  stepped (just _) = true
  stepped nothing  = false

case-g1-field-ok : stepped (eval1 (sys hp (atCs (scr ∷ []) ∷ [])) zero) ≡ true
case-g1-field-ok = refl

case-g1-field-aliased :
  stepped (eval1 (sys hp (atCs (scr ∷ fld ∷ []) ∷ [])) zero) ≡ false
case-g1-field-aliased = refl
