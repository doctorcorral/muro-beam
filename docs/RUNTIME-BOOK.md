# Runtime as a Muro book

The Agda model in `agda/` is the proof. The book in `book/` is the artefact the muro wall checks. This document is the plan for that book.

Part 1, merged as PR #6, is the boundary mirror, the runtime data, this plan, the smoke, and the CI job. Part 2, merged as PR #7, runs `alloc`, `deref` / `spend`, `send`, and `reuse`. Part 3, merged as PR #8, runs one CEK step (`eval1` and its helpers, plus fuel-bounded `runFor`) and total ordered `collect`. Part 4 is this book. It runs v0 `recv` (`recvRoot`), the process steps `spawn1`, `emit1`, `deliver1`, `recv1`, `arm1`, `seq1`, `bind1`, and `done1`, one scheduling step (`tryStep` / `tryPStep`), and `List Event` emission. The in-boundary `trip` runs spawn, emit a grade-1 reference, deliver, and recv. `cex`, already refused by `inBoundary`, is also refused when lowered and run (`ex-cex-stuck`). The smoke pins the accepted steps and the refusals. Peer death is the later monitor: one process watches one peer, queued mail is received before `tr-down`, and the failure arm runs once.

Ricardo approved the plan on 2026-11-12, with the four amendments below, and approved part 2 the same day after PR #6 merged. Part 2 merged as PR #7 later that day. Part 3 merged as PR #8. Part 4 followed.

## What this part does not claim

For the closed examples below, this book is an executable image of the Agda emitter. `make conformance` checks the printer with `make book-show`, compiles `MuroBeam.Conform` with `agda --ghc --safe`, and diffs the MAlonzo binary against the strings `book/show.muro` normalises. The CI job `malonzo conformance` runs that command and fails if a line differs. The lines match:

```
trip: just [tr-spawn 0 1, tr-send 1 0 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) Kmove, tr-recv 0 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0))))] h3l3p2
stuck: nothing
alloc: just [tr-alloc 0 pt(fin(1))] h1l1p1
deref: just [tr-spend 0 pt(fin(1)) pt(fin(0))] h1l1p1
send: just [tr-send 0 1 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) Kmove] h1l1p2
step: just [tr-step 0] h1l1p1
collect: ran [tr-collect(0)] h1l0p1
wide: overflow overflow overflow 10
down: just [tr-recv 0 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))), tr-down 0 1 killed] h1l1p2
down-again: nothing
down-done: just [] h1l1p2
abandon: just [] h1l1p2
send-dead: just [] h1l1p2
```

`trip` is `emitPops` of spawn, emit, deliver, and recv on `s0`. `stuck` is `eval1` after `runFor 6` of the lowered `cexApp`. Both sides refuse, and the line is `nothing`. A refusal carries no fingerprint. `alloc`, `deref`, `send`, `step`, and `collect` are the one-step pins in `book/emit.muro`. `collect` is total, so that line says `ran`. Ignore, flush, and await are not in the comparison. A wrapper is still not proved equal to its operation for an arbitrary system. `eval1` still returns `Maybe Sys`. `collect` still returns `Sys`. The events are built by the wrappers.

`down` is `runDs` of monitor, a `killed` exit, and two receives, on a meeting whose observer inbox already holds one grade-1 message. The first receive is `tr-recv`. The second is `tr-down`. `down-again` is that schedule plus one more receive, and the line is `nothing`: the arm does not run twice. `down-done` is monitor, `d-done` of the peer, an exit, and a receive. The peer is `done`, so the receive is a halt: `just` and an empty event list, and `armed` stays false. `abandon` is the same shape for `d-abandon`, and the reason stored is `abandon`. `send-dead` is monitor, a `killed` exit, and `d-send`. The put is consumed: `just` and an empty event list. The death flags are not on the fingerprint. `down-armed`, `down-done-armed`, `send-dead-dead`, and the other equations in `book/death.muro` pin them. A matching `just []` is not, by itself, the claim that the arm ran.

Success lines compare the event list and a post-state fingerprint. The fingerprint is `h` plus the heap length, `l` plus the number of live cells, and `p` plus the process count, in the same decimal as the events. It is not the system. Payloads, grades, residuals, and control are not on the line. A matching success line is not a claim that the final systems are equal. That is a hard limit of this comparison. `stuck` on `just` would print `just` and that same fingerprint, and no events, because `eval1` returns `Maybe Sys`. Today's `stuck` line is the refusal `nothing`.

`wide` is a printer check, not an eighth runtime example. Decimal fuel is 8. Fuel exhaustion, a remainder past 9, and a digit past 9 print `overflow`. They do not print a truncated numeral or an empty string. The four words are fuel 1 on ten (two digits), the bump catch-all at remainder 10, the digit catch-all at 10, and ten at fuel 8, which is `10`. A unary number of nine digits is not normalised. If one side goes back to truncating, this line no longer matches.

`MuroBeam.Cex` is the one closed `cex` and the one-process `lowerTm`. Example re-exports `cex` and still wraps `cexApp` as a `Checked`. `Lower.lower` is `lowerTm` of the checked term. The statements of `cex-ok`, `ex-cex-stuck`, and `lower-safe` are the same. `MuroBeam.Event`, `MuroBeam.Emit`, `MuroBeam.Cex`, and `MuroBeam.Conform` are `--safe` and have no postulates. The umbrella imports them and does not open them, so the v1c name `cex` stays the one Example re-exports. The harness does not import `Example` or `Lower`, because both reach `Unique`, and it does not import `PExample`, `Stray`, or `PWf`. `MuroBeam.Cex` imports `Process` and the grade syntax. Its generated Haskell imports those modules and does not import `Unique`.

The boolean checks and the proof predicate are not proved equivalent in general. `once` is accepted by `inBoundary` and inhabits `InB`, and `inBoundary-to-noEscape` sends that proof to `NoEsc`. `cex` is refused by the boolean check. A theorem that `inBoundary t ≡ yes` if and only if an `InB` proof exists is not in this book.

Part 2 is also weaker than Agda where the checker cannot state the Agda theorem. The Agda text is unchanged. Nothing is postulated.

- Agda's `grade0-not-dereferenced` assumes `rootAt s i j ≡ just r` and `residual r ≡ g0`. The book checks the shape that reduces: process 0, root 0, residual `pt (fin 0)`, in `grade0-not-dereferenced`. An arbitrary `Maybe` is not inverted.
- Agda's `spendRef-obj` and `spendRef-checked` follow from `spendRef r ≡ just r'`. The book proves the finite, `omega`, and `iv` shapes (`spendRef-finite`, `spendRef-omega`, `spendRef-iv`). `spendRef-finite` packages the object index and the checked grade.
- Agda's `Grade1Unique` is `∀ i → hasG1 i rs ≡ true → count i rs ≡ 1`. The empty-list case is `{false ≡ true}`, which this checker does not eliminate. The book pins `{count ≡ suc 0}` and `{hasG1 ≡ true}` on the alloc, deref, send, and reuse examples. `send-g1-moves` is the move for a checked `g1` root of process 0 sent to process 1, heap unchanged. It is not the quantified count preservation in `MuroBeam.Unique`.
- Agda's `send-preserves-residual` concludes `AllInv (refsOf t)` from `send ≡ just t`. Every book `Ref` already stores `Kept` (`ref-inv`). Send moves or copies that `Ref`. The book does not invert `{sendRoot ≡ just t}`.
- `alloc-ordered` is `OrdAt` for the heap append `alloc` performs. `reuse-ordered` is `OrdAt` for the `poke` `reuse` performs. Agda's `reuse-ordered` is the implication from `reuse ≡ just t` together with `Ordered (heap s)`. The examples pin the boolean as well (`alloc-ordered-bool`, `reuse-ordered-bool`). Agda's `Ordered` is a function of `lookup`. `OrdAt` is the list spine, which is the form this checker indexes.

Part 3 is weaker than Agda in the same way. The Agda text is unchanged.

- Agda's `collect : Sys → Sys` is total. The book function has that type. `collect-total` is that function, and `collect-nil` plus the `book/cek.muro` equations are concrete results. Agda's `Collected` is `t ≡ collect s`. The book does not add a separate existence proof.
- Agda's `collect-safe` says a `Reach`able index stays `live`, payload preserved. `Reach` is not a book data type. A parameter of type `Sys` is elaborated as `Type`, and the constructors would store membership in `liveRefs`, a residual boolean, and a child index, which the positivity walk cannot store. The book pins the shapes that reduce: `collect-live` (a non-`g0` root), `collect-ctl` (a control ref), `collect-edge` (a `suc-up` child of a higher reached index), and `collect-grades` (`omega` and an interval). Those names are examples, not the quantified theorem.
- Agda's `collect-frees-zero` says that `anyKeeper i (refsOf s) ≡ false` frees slot `i`. The book proves that pair for one system (`collect-free`, `collect-free-keeper`) and pins the same outcome for a `g0` root, an unmarked parent, and a `g0` env slot. It does not quantify over every system and index. `anyKeeper-nil`, `anyKeeper-g0`, `anyKeeper-omega`, `anyKeeper-aff`, and `anyKeeper-other` are the keeper facts that reduce.
- Agda's `go` walks the tail once and uses that mark list twice. A computed list is affine, and `let` only splits a pair, so the book passes the list to `markIfAt`, whose parameter is `+`. The recursion is still one structural call. The function is the same.
- `lookupB` and `lt` do not compute at a variable index, and `andB` matches its first argument, so a `g0` fact does not fire until `lt` reduces. Seed and `markOne` equations are concrete indices: `seed-g0`, `seed-omega-0`, `seed-aff-0`, `markOne-g0`, `markOne-not-lower`, `markOne-child`. `markIf-false` is general: a false parent bit returns the mark list.
- Agda's `capture-check-clear` takes an in-boundary lambda, an `EnvGrades` realisation, and concludes `anyG1 env ≡ false`. The book realises the context by canonical refs: `eg-cons` stores `ref o g r k`, so the checked grade is the context entry and the constructor does not call `checked`. `sharp-env`, `lam-clear`, `glamSharp`, `capture-check-clear`, and `closed-lam-clear` are checked. A motive on indexed `GTm` cannot return the literal `Type` (`Type has no type`). `isLam` returns a `Bool`, and `CapRes` / `packLam` / `fromCap` are the small family that extracts the `NoG1` stored on `ib-lam`. Carrying `EnvGrades` through every `eval1` step is not this part.
- There is no inversion of `{eval1 s i ≡ just t}`. `fresh-kept` says a `freshRef` is `selfKept`. The spend shapes are the part-2 lemmas. `step-ze`, `step-copy`, and `step-move` are the residual facts on the systems that reduce. `runFor` matches Agda: structural on the fuel, process 0, stop when `eval1` returns `nothing`. It is not a scheduler.

Part 4 is weaker than Agda in the same way. The Agda text is unchanged.

- Agda's `Step` and `PStep` store `{op ≡ just t}`. A book constructor cannot store that equation: the positivity walk unfolds `recvRoot` and `lookup`. `Step` and `PStep` are unindexed and hold the two systems. A hand-built value is well-typed. `tryStep`, `stepOf`, `pstepOf`, and `runPops` are the check, and the smoke pins their `just` and `nothing` results. `step-collect-always` says `tryStep s op-collect ≡ just (collect s)` for an arbitrary `s`. That is the book form of "collect is always a step". It is not Agda's constructor.
- `PStep` has `p-lift`, `p-spawn`, `p-emit`, `p-deliver`, `p-recv`, `p-arm`, `p-seq`, `p-bind`, and `p-done`. It does not have `p-await`, `p-flush`, `p-npeek`, or `p-ndemon`. `await1`, `flush1`, `npeek1`, and `ndemon1` are not ported. `flush1` blanks heap edges. `no-stray-reply` is not a book theorem. `ignore-spawn` and `ignore-arm` pin the spawn that rewrites `ignore` to `ignoreT`, and the `arm1` that turns `ignoreT` into `flushT` and records the tag. The proper-ignore flush and the naive-ignore leak are not in this book.
- `PStepStar` (`pstop`, `pmore`) does not store the `just`-proof. `tripStar` is the four constructors. `trip-p-spawn`, `trip-p-emit`, `trip-p-deliver`, `trip-p-recv`, and `trip-run` are the check that those constructors are the runs. `runPops` and `emitPops` take the `Pop` list first, so the structural call's decreasing argument is that tail.
- The placeholder cell a spawn snocs, and the cell a move snocs, are not `tr-alloc`. `deliver1` emits no event. `recv1` on an empty inbox and `ready` returns `just` and an empty event list. A refusal is `nothing`, not an empty trace. `tr-step` is the pid. Control before and after is still absent.
- The wrappers call the operations. There is no quantified equation that an emitting wrapper agrees with the operation for every system: a neutral `Maybe` does not match, so that equation is not `refl`. The pins are the systems that reduce (`trip-trace`, `emit-deref-g1`, `emit-alloc0`, `emit-send-g1`, `emit-reuse`, `emit-ze`, `emit-collect-free`, `emit-recv-one`, and the copy and refusal traces).
- `spawn-preserves-grade1`, `lowerP-safe`, and `residual-inv-step` are not restated. Every `Ref` still stores `Kept`.

The conformance comparison is `make conformance`, described above. The book side of `trip` is the first line. `ρ` prints as `ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0))))`, which is `selfKept grade1`. The driver imports `PRun`, not `PExample`. Local `agda` is 2.8.0 and local `ghc` is 9.12.2. CI uses Agda 2.8.0 and GHC 9.8.4. The phrase above is only for the lines under "What this part does not claim", and the fingerprint on a success line is not the system. `wide` is the printer check. The death lines are the same comparison: events and that fingerprint, not the meeting flags.

A book lemma that shares an Agda name is a shape or an example the wall can check, not the Agda theorem, unless the equation really is the same closed statement. `trip-spawn` is `spawn1 s0 0 ≡ just s1` on the `trip` systems. `ex-cex-stuck` is `eval1 (runFor 6 (lowerTm 0 cexApp)) 0 ≡ nothing`. See the weaker-than-Agda lists above.

## Four amendments

### 1. The book and the Agda model meet in a conformance test

The link is a test, not a slogan. Both sides run on the same closed terms. For the lines under "What this part does not claim", the traces match, and that is the executable image. It is not a claim about an arbitrary system.

Shared examples, encoded in `book/smoke.muro`:

- `once` is muro's `grade-once`. Agda writes `glam g1 g0 (gvar fzero)`. The book writes `glam 0 grade1 grade0 (gvar (suc 0) (fzero 0))`. The extra `Nat` is the scope. `fzero 0` is de Bruijn 0 at scope 1.
- `cex` is the §2B term. Agda writes it once, in `MuroBeam.Cex`, and Example re-exports that term: `glam g1 g0 (gapp (glam gω g0 (gapp (gvar fzero) (gvar fzero))) (glam aff g0 (gvar (fsuc fzero))))`. The inner application sits at scope 2. `fzero (suc 0)` is the inner binder. `fsuc (suc 0) (fzero 0)` is de Bruijn 1, the outer grade-1 binder.
- `ghost`, `glam g0 g0 (gvar 0)`, is the witness that the converse fails. `inBoundary` returns `no` and `noEscape` returns `yes`. Agda does not claim the converse either.

`book/trace.muro` fixes the event datatype. The book and `MuroBeam.Event` both emit `List Event` with these fields.

| Event | Fields |
| --- | --- |
| `tr-alloc` | object index, checked grade |
| `tr-spend` | object index, residual before, residual after |
| `tr-send` | source pid, destination pid, reference, `Kmove` or `Kcopy` |
| `tr-recv` | pid, reference |
| `tr-spawn` | parent pid, child pid |
| `tr-step` | pid. One CEK step. Control before and after is a later field. |
| `tr-collect` | freed object indices, in increasing order |
| `tr-down` | observer pid, dead pid, reason (`killed`, `crash`, `normal`, or `abandon`) |

`tr-` keeps these names off the process-term constructors. The heap operations, `eval1`, and `collect` do not build a trace. `book/emit.muro` does, by calling those operations and pairing the resulting system with the events. A placeholder cell is not `tr-alloc`. `deliver1` adds no event.

### 2. Two kinds of grade

Runtime residual grades and checked grades are ordinary inductive data: `BeamGrade` (`g0`, `g1`, `omega`) and `beamGrade`, the same reading as `MuroBeam.Boundary`, plus muro's `Grade` (`pt`, `iv`) as values `grade0`, `grade1`, `gradeOmega`, and `aff`. `Kept` is residual ≤ checked, also as data.

Muro's own graded binders, written on this book's source, are type-level evidence. Emitters erase them. The wall checks them the way it checks any other Muro book. They are not `BeamGrade` and they are not stored in a `Ref`.

A `+` on a `Nat`, a `Grade`, a `GTm`, a `Vec`, a `Ref` index, a `Sys` field, or an `OrdAt` index is the host's reuse quantity, so a walker or a proof can read the field twice. It is not a runtime grade. The two roles are not mixed.

### 3. Refusal belongs to the book's check

Out-of-boundary refusal is `inBoundary` and `noEscape`, total `run` functions. It is not the muro type checker rejecting a client term. `once` and `cex` are both well-typed `GTm 0` values. `boundary-accept` is `{inBoundary once ≡ yes}`. `boundary-refuse` is `{inBoundary cex ≡ no}`. The same shape is checked for `noEscape`. `mix muro.check` fails if those results flip.

The functions return `Answer` (`yes` or `no`), not a proof-carrying `Dec`. `refl` is refused in `run` mode, so a `run` cannot build the `yes` proof. The proof predicate is separate, and `inBoundary-to-noEscape` is evidence.

The same rule covers the heap. A refused `deref` of a `g0` residual, a refused `send` of a `g0` checked grade, a refused `send` of a residual that is already `g0`, a refused second `spend` of a spent `g1`, a refused `reuse` of an unspent root, a refused `reuse` of two spent references, a refused `reuse` when a mailbox still aliases the object, and a refused `reuse` of a spent non-`g1` ref are `nothing` from the `run` function. `book/run.muro` witnesses the results. `mix muro.check` fails if they flip.

The same rule covers the stepper. `eval1` on `idle` and on `pr`, a return against an empty stack or a `saved` frame, a `glam` whose env has a `g1`, a `gvar` of a missing slot or of a `g0` residual, a second spend of an already-spent `g1`, a `beta` that fails `badG1` or whose captured env has a `g1`, and a match on a `clo` or on `nat (suc _)` are `nothing`. `book/cek.muro` witnesses the results. The terms and heaps are well-typed data.

The same rule covers receive, spawn, and a schedule step. An empty v0 mailbox, a missing process, an `idle` control, a `pr` of `pdone`, a `keep` of a `g0` reference, a thinning that does not match the environment, a residual `g0` on `emit1`, a control that is not `send`, a missing destination, an empty ether, `recv1` on an empty inbox in `waiting` or `done`, and a control that is not `recv` are `nothing`. `recv1` on an empty inbox in `ready` is `just`: it parks `waiting`. `book/recv.muro` and `book/trip.muro` witness the results. `ex-cex-stuck` is the running refusal of `cex` beyond `inBoundary`: `lowerTm` of `cexApp`, six steps of `runFor`, then `eval1` returns `nothing`. The term stays a well-typed `GTm 0`.

### 4. Totality, decided here

Later parts follow this rule.

- Terms are an inductive datatype, a pure mirror of `GTm` and `PTm`.
- Every primitive operation is one `run` function, structurally recursive on its inputs: `alloc`, `deref` / `spend`, `send`, `recv`, `spawn`, one CEK step, and total ordered `collect`. No termination pragma. No hand-written well-founded recursion.
- Multi-step evaluation is driven from outside. Either an explicit fuel argument, `runFor fuel state`, or an external scheduler that applies one process step at a time, in the style of Agda's `PStep`.
- No internal unbounded loop.

`inBoundary` and `noEscape` follow the rule: they recurse on the term, and they take no fuel. `alloc`, `deref`, `sendRoot`, and `reuse` follow it too. `eval1` does not call itself. Its helpers are one `run` each. `runFor` recurses on the fuel and stops when `eval1` returns `nothing`. `collect` is one `run` from `Sys` to `Sys`, structural on the heap and the process list, with no internal loop. `recvRoot` walks one mailbox. `spawn1` walks one thinning. `emit1`, `deliver1`, `recv1`, `seq1`, `bind1`, `done1`, and `arm1` each walk one process list or one stack. `finRebuild` walks one `Fin`, with the bound erased so the `Fin` is the argument it descends on. `runPops` and `emitPops` walk one `Pop` list and apply one step, then the tail. `runDs` walks one `DOp` list the same way. `stepMon`, `stepExit`, `observe`, `stepRecv`, `stepSend`, `stepDone`, `stepAbandon`, and `stepSettle` do not call themselves. None of them is an internal unbounded loop.

## Four parts

| Part | Contents |
| --- | --- |
| 1 (merged, PR #6) | Boundary mirror, runtime data, this plan, smoke, CI. |
| 2 (merged, PR #7) | `alloc`, `deref` / `spend`, `send` that moves a finite grade and copies `omega` and every `iv`, and `reuse`. Residual and grade-1 evidence the checker can express. Smoke for the accepted steps and the refusals. |
| 3 (merged, PR #8) | One CEK step (`eval1`, `runFor`), and total ordered `collect`. |
| 4 (this book) | `recv`, `spawn`, scheduling. The in-boundary `trip`. The out-of-boundary term refused by `runFor` / `eval1`. Emission of `List Event`. The MAlonzo comparison is `make conformance`. |

## Two pins

The Agda model still imports `vendor/muro` at v0.20.32 (`792497695ef3b0dd37fe2b262f6225c989eb6818`). That pin is not bumped. The book is checked with muro 0.20.33 from Hex. 0.20.33 adds CSHRL synthesis on top of 0.20.32. This book does not use CSHRL. Parts 2, 3, and 4 stayed on 0.20.33: the evidence in this book, including `trip-trace` and `ex-cex-stuck`, was expressible on that pin. Peer death stayed there too. The schedules are closed equations on a `Meet`, which 0.20.33 already checks. muro 0.21.0's `may fail` syntax is the language side. This book is the VM, and it does not need that syntax. Later published releases are not, by themselves, a reason to move.

`make book` runs `mix muro.check book/smoke.muro`. That file imports the rest of the book except the conformance printer, and the checker flattens imports, so one check covers those files. `make book-show` runs `mix muro.check book/show.muro`. `smoke.muro` does not import the printer. `make conformance` runs `book-show` before the MAlonzo diff. CI installs the pinned archive. It does not fetch the Agda standard library.

## What the book defines

| File | Contents |
| --- | --- |
| `book/data.muro` | `Bool`, `Maybe`, `Answer`, `List`, `Fin`, `Vec`, `Le`, `leRefl`, `le-lower`, `vlookup`, `lt`, `natEq`, `notB`, `append`, `lookup`, `update`, `removeAt`. Local, so `std:list`'s `Or` (`yes` / `no`) does not clash with `Answer`. The book's `Bool` replaces the prelude, so `not` is not in scope. |
| `book/grade.muro` | `Point`, `Grade`, `BeamGrade`, `beamGrade`, `isZeroGrade`, `isG1`, `g1InScope`, `kind`, `Kept`, `selfKept`, `spend`, and the inductive premises below. |
| `book/term.muro` | `GTm`, `Scoped`, `predGrade`, `Pred`. |
| `book/boundary.muro` | `Ix`, `InB`, `NoEsc`, `toNo`, `inBoundary-to-noEscape`, `inBoundary`, `noEscape`. |
| `book/heap.muro` | `Status`, `Ref`, `Val`, `Obj`, `ordered`, `Below`, `OrdAt`, `spendRef`, `count`, `hasG1`, `alloc-ordered`, `reuse-ordered`. |
| `book/process.muro` | `PState`, `Msg`, `Thin`, `PTm`, `Flight`, `Code`, `Frame`, `Ctl`, `Proc`, `Sys`. |
| `book/ops.muro` | `alloc`, `deref`, `sendRoot`, `reuse`, `refsOf`. |
| `book/trace.muro` | `Event`, `Trace`. The operations, the stepper, and `collect` do not emit these. |
| `book/run.muro` | Checked alloc, deref, send, and reuse examples, including the refusals. |
| `book/step.muro` | `eval1`, `evalTm`, `evalRet`, `beta`, `onMatch`, `useVar`, `anyG1`, `regrade`, `badG1`, `runFor`, `lowerTm`, and `capture-check-clear`. |
| `book/collect.muro` | `liveRefs`, `anyKeeper`, `markGo`, `collect`. `collect` returns `Sys`. |
| `book/cek.muro` | Accepted and refused CEK steps, and the collect examples. |
| `book/recv.muro` | v0 `recvRoot`. Empty mailbox is `nothing`. A message is dequeued onto the roots. |
| `book/prun.muro` | `spawn1`, `emit1`, `deliver1`, `recv1`, `arm1`, `seq1`, `bind1`, `done1`. |
| `book/sched.muro` | `Op`, `Pop`, `Step`, `PStep`, `PStepStar`, `tryStep`, `tryPStep`, `stepOf`, `pstepOf`, `runPops`. |
| `book/emit.muro` | Emitting wrappers and `emitPops`. A run is `ran : Sys → List Event → Run`. |
| `book/trip.muro` | The `trip` schedule, the copy and ignore pins, and the refusals. |
| `book/smoke.muro` | `once`, `cex`, `ghost`, `cexApp`, `ex-cex-stuck`, and the import of `trip.muro`. |
| `book/death.muro` | One monitor, exit, receive, consumed send, `done`, abandon, and settled `:normal`. |
| `book/show.muro` | The conformance printer. It imports `smoke.muro`. `make book` does not import it. `make book-show` checks it. `scripts/book_show.exs` normalises the example lines, `show-wide`, and the death lines. |

`beamGrade` reads `pt (fin 0)` as `g0`, `pt (fin 1)` as `g1`, `pt inf` as `omega`, and every `iv`, including `aff`, as `omega`. `pt (fin n)` for `n ≥ 2` is `nothing`. The checked equations are `beam-g0`, `beam-g1`, `beam-omega`, `beam-iv`, and `beam-fin2`. `kind` is the same three send behaviours: `g0-not-sent`, `g1-moved`, `omega-copied`, `iv-copied`.

`inBoundary` refuses a `glam` when the sharp flag is true, and a `gvar` whose binder is grade 0. A `gpi` body is scanned. Uses are not counted. The flag starts false on the empty context and is pushed with `orB sharp (isG1 c)`, the same boolean as `g1InScope`. `noEscape` is the same walk with every `gvar` accepted. `inBoundary-to-noEscape` says the filter implies the capture restriction. The converse is not a theorem. `ghost` is the boolean witness, and `ghost-noesc` inhabits `NoEsc` for that term.

`Ref` stores an object index, a checked grade, a residual grade, and a `Kept` proof. `selfKept` builds the reflexive proof. `Val` is `nat`, `suc-up`, or `clo` of a captured `List Ref` and a `Scoped` term. `Obj` is a payload and `live` or `free`. `ordered` is the boolean walk. `OrdAt` is the proof-carrying spine: the cell at index `i` has children below `i`. Agda states `Ordered` as a function of `lookup`. The list induction is the form muro indexes directly. `heap-nil`, `heap-nat`, `heap-bad`, and `heap-link` pin the boolean. A successor that points at its own cell is `false`. A successor that points at a lower cell is `true`. `ordered-nil` and `ordered-nat` inhabit `OrdAt`.

`Proc` is pid, state, roots, inbox, control. The inbox is the mailbox. `Msg` holds a `Ref`. `PState` is `ready`, `waiting`, `done`. `Ctl` is `idle`, `ev`, `rv`, or `pr`. `Frame` is `ar`, `fn`, `su`, `mt`, `bd`, or `saved`. `PTm` has the Agda constructors, with `done` spelled `pdone`. A `+` on a scope, on `send`'s destination, on a protocol tag, and on `Code`'s scope, environment, and dead-tag list is host reuse, so a step can read the field and write it back. `Proc`'s control stays affine. `waiting` is written only by `recv1`.

`spend` steps a `Kept`. A finite residual `pt (fin (suc k))` becomes `pt (fin k)` by `le-lower`, and the checked grade stays. `g0` is `nothing`. `omega` and every `iv` stay. `spendRef` rebuilds the `Ref`. `alloc` appends a live `nat` cell. The fresh index is `length` of the heap, and the new root is `selfKept`. `deref` is Agda's run-mode deref: look up the root, `spendRef` it, write it back. `sendRoot` is Agda's `send`. `kind` of the checked grade decides. `isZeroGrade` of the residual refuses. A finite point, including `g1` and `pt (fin n)` for `n ≥ 2`, moves: the root leaves the sender and is enqueued on the receiver. A self-send posts on that same process after the drop. `omega` and every `iv` copy: the sender keeps the root and the mailbox receives the same `Ref`. The heap is unchanged. `reuse` overwrites a spent grade-1 slot in place when `count` of that object in `refsOf` is 1. `refsOf` counts roots, mailbox messages, heap edges, and control references, so an in-flight message counts.

`eval1` looks up process `i` and steps its control. `idle` and `pr` are `nothing`. `ev` is `evalTm`. `rv` is `evalRet`. Syntax stays on frames. Values are `Ref`s. A `g1` pointer whose `count` in `refsOf` is 1 is moved: the env slot becomes a fresh `g0` ref and a dummy `nat 0` is appended. A `g1` whose count is not 1 is `nothing`, not an alias. A nat is copied onto a fresh `omega` ref. An `omega` or interval pointer is written back. `glam` is refused when `anyG1` of the env is true. `beta` opens a `clo` of a `glam` and refuses `badG1` or a captured `g1`. `saved` is not resumed here. `runFor` applies `eval1` at process 0, structural on the fuel.

`collect` seeds marks from `liveRefs` (control, roots, and mailbox messages) whose residual is not the point `g0`. `markGo` walks from the highest index down and marks a child only when the parent bit is set, the child index is lower, and the child's residual is not `g0`. `apply` keeps a marked object and sets `live`. An unmarked slot becomes `cell (nat 0) free`. `clean` drops a `g0` residual from roots and messages. Environment and frame slots stay, so indices do not move.

`recvRoot` is v0 `recv`. An empty mailbox is `nothing`. A message is appended to the roots and the inbox becomes the tail. `recv1` is the process-layer step: a message is bound on the front of the environment and the process stays `ready`; an empty inbox in `ready` parks `waiting`; `waiting`, `done`, and any term other than `recv` are `nothing`. `spawn1` appends a child at `length` of the old process list, thins the environment, and follows `kind`. A finite point moves and the parent slot becomes one fresh `g0` reference, shared by every moved slot. `omega` and every `iv` are copied. `g0` is `nothing`. The placeholder cell is allocated whenever the split succeeds, including when every slot was copied. `emit1` refuses a residual `g0`, a missing destination, and a dead or demo tag of the object. A move snocs the same kind of placeholder and parks the reference in the ether. A copy keeps the heap and the environment. `deliver1` takes one flight from `pr` or from a `saved` frame, updates the sender first, drops the flight when the destination's dead list contains the object index, and enqueues it otherwise. A demo tag does not drop it. `waiting` wakes. A missing destination is `nothing`, and the sender update is not returned. `seq1` moves the ether onto one `saved` frame. `bind1` resumes when that frame is the whole stack. `done1` sets `done` and clears the roots and the environment. `arm1` turns `ignoreT` into `flushT` and records the tag. `await1` and `flush1` are not in this book.

`tryStep` is one v0 operation: `deref`, `sendRoot`, `recvRoot`, `alloc`, `reuse`, `eval1`, or `collect`. `tryPStep` is one process step, or `tryStep` under `pop-lift`. `runPops` applies a list of those steps from the outside. `Step` and `PStep` name the two systems. `stepOf` and `pstepOf` build them only from a `just` result.

`emitDeref` reports `tr-spend` with the object index and the residual before and after `spendRef`, and the state from `deref`. `emitAlloc` reports `tr-alloc` at `length` of the old heap. `emitSendRoot` and `emitEmit` report `tr-send` with the source pid, the destination pid, the reference, and `Kmove` or `Kcopy`. `emitSpawn` reports `tr-spawn` of the parent index and the old process-list length. `emitRecv` and a binding `emitRecv1` report `tr-recv`. `emitEval` reports `tr-step`. `emitCollect` reports `tr-collect` of the unmarked indices, increasing. `emitReuse`, `emitDeliver`, a parking `emitRecv1`, `emitArm`, `emitSeq`, `emitBind`, and `emitDone` report an empty list when the operation returns `just`. `trip` is spawn at process 0, emit at the child, deliver, recv. The trace is `[tr-spawn 0 1, tr-send 1 0 ρ Kmove, tr-recv 0 ρ]`.

## Peer death

`MuroBeam.Death` and `book/death.muro` are the same meeting. It is not stored on `Proc`. `codeDead`, `deadInCtl`, and `deadAt` stay the protocol tags that `deliver`, `ignore`, and demonitor already use. A death here is `Why` and `tr-down`.

One monitor: `d-mon` of an observer pid and a peer pid. A second monitor is `nothing` (`second-monitor`). An exit with no monitor is `nothing` (`no-monitor`). `d-exit` records the reason and emits nothing. A failure exit sets `dead`. `d-send` is only the consumed put: when `dead` is set it returns `just` and an empty event list (`send-dead-events`, `send-dead-dead`), and the arm is still false. The next receive emits `tr-down` (`send-then-down`). A send before that mark is `nothing` (`send-before-dead`). Enqueue of an ordinary message stays `sendRoot` and `emit1`.

`d-recv` on a non-empty observer inbox dequeues one message and emits `tr-recv`. It does not observe the down yet. Agda's `takeMail` also appends that `Ref` onto the process roots. The book's `takeMail` does not. `Ref`'s `Kept` field is affine, so the same ref cannot be the received value and a new root. The event still carries the ref. No death equation reads the roots, and the fingerprint does not either. `deliver1` of ether mail is still event-silent. When the inbox is empty, `observe` runs. If the reason matches the arm, the step emits one `tr-down` (observer, peer, reason) and sets `armed` and `noted`. `down-events` is that pair, mail then down. `down-again` is one more receive, and it is `nothing`. `send-after-arm` is a consumed put after the arm: the event list stays the mail and the one down.

`d-done` on the peer sets the process state to `done` and sets `halted`. A later exit is recorded and does not set `dead`. The receive is `just` and an empty list (`down-done-events`). `armed` is false, `dead` is false, `halted` is true, and the peer state is `done`. `d-abandon` sets `halted`, stores `abandon`, and does not change the process state (`abandon-state` is `ready`). The receive is the same empty success, and the arm does not run.

`:normal` is a failure-arm down when neither phase is settled (`normal-mid`, and `armed` is true). `d-settle` on the peer, or on the observer, makes the same exit a halt (`normal-settled`, `normal-self`, `armed` false). An unmatched reason is `nothing` (`unmatched`), not a successful step. A second exit is `nothing` (`exit-twice`).

`runDs` walks one `DOp` list, the same way `emitPops` walks one `Pop` list. `stepMon`, `stepExit`, `stepRecv`, `stepSend`, `stepDone`, `stepAbandon`, `stepSettle`, and `observe` do not call themselves. `observe-noted` in Agda says that any meeting with `noted ≡ true` observes to `nothing`. The book does not state that quantification. A premise `{noted ≡ true}` does not refine the match on the meeting, so the `true` branch is not `refl` for an arbitrary `Meet`. `down-again` is the closed schedule.

The fingerprint on a death line is still heap length, live cells, and process count. These schedules start from one live cell and two processes, and they stay `h1l1p2`. The flags are the equations above.

### Departures from muro 0.21.0

The OTP image in muro 0.21.0 (`Muro.Emit.Otp` at tag `v0.21.0`) is the behaviour this meeting follows. These are the places it does not.

- There is no `may fail` syntax, no Elixir module, and no fsm `down/1`. The monitor is a runtime step.
- The failure arm is the one transition that sets `armed` and emits `tr-down`. It does not `drive` a protocol skeleton. There is no continuation term.
- An unmatched reason is `nothing`. OTP stops `{:shutdown, {:unexpected, reason}}`. This meeting has no exit term and no supervisor to stop into.
- The stored reason is the `Why` the step was given. OTP rewrites `:kill` to `:killed` before the arm sees it. Callers of this step pass `killed` when that is the reason they mean. There is no second spelling.
- There is no `{:muro_halt, _}` message apart from abandon. `d-abandon` is the halt. OTP also treats `{:shutdown, :abandon}` as a halt before that message arrives. A later exit is refused, because an exit is once.
- There is no `{:muro_settled, _}` token. `d-settle` sets the phase. `:normal` is a halt when either phase is settled, and a failure-arm down when neither is and the peer is not `done`.
- `d-done` is a halt even if the phase is not settled, and even when the later exit reason is `killed`. That is this meeting's reading of "no death after done". OTP's `role dead` is the early stop, not `done` or protocol `stop`.
- `d-exit` sets `dead` before the arm, and `d-recv` still delivers the inbox before `tr-down`. Messages already in the inbox are the ones that arrived before the down. This meeting does not keep a second BEAM mailbox, and it does not drop a queued message. The checker's drop-from-queue run is not a step here. The OTP image does not take that run either.
- `d-send` models only the consumed put. It is `nothing` on the halt path, where `dead` is false. OTP's `peer_dead` is the failure mark, not the halt mark. A successful enqueue is still the existing send.
- One monitor and two processes. A third process, a monitor set, credit, and acks are not in this meeting.
- The steps are not `PStep`. `no-stray-reply` does not quantify over them. `d-done` sets the state and the halt flag. It does not run `done1`, so it does not clear roots.
- This is not a runnable VM. There is still no emitter, no image, no loader, no scheduler for an arbitrary program, no CLI, and no I/O.

## Names

| Agda | Book | Why |
| --- | --- | --- |
| `ω` | `omega` | ASCII constructor. |
| `gradeω` | `gradeOmega` | ASCII, and distinct from the `BeamGrade` constructor. |
| Grade values `g0`, `g1`, `gω` | `grade0`, `grade1`, `gradeOmega` | `MuroBeam.Boundary` already renames muro's values so `BeamGrade` can own `g0` and `g1`. |
| `suc↑` | `suc-up` | ASCII. |
| `t[]` | `tnil` | ASCII. `[]` is `nil` in this checker. |
| `Σ ℕ (λ n → GTm n)` | `Scoped` | A constructor keeps the scope. |
| `inBoundary?`, `noEscape?` | `inBoundary`, `noEscape` | `?` is a hole. |
| `inBoundary→noEscape` | `inBoundary-to-noEscape` | ASCII. |
| `PTm`'s `done` | `pdone` | One constructor namespace. `PState`'s `done` keeps the name. |
| `send` | `sendRoot` | `PTm` already binds `send`. |
| `deref` at mode `run` | `deref` | The book has no `Mode`. Spec and evidence are not operations. |
| `spend-ω` | `spend-omega` | ASCII. |
| `lower` | `le-lower` | ASCII. `≤-step` is `le-step`. |
| `Lower.lower` | `lowerTm` | `le-lower` already binds the `Le` step. |
| `≡ᵇ` | `natEq` | ASCII. The 0/1 addend in `count` is `bump`. |
| `Spent` parameter | index of `Spent` | A data parameter is elaborated as `Type`. |
| `go` | `markGo` | `Code` already binds `go`. |
| tail used twice in `go` | `markIfAt` | A computed list is affine. The `+` is on the parameter that reads the list again. |
| `recv` | `recvRoot` | `PTm` already binds `recv`. `recv1` is the process-layer step. |
| `PStep*`'s `pdone` | `pstop` | `PTm` already binds `pdone`. |
| `Meet`'s `mt` | `meeting` | `Frame` already binds `mt`. |
| `takeMail` copies the ref onto the roots | the inbox loses the message and the roots stay | `Kept` inside `Ref` is affine. The event is the one use. |
| protocol tag | `tag` | ASCII binder. The `+` is host reuse, not a `BeamGrade`. |

## Where 0.20.33 stops

These are checker limits. The Agda statements are not weakened to fit them, and nothing is postulated.

- A data parameter is elaborated as `Type`. `data InB (n : Nat) (ctx : Vec Grade n) : GTm n → Type` fails with `cannot convert Nat ≡ Type`.
- A later index whose type depends on an earlier index value is not instantiated. `Π (n : Nat) → GTm n → Type` fails with `cannot convert n ≡ n` on a constructor that looks well-typed. `InB` and `NoEsc` are indexed by one `Ix` value, `ix n ctx term`. `At`, `NoG1`, and `Pred` use the same package. Closed `inBoundary-to-noEscape` is still `Π (e : GTm 0) → InB (ix 0 vnil e) → NoEsc (ix 0 vnil e)`.
- The positivity walk unfolds a recursive function until the fuel is gone, then reports the field as not strictly positive. A constructor therefore cannot store `{isZeroGrade (vlookup …) ≡ false}` or `{g1InScope ctx ≡ false}`, and an index cannot call `predGrade`. The premises are the relations `At` (lookup), `NotZero` (the grade is not `grade0`), `NoG1` (no grade-1 binder), and `Pred` (the match predecessor). `notZero-sound`, `notG1-sound`, and `noG1-sound` are checked proofs that those relations imply the boolean facts. The other direction, from the boolean equality back to the relation, is not proved: the `grade0` branch would need to eliminate `{true ≡ false : Bool}`, and this checker has no such elimination. A direct `At` to `vlookup` lemma was tried. The successor case sticks, because one unfolding of `vlookup` is a `vlookup` on `vtail (vcons …)` and that application does not convert with the tail variable. That lemma is not in the book. The relation is the premise the proofs use.
- A motive on an indexed family is checked by inferring its codomain. The literal `Type` in that position fails with `Type has no type (no Type : Type)`. An unindexed family's motive is checked as a kind, so `(λ _ → Type)` is accepted there, as in `noG1-sound`. `glamSharp` therefore does not match on `GTm` to compute a type. `isLam` returns `Bool`, and `CapRes` is indexed by that boolean together with the context. `packLam` and `fromCap` extract the `NoG1` that `ib-lam` already stores.
- `data Spent (c : Grade) : Type` fails with `cannot convert Grade ≢ Type`. `Spent` is indexed by the checked grade. The index is still the checked grade of the result.
- There is no elimination of `{false ≡ true : Bool}`. That is why `Grade1Unique` is not stated as `hasG1 i rs ≡ true → count i rs ≡ 1`. The nil case is the absurd equation.
- There is no inversion of `Maybe`. A premise `{spendRef r ≡ just r'}`, `{rootAt s i j ≡ just r}`, or `{reuse s i j g v ≡ just t}` does not refine `r` or `t`. The book states the shapes that reduce, and it states `alloc-ordered` and `reuse-ordered` for the heap operations those steps perform.
- A `match` motive that ignores its argument leaves a `poke` or an `append` stuck on a variable index, so the branch type does not convert. The motive has to mention the index, as `pokeOrd` does. This is how the ordered proofs are written. It is not a missing lemma.

Part 4 is the receive, spawn, scheduling, `trip`, running refusal, and emission above. Peer death is the monitor, the down, and the failure arm in the section of that name. The MAlonzo comparison is the lines under "What this part does not claim". The totality rule is unchanged. `runDs` is structural on the `DOp` list.
