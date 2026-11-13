# Runtime as a Muro book

The Agda model in `agda/` is the proof. The book in `book/` is the artefact the muro wall checks, and the artefact later parts will emit. This document is the plan for that book.

Part 1, merged as PR #6, is the boundary mirror, the runtime data, this plan, the smoke, and the CI job. Part 2 is this book. It runs `alloc`, `deref` / `spend`, `send`, and `reuse`. It checks the residual and grade-1 facts the wall can express, and the smoke pins both the accepted steps and the refusals. It does not emit events, it does not run a CEK step, and it does not compare traces with Agda.

Ricardo approved the plan on 2026-11-12, with the four amendments below, and approved part 2 the same day after PR #6 merged.

## What this part does not claim

This book is not the executable image of the proved specification. That phrase waits on a conformance test that does not exist yet. The test will run this book and the Agda model, compiled with the MAlonzo / GHC backend, on the same `InBoundary` examples and compare traces event by event. Part 1 records the shared examples and the event format. Part 2 does not build MAlonzo, it does not emit a runner, and it does not add a GHC job. The heap steps return `Maybe Sys`. They do not emit `Event`.

The boolean checks and the proof predicate are not proved equivalent in general. `once` is accepted by `inBoundary` and inhabits `InB`, and `inBoundary-to-noEscape` sends that proof to `NoEsc`. `cex` is refused by the boolean check. A theorem that `inBoundary t ≡ yes` if and only if an `InB` proof exists is not in this book.

Part 2 is also weaker than Agda where the checker cannot state the Agda theorem. The Agda text is unchanged. Nothing is postulated.

- Agda's `grade0-not-dereferenced` assumes `rootAt s i j ≡ just r` and `residual r ≡ g0`. The book checks the shape that reduces: process 0, root 0, residual `pt (fin 0)`, in `grade0-not-dereferenced`. An arbitrary `Maybe` is not inverted.
- Agda's `spendRef-obj` and `spendRef-checked` follow from `spendRef r ≡ just r'`. The book proves the finite, `omega`, and `iv` shapes (`spendRef-finite`, `spendRef-omega`, `spendRef-iv`). `spendRef-finite` packages the object index and the checked grade.
- Agda's `Grade1Unique` is `∀ i → hasG1 i rs ≡ true → count i rs ≡ 1`. The empty-list case is `{false ≡ true}`, which this checker does not eliminate. The book pins `{count ≡ suc 0}` and `{hasG1 ≡ true}` on the alloc, deref, send, and reuse examples. `send-g1-moves` is the move for a checked `g1` root of process 0 sent to process 1, heap unchanged. It is not the quantified count preservation in `MuroBeam.Unique`.
- Agda's `send-preserves-residual` concludes `AllInv (refsOf t)` from `send ≡ just t`. Every book `Ref` already stores `Kept` (`ref-inv`). Send moves or copies that `Ref`. The book does not invert `{sendRoot ≡ just t}`.
- `alloc-ordered` is `OrdAt` for the heap append `alloc` performs. `reuse-ordered` is `OrdAt` for the `poke` `reuse` performs. Agda's `reuse-ordered` is the implication from `reuse ≡ just t` together with `Ordered (heap s)`. The examples pin the boolean as well (`alloc-ordered-bool`, `reuse-ordered-bool`). Agda's `Ordered` is a function of `lookup`. `OrdAt` is the list spine, which is the form this checker indexes.

## Four amendments

### 1. The book and the Agda model meet in a conformance test

The link is a test, not a slogan. Both sides will be run on the same closed terms. Until the traces match, docs do not call the book an executable image.

Shared examples, encoded in `book/smoke.muro`:

- `once` is muro's `grade-once`. Agda writes `glam g1 g0 (gvar fzero)`. The book writes `glam 0 grade1 grade0 (gvar (suc 0) (fzero 0))`. The extra `Nat` is the scope. `fzero 0` is de Bruijn 0 at scope 1.
- `cex` is the §2B term from `MuroBeam.Example`. Agda writes `glam g1 g0 (gapp (glam gω g0 (gapp (gvar fzero) (gvar fzero))) (glam aff g0 (gvar (fsuc fzero))))`. The inner application sits at scope 2. `fzero (suc 0)` is the inner binder. `fsuc (suc 0) (fzero 0)` is de Bruijn 1, the outer grade-1 binder.
- `ghost`, `glam g0 g0 (gvar 0)`, is the witness that the converse fails. `inBoundary` returns `no` and `noEscape` returns `yes`. Agda does not claim the converse either.

`book/trace.muro` fixes the event datatype. A later part emits `List Event` from both sides.

| Event | Fields |
| --- | --- |
| `tr-alloc` | object index, checked grade |
| `tr-spend` | object index, residual before, residual after |
| `tr-send` | source pid, destination pid, reference, `Kmove` or `Kcopy` |
| `tr-recv` | pid, reference |
| `tr-spawn` | parent pid, child pid |
| `tr-step` | pid. One CEK step. Control before and after is a later field. |
| `tr-collect` | freed object indices, in increasing order |

`tr-` keeps these names off the process-term constructors. The heap operations do not build a trace. Emission is part 4.

### 2. Two kinds of grade

Runtime residual grades and checked grades are ordinary inductive data: `BeamGrade` (`g0`, `g1`, `omega`) and `beamGrade`, the same reading as `MuroBeam.Boundary`, plus muro's `Grade` (`pt`, `iv`) as values `grade0`, `grade1`, `gradeOmega`, and `aff`. `Kept` is residual ≤ checked, also as data.

Muro's own graded binders, written on this book's source, are type-level evidence. Emitters erase them. The wall checks them the way it checks any other Muro book. They are not `BeamGrade` and they are not stored in a `Ref`.

A `+` on a `Nat`, a `Grade`, a `GTm`, a `Vec`, a `Ref` index, a `Sys` field, or an `OrdAt` index is the host's reuse quantity, so a walker or a proof can read the field twice. It is not a runtime grade. The two roles are not mixed.

### 3. Refusal belongs to the book's check

Out-of-boundary refusal is `inBoundary` and `noEscape`, total `run` functions. It is not the muro type checker rejecting a client term. `once` and `cex` are both well-typed `GTm 0` values. `boundary-accept` is `{inBoundary once ≡ yes}`. `boundary-refuse` is `{inBoundary cex ≡ no}`. The same shape is checked for `noEscape`. `mix muro.check` fails if those results flip.

The functions return `Answer` (`yes` or `no`), not a proof-carrying `Dec`. `refl` is refused in `run` mode, so a `run` cannot build the `yes` proof. The proof predicate is separate, and `inBoundary-to-noEscape` is evidence.

The same rule covers the heap. A refused `deref` of a `g0` residual, a refused `send` of a `g0` checked grade, a refused second `spend` of a spent `g1`, a refused `reuse` of an unspent root, and a refused `reuse` of two spent references are `nothing` from the `run` function. `book/run.muro` witnesses the results. `mix muro.check` fails if they flip.

### 4. Totality, decided here

Later parts follow this rule.

- Terms are an inductive datatype, a pure mirror of `GTm` and `PTm`.
- Every primitive operation is one `run` function, structurally recursive on its inputs: `alloc`, `deref` / `spend`, `send`, `recv`, `spawn`, one CEK step, and total ordered `collect`. No termination pragma. No hand-written well-founded recursion.
- Multi-step evaluation is driven from outside. Either an explicit fuel argument, `runFor fuel state`, or an external scheduler that applies one process step at a time, in the style of Agda's `PStep`.
- No internal unbounded loop.

`inBoundary` and `noEscape` follow the rule: they recurse on the term, and they take no fuel. `alloc`, `deref`, `sendRoot`, and `reuse` follow it too. Each is one `run`, structurally recursive on a list, a grade proof, or a `Nat`. `recv`, `spawn`, one CEK step, and `collect` are later parts.

## Four parts

| Part | Contents |
| --- | --- |
| 1 (merged, PR #6) | Boundary mirror, runtime data, this plan, smoke, CI. |
| 2 (this book) | `alloc`, `deref` / `spend`, `send` that moves a finite grade and copies `omega`, and `reuse`. Residual and grade-1 evidence the checker can express. Smoke for the accepted steps and the refusals. |
| 3 | One CEK step, and total ordered `collect`. |
| 4 | `recv`, `spawn`, scheduling. An in-boundary example that runs. The out-of-boundary example refused by this book's check. Emission. The conformance comparison, when the MAlonzo build is ready. |

## Two pins

The Agda model still imports `vendor/muro` at v0.20.32 (`792497695ef3b0dd37fe2b262f6225c989eb6818`). That pin is not bumped. The book is checked with muro 0.20.33 from Hex. 0.20.33 adds CSHRL synthesis on top of 0.20.32. This book does not use CSHRL. Part 2 stays on 0.20.33. The published releases 0.20.34 through 0.20.36 add synthesis and kernel `Bytes` / `Slice`. They do not remove the checker limits below, so the pin is not bumped.

`make book` runs `mix muro.check book/smoke.muro`. That file imports the rest, and the checker flattens imports, so one check covers the book. CI installs the pinned archive. It does not fetch the Agda standard library.

## What the book defines

| File | Contents |
| --- | --- |
| `book/data.muro` | `Bool`, `Maybe`, `Answer`, `List`, `Fin`, `Vec`, `Le`, `leRefl`, `le-lower`, `vlookup`, `lt`, `natEq`, `append`, `lookup`, `update`, `removeAt`. Local, so `std:list`'s `Or` (`yes` / `no`) does not clash with `Answer`. |
| `book/grade.muro` | `Point`, `Grade`, `BeamGrade`, `beamGrade`, `isZeroGrade`, `isG1`, `g1InScope`, `kind`, `Kept`, `selfKept`, `spend`, and the inductive premises below. |
| `book/term.muro` | `GTm`, `Scoped`, `predGrade`, `Pred`. |
| `book/boundary.muro` | `Ix`, `InB`, `NoEsc`, `toNo`, `inBoundary-to-noEscape`, `inBoundary`, `noEscape`. |
| `book/heap.muro` | `Status`, `Ref`, `Val`, `Obj`, `ordered`, `Below`, `OrdAt`, `spendRef`, `count`, `hasG1`, `alloc-ordered`, `reuse-ordered`. |
| `book/process.muro` | `PState`, `Msg`, `Thin`, `PTm`, `Flight`, `Code`, `Frame`, `Ctl`, `Proc`, `Sys`. |
| `book/ops.muro` | `alloc`, `deref`, `sendRoot`, `reuse`, `refsOf`. |
| `book/trace.muro` | `Event`, `Trace`. The operations do not emit these. |
| `book/run.muro` | Checked alloc, deref, send, and reuse examples, including the refusals. |
| `book/smoke.muro` | `once`, `cex`, `ghost`, the part-1 results, and the import of `run.muro`. |

`beamGrade` reads `pt (fin 0)` as `g0`, `pt (fin 1)` as `g1`, `pt inf` as `omega`, and every `iv`, including `aff`, as `omega`. `pt (fin n)` for `n ≥ 2` is `nothing`. The checked equations are `beam-g0`, `beam-g1`, `beam-omega`, `beam-iv`, and `beam-fin2`. `kind` is the same three send behaviours: `g0-not-sent`, `g1-moved`, `omega-copied`, `iv-copied`.

`inBoundary` refuses a `glam` when the sharp flag is true, and a `gvar` whose binder is grade 0. A `gpi` body is scanned. Uses are not counted. The flag starts false on the empty context and is pushed with `orB sharp (isG1 c)`, the same boolean as `g1InScope`. `noEscape` is the same walk with every `gvar` accepted. `inBoundary-to-noEscape` says the filter implies the capture restriction. The converse is not a theorem. `ghost` is the boolean witness, and `ghost-noesc` inhabits `NoEsc` for that term.

`Ref` stores an object index, a checked grade, a residual grade, and a `Kept` proof. `selfKept` builds the reflexive proof. `Val` is `nat`, `suc-up`, or `clo` of a captured `List Ref` and a `Scoped` term. `Obj` is a payload and `live` or `free`. `ordered` is the boolean walk. `OrdAt` is the proof-carrying spine: the cell at index `i` has children below `i`. Agda states `Ordered` as a function of `lookup`. The list induction is the form muro indexes directly. `heap-nil`, `heap-nat`, `heap-bad`, and `heap-link` pin the boolean. A successor that points at its own cell is `false`. A successor that points at a lower cell is `true`. `ordered-nil` and `ordered-nat` inhabit `OrdAt`.

`Proc` is pid, state, roots, inbox, control. The inbox is the mailbox. `Msg` holds a `Ref`. `PState` is `ready`, `waiting`, `done`. `Ctl` is `idle`, `ev`, `rv`, or `pr`. `Frame` is `ar`, `fn`, `su`, `mt`, `bd`, or `saved`. `PTm` has the Agda constructors, with `done` spelled `pdone`.

`spend` steps a `Kept`. A finite residual `pt (fin (suc k))` becomes `pt (fin k)` by `le-lower`, and the checked grade stays. `g0` is `nothing`. `omega` and every `iv` stay. `spendRef` rebuilds the `Ref`. `alloc` appends a live `nat` cell. The fresh index is `length` of the heap, and the new root is `selfKept`. `deref` is Agda's run-mode deref: look up the root, `spendRef` it, write it back. `sendRoot` is Agda's `send`. `kind` of the checked grade decides. `isZeroGrade` of the residual refuses. A finite point, including `g1` and `pt (fin n)` for `n ≥ 2`, moves: the root leaves the sender and is enqueued on the receiver. A self-send posts on that same process after the drop. `omega` and every `iv` copy: the sender keeps the root and the mailbox receives the same `Ref`. The heap is unchanged. `reuse` overwrites a spent grade-1 slot in place when `count` of that object in `refsOf` is 1. `refsOf` counts roots, mailbox messages, heap edges, and control references, so an in-flight message counts. `recv`, `spawn`, the CEK stepper, and `collect` are not in this book.

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
| `≡ᵇ` | `natEq` | ASCII. The 0/1 addend in `count` is `bump`. |
| `Spent` parameter | index of `Spent` | A data parameter is elaborated as `Type`. |

## Where 0.20.33 stops

These are checker limits. The Agda statements are not weakened to fit them, and nothing is postulated.

- A data parameter is elaborated as `Type`. `data InB (n : Nat) (ctx : Vec Grade n) : GTm n → Type` fails with `cannot convert Nat ≡ Type`.
- A later index whose type depends on an earlier index value is not instantiated. `Π (n : Nat) → GTm n → Type` fails with `cannot convert n ≡ n` on a constructor that looks well-typed. `InB` and `NoEsc` are indexed by one `Ix` value, `ix n ctx term`. `At`, `NoG1`, and `Pred` use the same package. Closed `inBoundary-to-noEscape` is still `Π (e : GTm 0) → InB (ix 0 vnil e) → NoEsc (ix 0 vnil e)`.
- The positivity walk unfolds a recursive function until the fuel is gone, then reports the field as not strictly positive. A constructor therefore cannot store `{isZeroGrade (vlookup …) ≡ false}` or `{g1InScope ctx ≡ false}`, and an index cannot call `predGrade`. The premises are the relations `At` (lookup), `NotZero` (the grade is not `grade0`), `NoG1` (no grade-1 binder), and `Pred` (the match predecessor). `notZero-sound`, `notG1-sound`, and `noG1-sound` are checked proofs that those relations imply the boolean facts. The other direction, from the boolean equality back to the relation, is not proved: the `grade0` branch would need to eliminate `{true ≡ false : Bool}`, and this checker has no such elimination. A direct `At` to `vlookup` lemma was tried. The successor case sticks, because one unfolding of `vlookup` is a `vlookup` on `vtail (vcons …)` and that application does not convert with the tail variable. That lemma is not in the book. The relation is the premise the proofs use.
- `capture-check-clear`, `EnvGrades`, and `anyG1` are not in this part. They belong with the machine steps.
- `data Spent (c : Grade) : Type` fails with `cannot convert Grade ≢ Type`. `Spent` is indexed by the checked grade. The index is still the checked grade of the result.
- There is no elimination of `{false ≡ true : Bool}`. That is why `Grade1Unique` is not stated as `hasG1 i rs ≡ true → count i rs ≡ 1`. The nil case is the absurd equation.
- There is no inversion of `Maybe`. A premise `{spendRef r ≡ just r'}`, `{rootAt s i j ≡ just r}`, or `{reuse s i j g v ≡ just t}` does not refine `r` or `t`. The book states the shapes that reduce, and it states `alloc-ordered` and `reuse-ordered` for the heap operations those steps perform.
- A `match` motive that ignores its argument leaves a `poke` or an `append` stuck on a variable index, so the branch type does not convert. The motive has to mention the index, as `pokeOrd` does. This is how the ordered proofs are written. It is not a missing lemma.

`recv`, `spawn`, the CEK stepper, and `collect` are later parts, under the totality rule above.
