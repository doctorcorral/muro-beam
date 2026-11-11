# muro-beam design

muro-beam executes muro *run* images as processes, in the spirit of the Erlang BEAM: lightweight actors, mailboxes, and a wall between what a book proved and what the host steps at runtime.

v0 is a total Agda book of the scheduler, the graded heap, and send. v1a is that runtime plus a CBV CEK that runs a closed `GTm` muro's `decide run` has accepted. It does not emit code. It does not re-check a muro term. It reads the grades muro's judgment already checked. Boundary v1, in `MuroBeam.Boundary`, is the contract over that machine. The machine is the implementation.

`main` at `079ca47` is tagged `v0`. v1 is three pull requests. This book is the first of them.

## Why

muro separates run, spec, and evidence, and it emits only run terms. The current backends erase binder grades and leave allocation to the host.

A VM that wants to look like BEAM without giving up muro's wall needs those facts. It should drop a value that is never used, move a value that is used exactly once, and keep a value that may be used many times, without re-proving the book at run time.

Grades land in [murolang/muro](https://github.com/murolang/muro) as evidence on the mode-indexed judgment. muro-beam is the runtime that is allowed to read them. v0 imports the lattice from that book. It does not copy it.

## What v0 contains

A `--safe` Agda model:

- processes, mailboxes, and a one-step scheduling relation
- a shared heap whose roots carry a checked grade and a residual computational grade
- a total `collect`
- send that transfers ownership of a grade-1 value
- the theorems named below

The modules are `MuroBeam.Grade`, `MuroBeam.Heap`, `MuroBeam.Process`, `MuroBeam.Collect`, `MuroBeam.Unique`, and `MuroBeam.Example`. v1a adds `MuroBeam.Source` and `MuroBeam.Lower`. Boundary v1 adds `MuroBeam.Boundary`. `MuroBeam.Lib` holds a few natural-number and list lemmas so the book does not import the large `Data.Nat.Properties` development. `MuroBeam` re-exports the book. `MuroBeam.Unique` holds grade-1 uniqueness and the proofs that `Step` preserves it.

The grade lattice is the submodule `vendor/muro`, pinned at murolang/muro tag `v0.20.32` (commit `792497695ef3b0dd37fe2b262f6225c989eb6818`). Agda is invoked with `--no-libraries` and include paths `agda`, `vendor/muro/agda`, and `vendor/agda-stdlib/src` (stdlib v2.3). Checking the book typechecks `Muro.Grade` and the modules it imports (`Muro.Base`, `Muro.Syntax`, `Muro.Subst`, `Muro.Env`, `Muro.Arrow`). It does not typecheck `Muro.Soundness` or the rest of the muro library.

## Process and mailbox

Ordinary inductive types.

```agda
data PState : Set where
  ready   : PState
  waiting : PState
  done    : PState

data Msg : Set where
  msg : Ref → Msg

record Proc : Set where
  field
    pid   : ℕ
    state : PState
    roots : List Ref
    inbox : List Msg

record Sys : Set where
  field
    heap  : List Obj
    procs : List Proc
```

`pid` is the process's index in `procs`. A mailbox is a list of messages. A message carries one reference, which is an ownership token for a heap object. v0 does not spawn, exit, or restart processes. `waiting` and `done` are part of the type. No step in v0 enters them: an empty receive is simply not a step.

The references of a system are every process root together with the reference inside every mailbox message. In-flight messages count as references for collection and for grade-1 uniqueness.

## Scheduling

```agda
data Step : Sys → Sys → Set
```

`Step` is a one-step relation. A step is one of: dereference a root in **run** mode, send, receive, allocate, reuse a spent grade-1 slot in place, or `collect`. The relation says that some process takes that step. It does not say which process runs next, and it does not say that every process eventually runs.

There is no fairness theorem.

## Graded heap

The heap is a list of objects shared by every process. An object is a scalar payload and a status.

```agda
data Status : Set where
  live free : Status

record Obj : Set where
  field
    payload : ℕ
    status  : Status
```

In v0 a payload was a natural number and an object did not contain pointers, so "reachable" meant "pointed at by a root or a mailbox message". v1a replaces that payload with `Val` (`nat`, `suc↑`, `clo`). The ordered tracing collector is described in the v1 section. The reference record is unchanged.

A reference stores the object index, the grade muro checked, and the residual computational grade (the checked grade minus the uses so far):

```agda
record Ref : Set where
  field
    obj      : ℕ
    checked  : Grade
    residual : Grade
    kept     : Kept residual checked
```

`Grade` is `Muro.Grade.Grade` (`pt` / `iv`, with points `fin n` and `inf`). The names `g0`, `g1`, and `gω` are muro's.

`Kept residual checked` is the v0 form of "residual ≤ checked":

- both are finite points `fin k` and `fin n` with `k ≤ n`
- both are `gω`
- both are the same interval

`kept→≤ᵍ` shows that `Kept` implies muro's boolean order: `(residual ≤ᵍ checked) ≡ true`.

Every reference carries `Kept`, so the inequality is an invariant of the representation. The operations that build references (allocation, reuse, and `spend`) construct a `Kept` proof. Send and receive move or copy an existing reference, so they do not change the pair.

How a use updates the residual:

- Finite point. A residual `fin (suc k)` becomes `fin k`. The new residual is still `≤` the checked point. A residual `fin 0` (that is, `g0`) cannot be used.
- `gω`. The residual stays `gω`. The root is kept alive.
- Interval. The residual stays that interval. The root is kept alive. v0 does not tighten an interval and does not free one.

Allocation stores `residual = checked` for any grade, which is allowed by reflexivity of `Kept`.

## Collect

`collect : Sys → Sys` is a total function. Under `--safe` that type is the totality proof. `collect-total` is the same fact as an existence lemma.

`collect` walks every reference.

- A reference whose residual is the point `g0` is dropped from its root list or mailbox.
- Any other reference is kept. That includes `gω`, every interval (including a degenerate `[0, 0]`), and every positive finite point.
- A heap slot that is still pointed at by a kept reference stays in place, with its payload, and is marked live.
- Every other slot is marked free and its payload is cleared.

Grade 1 is a unique reference (below). After the single use, its residual is `g0`, so the next `collect` frees the slot. `reuse` may instead overwrite that slot in place, without waiting for `collect`, when the checked grade is `g1`, the residual is `g0`, and the object has exactly one reference.

## Ownership transfer on send

Send classifies the **checked** grade.

- Point `g0`. Refused. The residual of a `g0` reference is `g0`, which is not usable in run mode.
- Finite point `fin (suc n)`, including `g1`. **Move.** The reference is removed from the sender's roots and appended to the receiver's mailbox. Checked grade and residual are unchanged. The remaining budget travels with the value. This is ownership transfer, not a second copy, and it is not scaled by another binder grade.
- `gω`, or any interval. **Copy.** The sender keeps its reference and the receiver's mailbox gains an alias with the same grades. The residual is not decremented. These roots stay alive. Copying is refused for `g1`.

Receive pops one message and installs that same reference as a root. The number of references to the object does not change.

A grade-1 send therefore removes the value from the sender's roots. The object still has exactly one reference: the message, then the receiver's root.

## Theorems

The names below are the names in the Agda book.

- **`collect-total`**. `collect` is a function `Sys → Sys`. It is accepted with `{-# OPTIONS --safe #-}` and with no `TERMINATING` pragma.
- **`collect-safe`**. If a root or an in-flight message points at object `i` and its residual is not the point `g0`, and slot `i` exists, then `collect` leaves that slot in place and live. Informally: collect never frees an object reachable from a live root whose residual is still positive.
- **`collect-frees-zero`**. If no reference to slot `i` has a residual other than `g0`, `collect` frees the slot.
- **`kept→≤ᵍ`**. `Kept residual checked` implies `(residual ≤ᵍ checked) ≡ true` in `Muro.Grade`.
- **`residual-inv-step`**. After any `Step`, every reference in the resulting system satisfies `residual ≤ᵍ checked`.
- **`send-preserves-residual`**. A successful send moves or copies the sender's reference. The residual and the checked grade on that reference are unchanged, so the inequality still holds. Dereference is the operation that changes a residual, and `spend-finite`, `spend-ω`, and `spend-iv` describe it: a finite residual decreases by one, and `ω` and intervals stay put.
- **`grade1-unique`**. If any reference to object `i` has checked grade `g1`, then `i` occurs exactly once among all roots and mailbox messages.
- **`step-preserves-grade1`**. Every `Step` preserves `grade1-unique` (and the bound that every reference index lies in the heap).
- **`send-g1-moves`**. Sending a reference whose checked grade is `g1` and whose residual is not `g0` removes that occurrence from the sender and enqueues it on the receiver. The number of references to the object is unchanged.
- **`grade0-not-dereferenced`**. In run mode, if the selected root has residual `g0`, then `deref` returns nothing. There is no run-mode dereference step of a grade-0 residual. This is the runtime side of muro's refusal to promote an erased variable (`grade-erased-first` in `Muro.Grade`). Spec and evidence are not run modes: `deref` on those modes is nothing as well.

`reuse-in-place` records the justification for overwriting a slot: a successful reuse targets a checked `g1` root whose residual is already `g0` and whose object has exactly one reference.

## Worked trace

`MuroBeam.Example` is a checked trace on a two-process system.

- Allocate a `g1` cell, dereference it once, and `collect`. The residual becomes `g0` and the slot is freed.
- Reuse that spent `g1` slot in place. The same index receives a new payload and a fresh residual.
- Allocate a `gω` cell, dereference it, and `collect`. The residual stays `gω` and the slot stays live.
- Allocate an interval cell and dereference it. The residual stays the interval.
- Allocate `g0` and dereference it in run mode. `deref` is nothing.
- Allocate `g1` on process 0 and send it to process 1. Process 0's roots no longer contain it. Process 1's mailbox does. The object still has one reference. Receive moves that reference into process 1's roots.

## v1

v1 reads a closed `GTm` that `decide run []` accepts and runs it on the v0 heap. The pin stays murolang/muro `v0.20.32`. There is still no `erase : Tm → GTm` in that pin, so the machine never sees a core `Tm`. Application stays additive, as recorded below from murolang/muro#211. v1 does not add multiplication.

Ricardo split v1 into three pull requests. Each one is meant to check alone.

| PR | What it adds | What it leaves |
|---|---|---|
| **v1a** (this book) | `Checked`, CEK lowering, reference payloads, ordered tracing `collect`, safety of every reachable state | processes that spawn |
| **v1b** | `PTm`, `checkP`, `lowerP`, spawn / send / recv lowering, `waiting` on an empty mailbox | adequacy and simulation |
| **v1c** | `NoEscape`, `noEscape?`, `decide-sound`, `budget-adequate`, `exact-exhausts`, `done-collect-empty`, `MuroBeam.Ref`, `lower-sim` | a multiplicative application rule, and `erase` |

v1b and v1c are not in this book. The names above are the ones those PRs are expected to add. Nothing here postulates them.

### Input

`MuroBeam.Source` defines the input of v1a:

```agda
record Checked : Set where
  field
    term : GTm 0
    ok   : decide run [] term ≡ ok []
```

Run mode only. Spec and evidence terms are not lowered.

`decide-sound`, `NoEscape`, and `noEscape?` are v1c. v1a does not need them. A checked grade `g0` forces the residual to be `g0` (`Kept`), and `spend` refuses a `g0` residual, so no run step dereferences that binder. `gtyp` and `gpi` never call `spend`.

### Control

`Proc` gains `ctl : Ctl`. A v0 process that is not running code holds `idle`. A lowered program holds

```agda
ev term [] []
```

`Ctl` is a CEK state.

- `ev` is a `GTm` closure: the term, an environment `List Ref` indexed by de Bruijn index, and a continuation.
- `rv` is a returned value. The value is a `Ref`. The environment is threaded, so a spend inside a scrutinee is visible to the rest of the term.
- Frames hold `Ref`s only where a value has to live across a sub-computation (`fn` holds the function; `bd` holds the caller environment while a body runs). Argument terms and match branches are syntax, not references.

`eval1` is one CBV step of one process. It is a partial function (`Maybe`). `Step` gains `step-eval` beside deref, send, recv, alloc, reuse, and collect. `GTm` is untyped and can diverge, for example `(λω f. f f) (λω f. f f)`, so evaluation is a relation. Traces use `runFor : ℕ → Sys → Sys`, structural on the fuel.

How a term steps:

- `gvar x` is a run-mode dereference of environment slot `x`. That is v0 `spend`. A `g0` residual is not a step. A `nat` payload is copied into a fresh cell (the number itself, not a second graded reference). A `gω` or interval reference may be aliased. A second graded reference to a `g1` object is not a step.
- `gtyp` and `gpi` allocate an erased unit `nat 0` and do not dereference anything. The body of a `gpi` is not evaluated. Type-level grades stay on the checker.
- `gze` allocates a `nat 0` cell. `gsu` evaluates the predecessor, then allocates a `suc↑` cell whose child is that predecessor.
- `glam` allocates a `clo` cell. The captured environment is a list of `Ref`s. The body is stored with its scope size (`Σ ℕ GTm`). Capturing a `g1` reference would be a second graded reference to that object, so `eval1` refuses it.
- `gapp` evaluates the function, then the argument. A β step against `clo … (glam c t b)` regrades the argument reference to `checked = residual = c` and pushes it onto the closure's environment. The caller environment moves onto a `bd` frame, so it is not aliased for the duration of the call.
- `gmatch` on `suc↑` binds the predecessor at `predPair`'s computational grade, the same grade `decide` uses: the scrutinee variable's checked grade, or `aff` when the scrutinee is not a variable. The zero branch binds nothing.
- When the body returns, `bd` pops the binder reference and restores the caller environment. `collect` can then free the slot whether or not residual budget remains. A match may take a branch that uses a variable fewer times than the static max.

`lower : Checked → Sys` builds one process, pid 0, with `ev term [] []`, and an empty heap. `lower-wf` says that system is well-formed.

### Reference payloads and the ordered heap

```agda
data Val : Set where
  nat  : ℕ → Val
  suc↑ : Ref → Val
  clo  : List Ref → Σ ℕ (λ n → GTm n) → Val
```

`suc↑` stores the predecessor reference. The child index in the spec is `obj` of that reference, so the edge has a grade and is counted by `count` and `hasG1`. A `nat` has no children. A `clo` 's children are its captured references.

**Ordered.** Every child index is strictly below its parent's index. Allocation appends. No step writes an edge that points at or above its own slot. `reuse` writes a `nat`, which has no children, so it stays inside the order; `reuse-ordered` is that fact. An overwrite whose new children are not below the slot is not a step (`childrenBelow`).

The order makes the heap acyclic. `collect` is one structural pass from the highest index down: seed the marks from roots, mailboxes, environments, and frames whose residual is not the point `g0`, then, from the top, mark the live children of a reached object. No `TERMINATING` pragma. `Reach` is the corresponding inductive predicate: a live root, message, environment, or frame reference, or a live edge (or `suc↑`) out of a reached parent at a higher index. `collect-safe` says a reached slot stays live. `collect-frees-zero` says a slot that is not reached is freed and cleared.

`grade1-unique` counts every reference `refsOf` sees: roots, mailbox messages, environment slots, frame references, and heap edges.

### The additive counterexample

`decide` adds the use vectors of a function and its argument. It does not scale the argument by the grade of the binder it is substituted for. A closure that captures a grade-1 variable can be handed to a grade-ω binder, and the checker still counts the variable once.

This closed term is accepted by `decide run []`:

```agda
cex : GTm 0
cex =
  glam g1 g0
    (gapp
      (glam gω g0
        (gapp (gvar fzero) (gvar fzero)))
      (glam aff g0
        (gvar (fsuc fzero))))
```

Read as `λ(g1) x. (λ(gω) f. f f) (λ(aff) _. x)`. The inner λ captures `x`. The body of `f` is the ω binder's body `f f`: `f` is used twice, and the closure it receives reads `x`. Additively, `x` occurs once in the argument, so the outer `g1` checks. At run time a second use of that captured reference is a second graded reference, or a second `spend` of a residual that the first use already exhausted.

v1a refuses the alias. `eval1` will not install a `clo` whose environment contains a `g1` reference while that reference still lives in the caller environment. Running `gapp cex gze` therefore gets stuck at the inner λ, after `x` has been allocated at grade 1. The stuck state is well-formed. `collect` does not free `x`: its residual is still `g1`, and the environment reference reaches it. Safety holds. Adequacy does not, and is not claimed. That is the runtime face of the #211 choice. It is not a bug in either repository.

`NoEscape` (v1c) is the fragment in which this pattern is excluded and a checked program is not supposed to get stuck on a grade. v1a proves safety for every lowered program, including this one.

### Theorems added in v1a

- **`lower-wf`**. `WF (lower e)`. Bounds hold and grade 1 is unique. The heap is empty.
- **`lower-safe`**. `Step* (lower e) s` implies `WF s` and `AllInv (refsOf s)`. Collect-safety and grade-1 uniqueness apply to every state reachable from a checked program.
- **`lower-g0-never-deref`**. A reference whose checked grade is `g0` has residual `g0`, and neither `deref` nor `eval1` spends it. `gtyp` and `gpi` do not read the environment. The checker side of the same fact is `sat g0 (finᶜ 0)` and `erased-is-zero`; connecting those to a trace is `decide-sound` in v1c.
- **`reuse-ordered`**. A successful `reuse` preserves the ordered-heap invariant.
- **`residual-inv-step`**, **`collect-safe`**, **`collect-frees-zero`**, **`grade1-unique`**, **`step-preserves-grade1`**. The v0 statements, now over `refsOf` extended with environments, frames, and heap edges, and over `Reach` for the tracing collector.

Every v0 theorem name is still in the book. `grade0-not-dereferenced`, `send-preserves-residual`, `send-g1-moves`, `kept→≤ᵍ`, `collect-total`, and `reuse-in-place` are unchanged in force. `send-g1-moves` and `reuse-in-place` count the extended reference list: a grade-1 send still moves the only reference, and a successful reuse still requires that the object occur once.

## Boundary v1

`MuroBeam.Boundary` is boundary v1. The constant `boundary-version` is `1`. It is the contract a program targeting muro-beam relies on. `Heap`, `Process`, `Collect`, and `Lower` are the implementation. The boundary re-exports that implementation. It adds no typing judgment. `vendor/muro` stays at `v0.20.32`. Application stays additive: `decide` on `gapp` is `addU`, as recorded above from murolang/muro#211.

The import arrow runs from `Boundary` into the v1a modules. Those modules do not import `Boundary`. Each of them is part of what the boundary re-exports, and the other direction is a cycle. `MuroBeam.Example` is the client. It imports `Boundary` and computes `inBoundary?` on muro's `grade-once` and on the §2B term. The umbrella imports `Boundary` and hides the re-exported v1a names, so each existing theorem stays a single binding.

### Grades

`BeamGrade` has three constructors: `g0`, `g1`, and `ω`. `beamGrade` reads a `Muro.Grade.Grade` as one of those, or as nothing. The reading is what v0 and v1a already do. It is not a second lattice. `kind`, `spend`, and `isZeroGrade` are the v1a functions, and they pattern-match on muro's own `Grade`.

- **`pt (fin 0)`**, muro's `g0`. `beamGrade` returns `g0`. `kind` is `nothing`, so send is refused (`g0-not-sent`). `spend` refuses a use. `collect` drops a residual that is this point.
- **`pt (fin 1)`**, muro's `g1`. `beamGrade` returns `g1`. `kind` is `Kmove` (`g1-moved`). `grade1-unique` is the uniqueness theorem.
- **`pt inf`**, muro's `gω`. `beamGrade` returns `ω`. `kind` is `Kcopy` (`ω-copied`). `spend-ω` leaves the residual. `isZeroGrade` is false, so `collect` keeps the root.
- **`iv a b`**, including muro's `aff`. `beamGrade` returns `ω` (`beam-iv`). This is an alias of that keep-alive behaviour, not a fourth grade. `kind (iv a b)` is `kind gω` (`iv-copied`): send copies. `spend-iv` leaves the residual (`iv-residual-stays` is that lemma). `isZeroGrade (iv a b)` is false, so `collect` does not drop the root. v0 and v1a do not spend inside an interval.
- **`pt (fin n)` for `n ≥ 2`.** `beamGrade` returns `nothing` (`beam-fin2`). Send moves it and spend decrements it, and `grade1-unique` does not apply. The boundary does not call this point `g1` or `ω`.

`beam-g0`, `beam-g1`, and `beam-ω` are the three `refl`s on muro's `g0`, `g1`, and `gω`.

### Values and operations

`BeamVal` is `Val`. A payload is a flat `nat`, a `suc↑` holding a `Ref`, or a `clo` holding the `List Ref` it captured and a scoped `GTm`. Those references live in an `Ordered` heap: every child index is strictly below its parent. The boundary does not redefine `Val`, `Ref`, or `Ordered`.

`alloc`, `deref`, `send`, and `collect` are the v1a functions. `deref` spends through `spendRef`. The evidence is the existing lemmas, re-exported and not re-proved:

- `collect-safe`, `collect-frees-zero`, `residual-inv-step`
- `grade1-unique`, `send-g1-moves`
- `grade0-not-dereferenced`, `reuse-ordered`
- `lower-safe`, `lower-g0-never-deref`
- `spend`, `spend-finite`, `spend-ω`, `spend-iv`

### The fragment

`InBoundary : GTm 0 → Set`. Lowering consumes a `Checked` term, and that term has scope 0, so the contract is a predicate on closed terms. `InB` is the same predicate under the binders the walk has entered. A free variable of an open term is not graded by `InBoundary`. `inBoundary? : (t : GTm 0) → Dec (InBoundary t)` decides it by recursion on the term. There is no fuel and no termination pragma.

A `glam` is refused when a grade-1 binder is already in scope. `eval1` stores the whole environment in the closure (`clo env`), and `anyG1` refuses that step. The §2B term is this shape: both inner closures sit under the outer `g1`, including the closure that captures the `g1` variable and is passed to the `ω` binder. `boundary-refuse` is `inBoundary? cex ≡ no _`. `boundary-accept` is `inBoundary? (term once) ≡ yes _`. `once` is muro's `grade-once`, a checked `g1` λ whose body is a variable.

The check is conservative. A `glam` under a `g1` binder is refused even when a particular trace never enters that binder. A `gvar` whose binder is `g0` is refused, because `spend` refuses a `g0` residual (`isZeroGrade`). Uses are not counted: two uses of a `g1` variable are `decide`'s refusal. A `gpi` body is erased by `eval1` and is still scanned, so a closure written only inside a Π can be refused even though that Π never runs it.

`capture-check-clear` is the link that is proved. If `InB Γ (glam c t b)` and the environment realises `Γ` (`EnvGrades`), then `anyG1` of that environment is false. `lam-not-under-g1` is the syntactic half: an accepted `glam` has `sharpCxt Γ ≡ false`. `sharp-env` says `sharpCxt` and `anyG1` agree when the environment realises the context. `g1-blocks-lam` is the inner closure of the §2B shape, a `glam` in the singleton context `(g1)`. `closed-lam-clear` instantiates `capture-check-clear` at the empty environment `lower` starts from. `anyG1 []` is false for every closed λ, in the fragment or not.

What is not proved, and is v1c: that a running trace stays inside `EnvGrades`, `NoEscape`, `noEscape?`, `budget-adequate`, `decide-sound`. `InBoundary` does not say that every `Step*` from `lower` avoids a stuck `eval1`. A shape-stuck term such as `gapp gze gze` is in the fragment. `badG1`, a second alias of a `g1` pointer, is not decided here.

### Muro side

A program imports the boundary. The implementation stays here. The Muro-side spelling, once an emitter exists, is:

```
import beam "muro-beam-boundary"
def myProc : run Π (r : BeamGrade) → InBoundary r → Proc
```

That is not a muro term in this repository. A pure Muro mirror of the boundary comes later. The Agda predicate is on a closed `GTm`, the run image. The Π above is the intended client spelling. It is not a type in this book.

## Limits

- **ω and intervals are not spent down.** A use leaves the residual where it is. They are aliased, not moved. Ordered tracing frees the cell once nothing reaches it, including a degenerate interval `[0, 0]` after its last live reference is gone. Nothing inside an interval is decremented.
- **No fairness.** `Step` is one step of some process, or one `eval1`, or `collect`. The book does not prove that a ready process eventually runs, and it does not count reductions. Fuel in `runFor` is a bound supplied by the trace, not a liveness theorem.
- **No distribution.** One shared heap, one list of processes, no locations, no network.
- **No FPGA and no LVA.** Binder grades are used as written. There is no second analysis and no hardware emitter.
- **No muro→muro-beam emitter, and no core `Tm`.** v1a lowers a `GTm` that `decide run` already accepted. It does not read `Muro.Reduction`, and muro `v0.20.32` has no `erase : Tm → GTm`.
- **Application is additive.** As recorded below from the review of murolang/muro#211, the graded judgment adds use vectors and does not scale an argument by the binder's computational grade. The runtime follows that choice. The counterexample in the v1 section is accepted by `decide` and gets stuck on the machine. Send does not multiply. A finite point grade is moved whole, residual included. `ω` and intervals are aliased. They are not scaled.
- **Payloads are `nat`, `suc↑`, and `clo`.** A `nat` is copied on dereference. A `suc↑` or a `clo` is a reference payload. Reachability in `collect-safe` is `Reach`, not the reference alone.
- **Capture of `g1` does not alias.** Building a closure that would put a second graded reference on a `g1` object is not a step. Programs that do that get stuck safely. `NoEscape` adequacy is v1c.
- **No spawn, failure, or supervision.** The process list is fixed by the configuration that starts the trace. `waiting` is still unused. Spawn, send, and recv as term formers are v1b.
- **Environment slots are not reindexed by `collect`.** A `g0` root or mailbox message is dropped, as in v0. A `g0` environment slot stays in place so that de Bruijn indices do not move; it does not mark its object reached. Scope exit pops the binder. That is what lets `collect` free it.
- **Grade 1 is the unique checked point `g1`.** Uniqueness is not claimed for a finite point above 1. Those are still moved rather than copied by send. The theorem that is actually proved is the `g1` statement, now over roots, messages, environments, frames, and heap edges.
- **`InBoundary` is not adequacy.** It refuses a closure in the scope of a `g1` binder, and a `g0` variable. It does not count uses, and it does not follow a trace. `NoEscape` and `budget-adequate` are still v1c.
- **Not in this book.** `PTm`, `checkP`, `lowerP`, `NoEscape`, `noEscape?`, `decide-sound`, `budget-adequate`, `exact-exhausts`, `done-collect-empty`, `MuroBeam.Ref`, `lower-sim`. No executable runtime, no extraction, no bytecode. No pure Muro mirror of the boundary.

## Goals beyond v0

- Execute a real muro run image, once an emitter exists.
- Read computational grades as static multiplicity: `0` drop, `1` move, `ω` reuse, and an exact natural or an interval when the checker knew more. v0 does the `0` / `1` / `ω` cases and keeps intervals. It does not yet spend a finite point above 1 down to zero inside a larger runtime.
- Treat a missing grade pair as the affine interval `[0, 1]`. The lattice already contains that interval (`aff`). v0 keeps it alive with the other intervals.
- Honor type-level grades only where they constrain the runtime. v0 accounts for the computational component. It does not keep a second dynamic counter for the type-level grade.
- Stay downstream of muro. The checker discharges grade constraints. The VM consumes facts.

## Non-goals

- No LVA on top of binder grades.
- No FPGA emitter.
- No self-hosting of muro on muro-beam.
- No SMT solver, and no change to how the muro checker discharges constraints.
- No change to session linearity beyond the reading "linear = grade 1".
- Not a replacement for the existing emitters. Those continue to erase grades.
- Not a distributed BEAM, and not an OTP supervisor.

## Relationship to the grades work in muro

A binder may carry an optional grade pair `(x : (c, t) A)`.

- `c` is the computational grade: how many times the bound value is used at run time.
- `t` is the type-level grade.
- The lattice includes `0`, `1`, `ω`, finite points, and intervals. v0 imports that lattice.
- Absence of a pair means the affine interval, not a second runtime rule invented here.

The checker proves the ungraded fragment is unchanged and the emitters erase grades before they write code. This repository is where a runtime that consults those facts lives.

## Application rule: additive, not multiplicative

Recorded from the review of murolang/muro#211 (Ricardo Corral-Corral, 2026-11-10).

The application rule in the graded judgment simply adds the use vectors of the function and the argument:

```agda
decide m Γ (gapp f a) =
  decide m Γ f >>= λ fu →
  decide m Γ a >>= λ au →
  ok (addU fu au)
```

There is no multiplication by the grade of the parameter. In a full graded system the uses of the argument would be scaled by the computational grade of the binder they are substituted for. That scaling is omitted here so that a graded binder does not change the use-counting behaviour already defined for +. An operand is counted the same way whether it appears under a graded λ or under an ordinary one. The ungraded fragment therefore stays exactly as it was, and a graded book still emits the same code as the book with the grade pairs removed.

Multiplying would have made grades affect the affine accounting itself. That is a larger change: it would require a second quantity, it would make the treatment of graded binders diverge from the treatment of +, and it would break the emission identity that the PR is careful to preserve. For a first introduction of grades as pure evidence that refine (but do not alter) the existing use check, the non-multiplying rule is the smaller and consistent design.

If a later runtime needs the multiplicative reading, it can be added as an explicit extension on top of this judgment. The books that check today will still check, and the wall remains the same.

Implication for muro-beam: the runtime must not assume that argument uses are scaled by the binder's computational grade. v0 does not scale. A send of a finite point moves the residual that remains. A send of `ω` or an interval aliases that same grade. If muro-beam needs the multiplicative reading, it is added as an explicit extension on top of the judgment in murolang/muro, so books that check today keep checking.

## Open questions

- **Image format.** v1a runs a `GTm` in the CEK. It does not choose bytecode or a backend. There is still no emitter.
- **Scheduling policy.** v0 fixes only the one-step relation. Reduction counting, preemption, and per-process heaps are open. v0 uses one shared heap.
- **Intervals as usage budgets.** v0 keeps them. A later collector could spend inside an interval once the checker and the runtime agree on a decrement that stays inside `≤ᵍ`.
- **Failure and supervision.** Open. Not in this book.
- **Interop** with code the Elixir backend already emitted. Open.
