# muro-beam design

muro-beam executes muro *run* images as processes, in the spirit of the Erlang BEAM: lightweight actors, mailboxes, and a wall between what a book proved and what the host steps at runtime.

v0 is a total Agda book of the scheduler, the graded heap, and send. v1a is that runtime plus a CBV CEK that runs a closed `GTm` muro's `decide run` has accepted. It does not emit code. It does not re-check a muro term. It reads the grades muro's judgment already checked. Boundary v1, in `MuroBeam.Boundary`, is the contract over that machine. The machine is the implementation.

`main` at `079ca47` is tagged `v0`. v1 is three pull requests. This book is the third: adequacy of the v1a machine, on top of the v1b process layer.

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
| **v1a** | `Checked`, CEK lowering, reference payloads, ordered tracing `collect`, safety of every reachable state | processes that spawn |
| **v1b** | `PTm`, `checkP`, `lowerP`, spawn / send / recv, `waiting`, the request/reply ether, `no-stray-reply` | adequacy |
| **v1c** (this book) | `NoEscape`, `noEscape?`, `decide-sound`, `budget-adequate`, `exact-exhausts`, `done-collect-empty`, `MuroBeam.Ref` | a multiplicative application rule, `erase`, and forward `lower-sim` |

`lower-sim` was attempted in this book and is not a theorem. The statement is false for the `NoEscape` defined below. The section "v1c" records the counterexample. Nothing here postulates it.

### Input

`MuroBeam.Source` defines the input of v1a:

```agda
record Checked : Set where
  field
    term : GTm 0
    ok   : decide run [] term ≡ ok []
```

Run mode only. Spec and evidence terms are not lowered.

`decide-sound`, `NoEscape`, and `noEscape?` are proved in v1c. v1a does not need them for safety. A checked grade `g0` forces the residual to be `g0` (`Kept`), and `spend` refuses a `g0` residual, so no run step dereferences that binder. `gtyp` and `gpi` never call `spend`.

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

`NoEscape` excludes this pattern: both inner λs sit under the outer `g1`. v1a proves safety for every lowered program, including this one. Adequacy does not claim it. The exact predicate is in the v1c section. It is stricter than the spec's wording, which would still allow a λ in the head of a β-redex. This machine refuses every `glam` while `anyG1` is true, so the predicate refuses every such λ.

### Theorems added in v1a

- **`lower-wf`**. `WF (lower e)`. Bounds hold and grade 1 is unique. The heap is empty.
- **`lower-safe`**. `Step* (lower e) s` implies `WF s` and `AllInv (refsOf s)`. Collect-safety and grade-1 uniqueness apply to every state reachable from a checked program.
- **`lower-g0-never-deref`**. A reference whose checked grade is `g0` has residual `g0`, and neither `deref` nor `eval1` spends it. `gtyp` and `gpi` do not read the environment. The checker side of the same fact is `sat g0 (finᶜ 0)` and `erased-is-zero`. `decide-sound` is the discharge fact for every binder, and it is not a trace. The trace fact for a grade-1 slot is `budget-adequate`.
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

`InBoundary` is not a trace theorem. A `yes` does not say that every `Step*` from `lower` avoids a stuck `eval1`. A shape-stuck term such as `gapp gze gze` is in the fragment. So is `alias` in `MuroBeam.Example`: `inBoundary?` and `noEscape?` both accept it, the reference machine returns the argument closure, and the CEK stands on a `β` that `badG1` refuses. `inBoundary→noEscape` is the implication that is proved. The converse is not claimed. `budget-adequate` is a separate trace invariant for match-free terms, stated in the v1c section.

### Muro side

A program imports the boundary. The implementation stays here. The Muro-side spelling, once an emitter exists, is:

```
import beam "muro-beam-boundary"
def myProc : run Π (r : BeamGrade) → InBoundary r → Proc
```

That is not a muro term in this repository. A pure Muro mirror of the boundary comes later. The Agda predicate is on a closed `GTm`, the run image. The Π above is the intended client spelling. It is not a type in this book.

## v1b / processes

v1b adds a process term and a scheduler step that can see a reply in flight. The modules are `MuroBeam.PSyntax`, `MuroBeam.PRun`, `MuroBeam.PTm`, `MuroBeam.Stray`, and `MuroBeam.PWf`. `MuroBeam.PExample` is the trace. v0 and v1a are unchanged: every theorem they named still has the same statement. `vendor/muro` stays at `v0.20.32`.

### Term

`PTm` is our own term. It is not a new typing judgment inside muro.

- `done` ends the process.
- `send j x` sends environment slot `x` to pid `j`. One computational use of `x`.
- `recv (c , t) P` receives into a binder checked the way `glam` is checked (`under`).
- `spawn (Γ' ⊆ Γ) P` starts a child on a sub-environment. The thinning is `Thin`.
- `seq e P` runs a `GTm` and binds the value at grade `(ω , 0)`.
- `await`, `ignore`, and `nignore` are the request/reply surface. `await` and `ignore` consume a grade-1 reply. `nignore` is the negative example: the pre-fix shape that does not flush.

`checkP` calls muro's `decide`, `sat`, and `checkGrade` for every grade decision. It does not define a lattice. A send of a point at least 1 is one use, discharged later by `hold` / `under`. Grade 0 is refused because `sat g0 (finᶜ 1)` is false. A copied grade (ω or an interval) must pass `checkGrade` at `U0`, `U1`, or `Uω`. That chain rejects a narrow interval such as `[2 , 3]`. The gap is intentional and is the same kind of incompleteness as `InBoundary`: a `no` is a refusal, a `yes` is only the fragment the checker knows how to discharge.

`spawn` hands variables over the way v0 send does. A finite point, `g1` included, moves out of the parent. ω and intervals are copied. `g0` cannot be handed over. Moved slots in the parent become one shared fresh `g0` cell, so the placeholder is not an alias of a live object. The child's uses of a moved variable are the uses the parent context is charged. A protocol consumer (`await`, `ignore`, or `nignore`) sitting at the root of the parent continuation must itself be exactly one computational use; that use is the shape check, and it is not added on top of the child's use. Buried under `seq` or another constructor, it is not rewritten. Pids are stable: `spawn` appends, and nothing removes a process.

`seq` requires `inB?` of the embedded `GTm`, then `decide run`. `InBoundary` stays what v1a proved. Acceptance means the term is in the fragment the v1a machine was proved to keep well-formed. It does not mean every reduction sequence succeeds. This book does not turn `InBoundary` into a trace theorem.

### Runtime

A process instruction is a `Code`: the `PTm`, the environment, an ether of flights, and two tag lists, `dead` and `demo`. A flight is `flight dst ref`. It sits in the sender's `Code`. `ctlRefs` of `pr` counts the environment and the flights. While `seq` runs, the code is parked on a `saved` frame and `seq` parks an empty environment there, so the CEK environment stays the only copy of those references. `frameRefs` of `saved` still counts the parked environment together with the flights. `bind` moves that environment into the resumed code, a permutation of `refsOf`. Counting the parked environment means a tag cannot sit in a continuation and later reappear without having been in `refsOf`. `collect` and `grade1-unique` see an in-flight reply. There is no new `Msg` constructor and no ether field on `Sys`. v0 `send` still deposits straight into a mailbox. It is only a lifted step.

`recv` on an empty mailbox is no longer stuck as `nothing` when the instruction is the process `recv`. The process moves to `waiting`. A delivery sets it back to `ready`. The v0 function `recv` is unchanged and still returns `nothing` on an empty mailbox. `waiting` is used only by the process-layer steps. A finished process stays in the list, in `done`. `done` drops its environment and its roots and keeps the ether, so a reply already emitted can still be delivered.

`lowerP` starts pid 0 on an empty heap, in `pr`. `lowerP-safe` says every state reachable by `PStep*` is well-formed: the bound, `grade1-unique`, and `AllInv` on `refsOf`. `spawn-preserves-grade1` is the handover case of that proof (v0's move and copy facts, through `grow-unique`). `spawn-preserves-residual` is `AllInv (refsOf t)`, the same strength as `send-preserves-residual`: every reference still carries `Kept`.

### v1b / no-stray-reply

A request carries one grade-1 reply reference. The tag is that reference's object index, not a natural number a process could forge with `alloc`. The caller must consume it exactly once, by `await` or by a proper `ignore`.

Proper `ignore` is two steps, in the shape of Elixir's `Task.ignore/1` after the fix in elixir-lang/elixir@4104cd6 (issue [#16064](https://github.com/elixir-lang/elixir/issues/16064)):

1. `arm1` demonitors. The tag is recorded in `demo`. The mailbox and the ether are left alone. `dead` is not set.
2. `flush1` consumes the tag. It deletes every non-edge occurrence (mailboxes, roots, flights in every process) and replaces environment and frame occurrences with one fresh `g0` cell, so de Bruijn indices do not move. Then it sets `dead`.

`await` consumes the same way. It does not bind the payload. The reply value is the reference itself. On an empty mailbox it waits.

Naive `ignore` is the pre-fix shape: `npeek1` is the `after 0` receive, and on a miss `ndemon1` demonitors with no flush and without setting `dead`.

The step relation these theorems quantify over is `PStep`, not `Step`. `PStep` includes every v0/v1a `Step` via `lift`, plus spawn, emit, deliver, recv, await, arm, flush, the naive pair, seq, bind, and done. One schedule is not enough. `PStep*` is any finite interleaving.

```agda
data ReplyDone (s : Sys) (i τ : ℕ) : Set where
  replied :
      count τ (refsOf s) ≡ 0
    → τ < length (heap s)
    → deadAt (procs s) i τ ≡ true
    → ReplyDone s i τ

no-stray-reply :
    ∀ {s t i τ}
  → PStep* s t
  → ReplyDone s i τ
  → mailHas (procs t) i τ ≡ false
```

`ReplyDone` is unchanged: the count of `τ` in `refsOf` is zero, the object is in bounds, and `dead` is set. `flush1` and a consuming `await1` establish it (`ignore-consumes`, `await-consumes`). Those two lemmas no longer take `count τ (edgeRefs h) ≡ 0`. `consume` blanks every payload that still holds `τ` (`blankVal`: a `suc↑` or a `clo` whose children include the tag becomes `nat 0`) and then appends the fresh `g0` placeholder. Blanking is what makes the edge count zero, so a reply that lived only in a `suc↑` or a `clo` is covered by the same `ReplyDone`. The old premise is the special case in which the heap already had no such edge. `PExample.edge-stays` is that trace: the tag is the child of a `suc↑`, flush blanks it, and `no-stray-reply` applies to every later `PStep*`. Naive demonitor does not establish `ReplyDone`: the flight is still a reference, and `dead` is not set. Blanking is stronger than an `after 0` receive, and stronger than the v1b flush, which left the edge in place. A `gmatch` that extracts a `suc↑` and then sends the child can reintroduce the tag only when the edge was not blanked.

`PExample` records the schedules. `j5-stays` and `k4-stays` apply `no-stray-reply` after a flushing `ignore`: the reply was delivered in the demonitor/flush window, and flush ran before deliver. `a4-stays` is the same fact for `await`. `naive-leak` is a concrete `PStep*` from `n0` to `n5` on which `mailHas` of tag 0 is still true.

The proof is that a count of zero for an in-bounds object is preserved by every `PStep`, and a mailbox message is a reference in `refsOf`. `alloc`'s index is the length of the heap. `reuse` needs a live reference. Copying or sending needs a reference that is already there. None of those rebuilds an object whose count is already zero.

### Modeling assumptions

These are the places the model is sharper or coarser than the BEAM. They are assumptions, not theorems about Erlang.

- The ether is the sender's flight list. `emit` then `deliver` is the two-phase send. v0 `send` stays atomic and cannot express this window by itself.
- `demonitor` does not retract a flight and does not delete a mailbox message. It does not set `dead`. `deliver` reads `dead` only, so a reply that is in flight during demonitor is still enqueued if `flush` has not run.
- `Process.demonitor(ref, [:flush])` flushes `DOWN` messages, not `{ref, reply}`. This model has no `DOWN` constructor. The reply is an ordinary `msg`. The flag is not treated as removing that message.
- Proper `flush` consumes both a reply that has already arrived and a reply that is still a flight. On the BEAM, `flush_reply` is an `after 0` receive: it only sees the mailbox. A message still on the wire after that receive can still be delivered. Here the reply is a grade-1 reference, so the consuming flush deletes every remaining non-edge copy, blanks a `suc↑` or `clo` payload that still holds the tag, and `dead` makes a later `deliver` drop instead of enqueue. That is what makes the theorem true for every interleaving, including a `deliver` after `flush`, and including a tag that lived only as a heap edge. It is stronger than one `after 0` receive, and stronger than a flush that left the edge in place. It is the model's reading of "once `ignore` has returned, a late copy of this unique reply is not deposited."
- A new `emit` is refused when the destination already has the tag in `demo` or in `dead`. Refusal does not delete a flight that is already in the ether. Deactivation of the alias does not recall a message already sent.
- The naive leak is a concrete `PStep*` trace. The reply is in the ether while `ndemon1` runs, `dead` is not set, and the following `deliver` leaves `msg` in the caller's mailbox. A second window, `deliver` between the empty `after 0` and demonitor, is the same fact. If the mailbox already holds the tag, `npeek1` consumes it and there is no leak. That is the successful `after 0` branch.
- `seq` parks flights on `saved`. `deliver` pulls from `pr` and from `saved`. `bind` resumes only when `saved` is the whole stack, which is the shape `seq` produces. A `saved` frame buried under another `saved` is not produced by `seq`.
- The tag rewrite at `spawn` applies only to a protocol constructor at the root of the parent continuation.

### What v1b does not prove

The adequacy statements are the next section. v1b does not prove them. No multiplicative application. No new typing judgment. No executable runtime.

## v1c

Adequacy lives in muro-beam. muro is untouched, and application stays additive. The modules are `MuroBeam.Source` (`NoEscape`), `MuroBeam.Boundary` (`inBoundary→noEscape`), `MuroBeam.Adequacy` (`decide-sound`, `done-collect-empty`), `MuroBeam.Budget` (`budget-adequate`, `exact-exhausts`), and `MuroBeam.Ref` (the grade-free machine). There is no `MuroBeam.Sim`. `lower-sim` is not defined.

### `NoEscape`

The spec's wording was: a λ whose free variables include a finite or interval grade appears only in the head of a β-redex, or as the argument of a `glam` whose grade is a finite point of 1 or less. This machine does not implement that positions predicate. `eval1` on `glam` is `pass (not (anyG1 env))`, and `anyG1` is true when any captured reference has checked grade `g1`. A λ under a `g1` binder is not a step, including one that sits in the head of a β-redex. The predicate is that restriction, on the syntax:

```agda
NoEscape : GTm 0 → Set
NoEscape e = NoEsc [] e

-- ne-lam is the only interesting clause:
ne-lam : ∀ {c t b} → g1InScope Γ ≡ false → NoEsc (c ∷ Γ) b →
         NoEsc Γ (glam c t b)
```

`g1InScope` is true when the context contains `pt (fin 1)`. `noEscape? : (e : GTm 0) → Dec (NoEscape e)`. A finite point above 1, and an interval, may still be captured. That is weaker than the spec on those grades, and it is what makes `InBoundary` imply the predicate. `InBoundary` also refuses a `g0` variable, so the converse is false.

```agda
inBoundary→noEscape : ∀ {e} → InBoundary e → NoEscape e
```

`InBoundary` stays a sound but incomplete syntactic filter. It is not a trace theorem. The trace theorem is `budget-adequate`, which takes `NoEscape` as a side condition and quantifies over every `Step*` from `lower`, not over one schedule. It does not quantify over an arbitrary `PStep*`: a spawned process is outside this invariant. `no-stray-reply` is the statement that does quantify over every `PStep*` interleaving, and it is unchanged.

### `decide-sound`

The sentence "if `decide run Γ e ≡ ok us`, then each `us[x]` satisfies `sat` of `Γ[x]`" is false. `decide` on `gvar` does not consult `Γ`. `decide run (gp g0 g0 ∷ []) (gvar fzero)` returns computational count `finᶜ 1`, and `sat g0 (finᶜ 1)` is false. A closed `Uses 0` is empty, so that reading says nothing about a closed term either. What `under` checks is the binder. Spec mode forgets the computational component. A `gpi` is checked in spec mode even when the surrounding judgment is run.

```agda
decide-sound : ∀ {n} (Γ : GCtx n) e us →
               decide run Γ e ≡ okR us → Discharged run Γ e
```

`Discharged` carries, at each `glam`, `gpi`, and `gmatch`, evidence that checking the body returned a vector headed by `sp co ty`, and `sat` of the component the mode inspects on those counts. `ds-pi` checks the body in spec mode and records the type component only. `sat-g0-zero` is the static half of a grade-0 binder: `sat g0 k ≡ true` implies `k ≡ finᶜ 0`. `¬discharged-ghost` is `¬ Discharged run [] (glam g0 g0 (gvar fzero))`: the body checks as one computational use, and `sat g0` rejects it. `decide` fails the same term (`ghost-decide-fails`).

### `budget-adequate` and `exact-exhausts`

Only a checked grade of `g1` is tracked, and only on a match-free term. `MatchFree` has no `gmatch` clause. The spec's `NoEscape` mentions `gmatch`; this proof does not. Along every `Step*` from `lower`:

```agda
budget-adequate : (e : Checked) {s : Sys} →
                  NoEscape (term e) → MatchFree (term e) →
                  Step* (lower e) s → Inv tight s
```

`Inv tight` says the heap payloads and the focused control agree on the debt. A slot whose checked grade is still `g1` has residual `g1` and exactly one computational occurrence ahead, or residual `g0` and none. `spendRef` therefore does not refuse that deref. The debt is the `occ` count of the focus plus the frames, which for a checked `g1` binder is 1. Finite points above 1 are outside the invariant: a `pt (fin 2)` binder may be captured by an ω closure and used more than twice, and that term is still `NoEscape`. An interval does not step down to `g0`.

```agda
exact-exhausts : ∀ (e : Checked) {s h p v env env0 k i r} →
                 NoEscape (term e) → MatchFree (term e) →
                 Step* (lower e) s →
                 s ≡ sys h (p ∷ []) →
                 ctl p ≡ rv v env (bd env0 ∷ k) →
                 lookup env i ≡ just r →
                 isG1 (checked r) ≡ true →
                 residual r ≡ g0
```

At a `bd` pop the debt is 0, so a `g1` residual is `g0`. That is the one use, which is what `reuse` asks of a grade-1 cell. The spec's reading for every `fin n` is not what is proved. A binder that has not reached the pop is outside the claim. `budget-g1` is the companion fact: a `g1` variable that is about to be read still has residual `g1`.

Two machine limits are excluded rather than repaired. `onMatch` regrades the predecessor with `predComp` of the environment after the scrutinee was evaluated. A `g1` `suc↑` or `clo` moves, and the env slot is then a fresh `g0`, so `predComp` reads `g0`. `gmatch` on `suc` also extends the environment without shifting frames that were pushed in the unextended scope. `MatchFree` keeps both out of `budget-adequate`. `exact-exhausts` was already match-free in the spec.

### `done-collect-empty`

`collect` marks from `liveRefs` only. A false bit never marks a child, so an empty live set frees every slot even when edges exist.

```agda
done-collect-empty : ∀ s → liveRefs s ≡ [] → AllFree (heap (collect s))
```

`done-pid0` is the finished process: pid 0, state `done`, empty roots, empty inbox, empty environment, empty ether. A finished process that still holds flights does not free the objects those flights reach. The v1b model keeps the ether of `done`.

### `MuroBeam.Ref` and `lower-sim`

`MuroBeam.Ref` is a CBV environment machine. `RVal` is a nat, a successor, or a closure (`rlam`). `rstep : RCtl → Maybe RCtl` does not read a grade. A variable lookup returns the environment entry. `_↦_` is the graph of a successful `rstep`. `runR` is fuel-bounded evaluation, the same shape as `runFor`.

Forward simulation does not hold. The spec's statement is: if `e ↦ e'` and `NoEscape e`, then a `lower`-related CEK state reaches a related state by one or more non-collect `Step`s. `alias` in `MuroBeam.Example` is a counterexample:

```agda
alias =
  gapp
    (glam gω g0
      (gapp (glam g1 g0 (gvar fzero)) (gvar fzero)))
    (glam gω g0 gze)
```

`decide run [] alias ≡ ok []`. `noEscape? alias ≡ yes _`. `inBoundary? alias ≡ yes _`. `runR 40 (startR alias)` is the argument closure, `rlam` of `gze`. `runFor 40 (lower alias)` is a CEK state whose control is a returned argument under an `fn` frame, and `eval1` of that state is `nothing`. The argument object is also in the environment, so `badG1` refuses the β. The reference machine takes that β. Putting the name `lower-sim` on a lemma that adds "no grade-1 β of an aliased object", or "no finite point above 1", would be a weaker statement than the one that was asked for. The name is not used.

The same gap is why a grade-free simulation cannot be the proof of the budget. `budget-adequate` is proved directly on `Step*`. A second counterexample shape, not needed for the `alias` trace, is a `pt (fin 2)` binder captured by an ω closure and applied more times than the static count. `NoEscape` allows that capture. The CEK copies the residual into the closure, so the shared budget is not what `spend` sees either. The invariant does not claim it.

`use1`, `gapp (glam g1 g0 (gvar fzero)) gze`, is the adequate trace. It is in `InBoundary`, hence `NoEscape`, both machines return zero, and the CEK halts on that nat. `once`, `twice`, `match-once`, and `match-many` are muro's `grade-once`, `grade-twice`, `grade-match-once`, and `grade-match-many`, each lowered one step to a closure. `cex` is the §2B term: `decide` accepts it, `noEscape?` and `inBoundary?` refuse it, and `runFor 6` is stuck with the `g1` cell still live.

Backward simulation and determinacy are not stated. Adequacy against `Muro.Reduction` is not stated: the pin has no `erase : Tm → GTm`.

### `bind1`

`bind1` resumes only a singleton `saved` stack. `seq` pushes one `saved` frame and parks an empty environment there, so the traces this book runs never need a deeper stack. A `saved` frame under another frame is not produced by `seq`. Generalising the resumption would be a change to the process layer for a case the layer does not build. It is left as it was.

## Limits

- **ω and intervals are not spent down.** A use leaves the residual where it is. They are aliased, not moved. Ordered tracing frees the cell once nothing reaches it, including a degenerate interval `[0, 0]` after its last live reference is gone. Nothing inside an interval is decremented.
- **No fairness.** `Step` is one step of some process, or one `eval1`, or `collect`. The book does not prove that a ready process eventually runs, and it does not count reductions. Fuel in `runFor` is a bound supplied by the trace, not a liveness theorem.
- **No distribution.** One shared heap, one list of processes, no locations, no network.
- **No FPGA and no LVA.** Binder grades are used as written. There is no second analysis and no hardware emitter.
- **No muro→muro-beam emitter, and no core `Tm`.** v1a lowers a `GTm` that `decide run` already accepted. It does not read `Muro.Reduction`, and muro `v0.20.32` has no `erase : Tm → GTm`.
- **Application is additive.** As recorded below from the review of murolang/muro#211, the graded judgment adds use vectors and does not scale an argument by the binder's computational grade. The runtime follows that choice. The counterexample in the v1 section is accepted by `decide` and gets stuck on the machine. Send does not multiply. A finite point grade is moved whole, residual included. `ω` and intervals are aliased. They are not scaled.
- **Payloads are `nat`, `suc↑`, and `clo`.** A `nat` is copied on dereference. A `suc↑` or a `clo` is a reference payload. Reachability in `collect-safe` is `Reach`, not the reference alone.
- **Capture of `g1` does not alias.** Building a closure that would put a second graded reference on a `g1` object is not a step. Programs that do that get stuck safely. `NoEscape` is that restriction. It does not stop `badG1` from refusing a grade-1 β of a value that is already aliased, and `alias` is the witness.
- **No failure or supervision.** Spawn, send, recv, and `waiting` are in this book. A finished process stays in the list. Nothing here restarts a process or links two of them.
- **Environment slots are not reindexed by `collect`.** A `g0` root or mailbox message is dropped, as in v0. A `g0` environment slot stays in place so that de Bruijn indices do not move; it does not mark its object reached. Scope exit pops the binder. That is what lets `collect` free it.
- **Grade 1 is the unique checked point `g1`.** Uniqueness is not claimed for a finite point above 1. Those are still moved rather than copied by send. The theorem that is actually proved is the `g1` statement, now over roots, messages, environments, frames, and heap edges.
- **`InBoundary` is not adequacy.** It refuses a closure in the scope of a `g1` binder, and a `g0` variable. It does not count uses, and it does not follow a trace. It implies `NoEscape`. `budget-adequate` is the trace invariant, for match-free terms and for checked grade `g1` only.
- **`budget-adequate` is not every binder.** Finite points above 1 and intervals are outside `Inv tight`. `gmatch` is outside it (`MatchFree`). A moved `g1` scrutinee is rebound from the slot after the move, which is a fresh `g0`. The successor branch of `gmatch` extends the environment under frames typed in the unextended scope.
- **`exact-exhausts` is the `g1` pop.** It does not claim every `fin n`. A binder that has not reached `bd` is outside it.
- **`decide-sound` is binder discharge.** The counts are the uses `decide` computed for the body. It is not the false free-variable reading recorded in the v1c section.
- **`lower-sim` is not a theorem.** The grade-free machine takes the β that `badG1` refuses. Backward simulation and determinacy are not in this book.
- **`bind1` resumes one frame.** `seq` produces that shape. A nested `saved` stack is not resumed.
- **Not in this book.** No executable runtime, no extraction, no bytecode. No pure Muro mirror of the boundary. No `erase`, and no adequacy against `Muro.Reduction`. `checkP` does not accept every interval: a copied grade must pass `checkGrade` at `U0`, `U1`, or `Uω`. No multiplicative application.

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
