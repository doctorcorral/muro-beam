# muro-beam design

muro-beam executes muro *run* images as processes, in the spirit of the Erlang BEAM: lightweight actors, mailboxes, and a wall between what a book proved and what the host steps at runtime.

v0 is a total Agda book of that runtime. It does not emit code and it does not re-check a muro term. It reads the grades muro's judgment already checked.

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

The modules are `MuroBeam.Grade`, `MuroBeam.Heap`, `MuroBeam.Process`, `MuroBeam.Collect`, and `MuroBeam.Example`. `MuroBeam.Lib` holds a few natural-number and list lemmas so the book does not import the large `Data.Nat.Properties` development. `MuroBeam` re-exports the book.

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

Payloads are natural numbers. An object does not contain further pointers. The only references are roots and mailbox messages, so "reachable" in v0 means "pointed at by one of those references". This is not a tracing collector.

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

## Limits

- **ω and intervals are kept alive.** v0 does not decrement them and does not trace through them. `collect` frees a slot only when every reference to it has residual point `g0`. An interval is not that point, so it is kept, including a degenerate interval `[0, 0]`. There is no tracing collector.
- **No fairness.** `Step` is one step of some process. The book does not prove that a ready process eventually runs, and it does not count reductions.
- **No distribution.** One shared heap, one list of processes, no locations, no network.
- **No FPGA and no LVA.** Binder grades are used as written. There is no second analysis and no hardware emitter.
- **No muro→muro-beam emitter.** v0 does not read `Muro` terms, judgments, or run images. A later book can translate a checked run term into these steps. This one only consumes grades.
- **Application is additive.** As recorded below from the review of murolang/muro#211, the graded judgment adds use vectors and does not scale an argument by the binder's computational grade. The runtime follows that choice. Send does not multiply. A finite point grade is moved whole, residual included. `ω` and intervals are aliased. They are not scaled.
- **Flat payloads.** Objects hold a `ℕ`, not a tuple of child pointers. Reachability in `collect-safe` is the reference itself.
- **No spawn, failure, or supervision.** The process list is fixed by the configuration that starts the trace.
- **Grade 1 is the unique checked point `g1`.** Uniqueness is not claimed for a finite point above 1. Those are still moved rather than copied, so v0 never aliases them either. The theorem that is actually proved is the `g1` statement.

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

- **Image format.** v0 does not choose bytecode, an interpreted run AST, or a new backend. There is still no emitter.
- **Scheduling policy.** v0 fixes only the one-step relation. Reduction counting, preemption, and per-process heaps are open. v0 uses one shared heap.
- **Intervals as usage budgets.** v0 keeps them. A later collector could spend inside an interval once the checker and the runtime agree on a decrement that stays inside `≤ᵍ`.
- **Failure and supervision.** Open. Not in this book.
- **Interop** with code the Elixir backend already emitted. Open.
