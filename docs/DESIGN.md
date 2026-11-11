# muro-beam design notes

Early, pre-implementation. Nothing here commits the first runtime patch to a particular encoding or scheduler.

## Why

muro already separates run, spec, and evidence, and it emits only run terms. The current backends (Elixir, C, Rust, Zig, JavaScript, assembly, OTP, FSM) do not need to know how many times a binder is used: they erase that information and leave allocation to the host.

A VM that wants to look like BEAM without giving up muro's wall does need those facts. It should be able to drop a value that is never used, move a value that is used exactly once, and keep a value that may be used many times — without re-proving the book at run time.

That is what grades are for. They land in [murolang/muro](https://github.com/murolang/muro) first, as evidence on the mode-indexed judgment. muro-beam is the first runtime that is allowed to read them.

## Goals

- Execute muro run images as lightweight processes / actors: isolated heaps, mailboxes, and message passing, in the spirit of BEAM.
- Read computational grades (`c`) as static multiplicity:
  - `0` — unused at run time; the value can be dropped.
  - `1` — exactly once; the value can be moved, not copied.
  - `ω` — unrestricted reuse.
  - an exact natural, or an interval, when the checker already knows more than `{0, 1, ω}`.
- Treat a missing grade pair as today's affine rule (at most once), which is the special case `c ≤ 1`. Linear is `c = 1`.
- Honor type-level grades (`t`) only where they constrain what the runtime may do; they do not become a second dynamic accounting system.
- Stay downstream of muro. The language checker discharges grade constraints. The VM consumes facts. It does not re-type the book.

## Non-goals for now

- No VM implementation in this repository yet. The first commits are these notes.
- No LVA (a later analysis on top of binder grades).
- No FPGA emitter.
- No self-hosting of muro on muro-beam.
- No SMT solver, and no change to how the muro checker discharges constraints.
- No change to session linearity beyond the reading "linear = grade 1".
- Not a replacement for the existing emitters. Those continue to erase grades.

## Relationship to the grades work in muro

A binder may carry an optional grade pair:

```
(x : (c, t) A)
```

- `c` is the computational grade: how many times the bound value is used at run time.
- `t` is the type-level grade.
- The lattice includes at least `0`, `1`, `ω`, and intervals. Exact natural grades are allowed when they are statically known.
- Absence of a pair means the current affine rule.

The grades PR extends the judgment with a grade context, proves that the ungraded fragment is unchanged, and keeps every current emitter erasing grades before it writes code. This repository exists so the runtime that *does* consult those facts has a home that is not mixed into the language repo.

## Open questions

- **Image format.** Should muro-beam consume an emitted bytecode, an interpreted run AST, or a new official backend beside Elixir/C/Rust/Zig/JS/ASM?
- **Scheduling.** How close to BEAM (reduction counting, preemption, per-process heap, separate mailbox) versus a simpler cooperative actor loop?
- **LVA.** Are binder grades enough for the first useful drop/reuse/move decisions, or is a later linear/affine value analysis still needed on the run image?
- **FPGA.** A later emitter could read the same grades as occupancy or resource constraints. That is a later book, not this one.
- **Failure and supervision.** Does a failed process restart like an OTP supervisor, or is supervision itself a muro book that muro-beam only steps?
- **Interop.** A standalone VM versus talking to code that the existing Elixir backend already emitted for the real BEAM.

These stay open until the grades landing in muro is something a runtime can actually read.

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

Implication for muro-beam: the runtime must not assume that argument uses are scaled by the binder's computational grade. If muro-beam needs the multiplicative reading, it is added as an explicit extension on top of the judgment in murolang/muro, so books that check today keep checking.
