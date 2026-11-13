# muro-beam

A BEAM-like virtual machine for [muro](https://github.com/murolang/muro) books.

v0 (tag `v0`) is a `--safe` Agda model of that runtime: processes and mailboxes, a one-step scheduling relation, a shared heap with checked and residual grades, a total `collect`, and send that moves a grade-1 value. It imports muro's grade lattice. It does not emit code and it does not re-check a muro term.

v1a lowers a closed `GTm` that `decide run` accepts. A CEK step evaluates it on the v0 heap. Payloads are `nat`, `suc↑`, and `clo`. `collect` is one ordered pass. `lower-safe` says every reachable state stays well-formed, and a `g0` checked grade is never spent.

v1b adds `PTm`: `spawn`, `send`, `recv`, `seq`, and `done`, plus `await` and `ignore`. A reply can sit in the sender's ether before it is delivered, which is the window v0's atomic `send` does not have. `no-stray-reply` says that after the caller finishes `await` or a flushing `ignore` on a grade-1 reply, no interleaving puts that reply back in the caller's mailbox. A naive `ignore` that demonitors without flushing does leave it there. The flush blanks a `suc↑` or `clo` edge that still holds the tag, so the same theorem covers a reply that lived in the heap.

v1c is the adequacy layer. `NoEscape` is the capture restriction already used by the machine: no λ is placed where a grade-1 binder is in scope. `InBoundary` implies it (`inBoundary→noEscape`) and is still only a syntactic filter. `decide-sound` is binder discharge for `decide run`. `budget-adequate` says that on every `Step*` from `lower` of a match-free `NoEscape` term, a checked grade-1 slot is spent at most once, and `exact-exhausts` says the residual is `g0` when that binder is popped. `done-collect-empty` says an empty live set frees every heap slot. `MuroBeam.Ref` is a grade-free CBV machine. Forward `lower-sim` is not a theorem: `alias` is in `NoEscape`, the reference machine β-reduces, and the CEK refuses that β because the argument is aliased. The limits are in [docs/DESIGN.md](docs/DESIGN.md).

## Boundary v1

`MuroBeam.Boundary` is the contract, not the implementation. The implementation is the v1a machine. The boundary re-exports it: three grades, the payloads, and the theorems a client cites (`collect-safe`, `lower-safe`, and the others named in [docs/DESIGN.md](docs/DESIGN.md)). It is versioned. This book exports boundary v1 (`boundary-version` is 1).

`BeamGrade` is `g0`, `g1`, and `ω`. An interval, including muro's `aff`, is read as `ω`: the runtime copies it and keeps the root alive. A finite point above 1 is outside those three.

`InBoundary` is a decidable check on a closed `GTm`. It refuses a closure built in the scope of a grade-1 binder. muro's `grade-once` is accepted. The additive counterexample, a `g1` variable captured in a closure and passed to an `ω` binder, is refused. That check is not a trace theorem. It implies `NoEscape`. The trace invariant for grade 1 is `budget-adequate`.

A program imports the boundary. The Muro-side spelling, once an emitter exists, is:

```
import beam "muro-beam-boundary"
def myProc : run Π (r : BeamGrade) → InBoundary r → Proc
```

That import is not a muro term in this repository. The pure Muro mirror of the boundary is the book in [`book/`](book/). It is checked with muro 0.20.33. It defines the grades, the terms, the boundary check, the runtime data, the heap operations `alloc`, `deref` / `spend`, `send`, and `reuse`, one CEK step (`eval1`, and `runFor` on fuel), and total ordered `collect`. It does not yet receive, spawn, or schedule, and it is not yet compared with the Agda model. The plan is [docs/RUNTIME-BOOK.md](docs/RUNTIME-BOOK.md).

See [docs/DESIGN.md](docs/DESIGN.md).

## Check

Agda 2.7 or 2.8, and the standard library v2.3. The lattice is the submodule `vendor/muro`, pinned at murolang/muro tag `v0.20.32`.

```sh
git submodule update --init vendor/muro
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

`make agda` checks `agda/MuroBeam.agda` with `--safe` and `--no-libraries`. `make audit` rejects `postulate`, termination pragmas, holes, and an `OPTIONS` line without `--safe`. `vendor/agda-stdlib` is gitignored.

`make book` checks the Muro book with `mix muro.check`. The archive is muro 0.20.33 from Hex, not the Agda pin above. [`docs/RUNTIME-BOOK.md`](docs/RUNTIME-BOOK.md) records both pins.

## Related

- [murolang/muro](https://github.com/murolang/muro) — the language, the checker, and the current emitters
