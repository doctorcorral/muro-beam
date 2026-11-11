# muro-beam

A BEAM-like virtual machine for [muro](https://github.com/murolang/muro) books.

v0 (tag `v0`) is a `--safe` Agda model of that runtime: processes and mailboxes, a one-step scheduling relation, a shared heap with checked and residual grades, a total `collect`, and send that moves a grade-1 value. It imports muro's grade lattice. It does not emit code and it does not re-check a muro term.

v1a, on branch `v1a-lowering`, lowers a closed `GTm` that `decide run` accepts. A CEK step evaluates it on the v0 heap. Payloads are `nat`, `suc↑`, and `clo`. `collect` is one ordered pass. `lower-safe` says every reachable state stays well-formed, and a `g0` checked grade is never spent. Spawn is v1b. Adequacy is v1c.

See [docs/DESIGN.md](docs/DESIGN.md).

## Check

Agda 2.7 or 2.8, and the standard library v2.3. The lattice is the submodule `vendor/muro`, pinned at murolang/muro tag `v0.20.32`.

```sh
git submodule update --init vendor/muro
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

`make agda` checks `agda/MuroBeam.agda` with `--safe` and `--no-libraries`. `make audit` rejects `postulate`, termination pragmas, holes, and an `OPTIONS` line without `--safe`. `vendor/agda-stdlib` is gitignored.

## Related

- [murolang/muro](https://github.com/murolang/muro) — the language, the checker, and the current emitters
