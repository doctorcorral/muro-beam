# muro-beam

A BEAM-like virtual machine for [muro](https://github.com/murolang/muro) books.

v0 is a `--safe` Agda model of that runtime: processes and mailboxes, a one-step scheduling relation, a shared heap with checked and residual grades, a total `collect`, and send that moves a grade-1 value. It imports muro's grade lattice. It does not emit code and it does not re-check a muro term.

See [docs/DESIGN.md](docs/DESIGN.md).

## Check

Agda 2.7 or 2.8, and the standard library v2.3. The lattice is the submodule `vendor/muro`, pinned at murolang/muro tag `v0.20.32`.

```sh
git submodule update --init vendor/muro
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

`make agda` checks `agda/MuroBeam.agda` with `--safe` and `--no-libraries`. `vendor/agda-stdlib` is gitignored.

## Related

- [murolang/muro](https://github.com/murolang/muro) — the language, the checker, and the current emitters
