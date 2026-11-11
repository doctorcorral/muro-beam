# muro-beam

A BEAM-like virtual machine for [muro](https://github.com/murolang/muro) books.

This repository is in an early design stage. There is no runtime yet.

muro-beam is meant to execute muro *run* images as processes, in the spirit of the Erlang BEAM: lightweight actors, message passing, and a clear isolation boundary between what a book proved and what the host steps at runtime.

It will consume static multiplicity facts from muro's graded judgment — optional grade pairs `(x : (c, t) A)` on binders — so a future VM can drop unused values, reuse a value in place, and treat exactly-once resources as exactly-once. Those grades are evidence produced by muro. Existing emitters erase them; this runtime is one of the later books that will elect to read them.

See [docs/DESIGN.md](docs/DESIGN.md) for goals, non-goals, and open questions.

## Related

- [murolang/muro](https://github.com/murolang/muro) — the language, the checker, and the current emitters
