# Image format

v1 is the S-expression muro writes for `--backend mbi` today. The
grammar and the byte-level rules of that line are muro's
`manual/mbi.md` at commit
`3f1cae2ae987d1ad27b301e0b1e1ddb03abdd988`. The printer there is
`Muro.Beam.showPure`. v2 is the same line with a `(defs …)` section
between the boundary and the entry. This repository parses both.
The emitter that writes the defs section is not in this repository.

One line, tokens separated by one space, a trailing newline. Naturals
are decimal with no leading zero except `0`. `w` is ω.

```
image ::= (muro-beam-image <version> (boundary 1) (entry <prog>))
        | (muro-beam-image <version> (boundary 1) (defs <btm>+) (entry <prog>))
prog  ::= (seq <btm> (done))
btm   ::= (gvar <nat>) | (gtyp <nat>) | (glam <pair> <btm>) | (gpi <pair> <btm>)
        | (gapp <btm> <btm>) | gze | (gsu <btm>) | (gmatch <btm> <btm> <btm>)
        | (gref <nat>)
pair  ::= (<grade> <grade>)
grade ::= <point> | (iv <point> <point>)
point ::= <nat> | w
```

`<version>` is `1` or `2`. Any other number is `bad version`. A file
with no defs section has an empty definition list, whatever the
number is. An empty `(defs)` nest, with no term inside it, is `junk`.
The printer chooses the bytes from the list, not from the number: an
empty list is reprinted as the four-sexp line, and the number it
prints is the number it read. A cons is reprinted with `(defs …)`.

De Bruijn index 0 is the nearest binder. A `gref` index is a raw
natural. The parser does not check it against the definition list.
`decideB` does, at load. Domain types, annotations, and match motives
are not in the file. The grammar has `gtyp` even though the emitter
does not write it today. There is no process form in the entry. The
entry is `(seq <btm> (done))`.

Definitions are closed terms, in order. Definition i may `gref` its
own index or an earlier one. A later index is `bad gref`. The entry
may `gref` any definition and is not itself a definition. Each
definition is checked once, closed, against `inB? []` and `decideB`.
The entry is checked after that, at bound `length defs`.

What a later `muro emit --backend mbi` must write, when it learns
definitions: format 2, a `(defs …)` section of those closed terms in
dependency order, then `(entry (seq <btm> (done)))`. Grades stay
`(c t)`, with `w` and `(iv a b)`. De Bruijn indices, no domain types,
no motives, no annotations. This loader re-checks, so that emitter
stays outside the TCB. A v1 file with no defs section stays valid.

`MuroBeam.Image` is the record (`format`, `boundary`, `defs`, `term`)
and the printer. `MuroBeam.Parse` reads `String` to `Maybe Image`, and
refuses a de Bruijn index that does not fit its scope. `MuroBeam.Load.load`
accepts format 1 or 2 and `boundary-version`, then runs `checkP` on
`seq defs term done`. A success is a `CheckedP`, built only after that
check returns `ok []`. `lowerP-wf` and `lowerP-safe` apply to anything
loaded. The emitter is outside the TCB for those two. `lower-safe` is
not that claim: it is `Step* (lower e)` for a pure `Checked`.
Non-consequences of `load`: `budget-adequate` is

```agda
(e : Checked) {s : Sys} →
NoEscape (term e) → MatchFree (term e) →
Step* (lower e) s → Inv tight s
```

`checkP` on `seq` runs `boundaryOk (inB? (comps Γ) e)`. `load` calls
that at `Γ = []` on the entry term `e`. That decision is `InB [] e`.
The capture predicate on the same term is `NoEsc [] e`. `InBoundary`
and `NoEscape` are those two predicates on `embed` of a `GTm`, and
`inBoundary→noEscape` has that `GTm` type. There is no theorem
`load s ≡ ok p → InB [] e`, and none `load s ≡ ok p → NoEsc [] e`.
The public adequacy predicates stay `GTm`-only. What is also missing
is `MatchFree` (`match.mbi` loads and contains `gmatch`; `MatchFree`
has no `gmatch` clause; `mf-ref` is a clause of `Mf`) and the theorem's
path: pure `Checked` / `lower` / `Step*`, not `CheckedP` / `lowerP` /
`PStep*`. A successful `gref` step needs the `seg` frame `seq1` pushes,
and that frame is not on the pure path, so `budget-adequate` does not
follow it. `no-stray-reply` needs `ReplyDone`.

The round trip `parse-show` is proved on the character list `render`
produces. `toList ∘ fromList` is not a `--safe` lemma, so the String
statement is not the theorem.

The plan's sketch said `--backend beam` and an arbitrary `PTm` entry.
The emitter writes `--backend mbi` and `(seq <btm> (done))`, and today
it writes no defs section. v1 text is still what this parser accepts.
v2 adds the section above. The round trip `parse-show` covers both.

A complete sexp with no trailing newline, or a file that ends inside
an open sexp, is `truncated`. A newline while a sexp is still open is
`junk`, as is any other ill-formed token.

## Runner

`muro-beam` reads one image file and an optional `--fuel N` (default
1000). `scripts/build_runner.py` generates `MAlonzo/RunnerMain.hs` and
links it. That Haskell main is not an Agda module.
`MuroBeam.RunImage.cliRun` calls `load`, then `drive` at that fuel,
from cursor 0, with no meetings and no kept nat. The printed line is
the outcome, the events, the fingerprint `h<heap>l<live>p<procs>`,
and the kept nat. The event spelling and the decimals are
`MuroBeam.Show`, the same module `MuroBeam.Conform` uses for the book,
so `make conformance` pins the CLI line as well. A numeral past eight
digits is `overflow`.

Exit 0 is `halted`, `deadlock`, or `stuck`. Exit 2 is a parse or load
refusal, and stderr is `muro-beam:` plus the reason (`bad version`,
`bad gref`, `junk`, `truncated`, `outside the boundary`, and the
others `load` returns). Exit 3 is out of fuel: stderr says so, and
stdout is still the partial line. Exit 1 is usage, a fuel argument
that is not a natural, or a file the main cannot read: a missing
file, permission denied, a directory, invalid UTF-8, or a file
larger than 1 MiB. Those read failures print `muro-beam: cannot
read …` on stderr.

A pure image stops `stuck 0`. `seq1` pushes `saved` over `seg`, and
`bind1` resumes only `saved ∷ []`, so the process never reaches
`done`. The kept nat is the value on that returned reference. A
closure keeps nothing (`v-`). Fuel 0 does not step: the line is
`fuel [] h0l0p1 v-`. `mark` also maps `halted` and `deadlock` to
exit 0, but the file has no process form, so those outcomes are not
reached through a `.mbi`.

What this shows is `load` of the `String` the Haskell main passed
in, then one fuelled `drive` of `lowerP`. File IO is Haskell, so
Agda never sees the bytes, only that `String`. `cliRun` takes
`proj₁` of `drive`, so `PStep*` is typechecked into existence
rather than carried as a CLI witness. `drive-sound` is the
`PStep*` on that run. It does not show `budget-adequate`,
`MatchFree`, or `no-stray-reply`. A loaded `gmatch` is still
outside `MatchFree`. The file still has no process form, so spawn,
send, and recv are not an image the loader reads.

The Haskell main and the muro emitter are outside the TCB. `make
audit` does not see them. Hex muro 0.22.13 writes the checked-in
`suc.mbi` for `suc (suc 0)` and the checked-in `plus.mbi` for
`plus 2 3`. `make emit-check` runs that comparison in a private
`MIX_HOME` and then runs both files. The book archive stays 0.20.33.
That pin has no format-2 emitter. The lattice pin stays
`vendor/muro` `v0.20.32`.
