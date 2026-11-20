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
image ::= (muro-beam-image <version> (boundary 1) (entry <ptm>))
        | (muro-beam-image <version> (boundary 1) (defs <btm>+) (entry <ptm>))
ptm   ::= (done)
        | (send <nat> <nat> <ptm>)
        | (recv <pair> <ptm>)
        | (spawn <thin> <ptm> <ptm>)
        | (seq <btm> <ptm>)
        | (await <nat> <ptm>)
        | (ignore <nat> <ptm>)
        | (nignore <nat> <ptm>)
thin  ::= t[] | (keep <thin>) | (skip <thin>)
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
does not write it today.

The entry is a surface process term. `(seq <btm> (done))` is still a
legal entry, and the printer reprints that shape with the bytes it
used before process entries. `(send <pid> <index> <ptm>)` names a
destination pid as a raw natural, not a de Bruijn index, and a
payload index that must fit the scope. `(recv <pair> <ptm>)` binds
one variable at the pair's grades; the continuation is one scope
deeper. `(spawn <thin> <child> <parent>)` carries a thinning: `t[]`
is the empty thinning and is legal only at scope 0, `keep` hands the
nearest variable to the child, and `skip` leaves it with the parent.
A thinning that does not match the scope is `out of scope`, as is a
de Bruijn index that does not fit. `(await <index> <ptm>)`,
`(ignore <index> <ptm>)`, and `(nignore <index> <ptm>)` are the same
one-index shape.

`awaitT`, `ignoreT`, `flushT`, `ncheckT`, and `ndemonT` are not
surface syntax. `spawn` writes them once a moved reply has an object
index, and a trace steps through them. The parser refuses those five
heads with `not surface`.

`(defs …)` is the definition list of a root `seq`, including a `seq`
whose continuation is not `done`. A nested `seq` does not inherit
that list. Any other entry with a non-empty list is
`defs need a seq entry`.

Definitions are closed terms, in order. Definition i may `gref` its
own index or an earlier one. A later index is `bad gref`. The entry
may `gref` any definition and is not itself a definition. Each
definition is checked once, closed, against `inB? []` and `decideB`.
The entry is checked after that, at bound `length defs`.

What a later `muro emit --backend mbi` must write, when it learns
definitions and process terms: format 2 when there are definitions,
a `(defs …)` section of those closed terms in dependency order, and
an entry in the spelling above. A pure term stays
`(entry (seq <btm> (done)))`. A process term is the same `ptm`
grammar, and `(defs …)` is written only when the entry is a `seq`.
The five tagged heads are not written. Grades stay `(c t)`, with `w`
and `(iv a b)`. De Bruijn indices, no domain types, no motives, no
annotations. This loader re-checks, so that emitter stays outside
the TCB. A v1 file with no defs section stays valid.

`MuroBeam.Image` is the record (`format`, `boundary`, `defs`, `entry`)
and the printer. `entry` is a surface `SPtm 0`. `MuroBeam.Parse`
reads `String` to `Maybe Image`, and refuses a de Bruijn index or a
thinning that does not fit its scope. `MuroBeam.Load.load` accepts
format 1 or 2 and `boundary-version`, embeds the surface term, and
runs `checkP` on that program. A root `seq` receives the image's
definition list. A success is a `CheckedP`, built only after that
check returns `ok []`. A legacy entry loads as `seq defs btm done`,
the program load checked before process entries. `lowerP-wf` and
`lowerP-safe` apply to anything loaded. The emitter is outside the
TCB for those two. `lower-safe` is not that claim: it is
`Step* (lower e)` for a pure `Checked`.
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
The emitter writes `--backend mbi`. It writes `(seq <btm> (done))`
and, from muro 0.21.22, a defs section. It does not write `spawn`,
`send`, `recv`, `await`, `ignore`, or `nignore`. This parser accepts
the old lines and the surface process term above. The round trip
`parse-show` covers both. The surface type has no tagged constructor,
so the round trip does not mention `awaitT` and the other four.

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

A pure image stops `stuck 0`. `seq1` pushes `saved` over `seg`.
`bind1` resumes a singleton `saved` stack, and it resumes
`saved ∷ seg ∷ []` when the continuation is not `done`. A `done`
continuation on that stack stays parked, so a pure image still
never reaches `done`. The kept nat is the value on that returned
reference. A closure keeps nothing (`v-`). Fuel 0 does not step:
the line is `fuel [] h0l0p1 v-`.

A process image is the same path: `load`, then `lowerP`, then
`drive`. `spawn t[]` of two `done` terms halts. A bare `(done)`
halts. `examples/images/send-recv.mbi` binds `2` at ω, spawns a
child that sends that variable to pid 0, and receives it at `(w 0)`.
That run halts and keeps `v2`. `await`, `ignore`, and `nignore`
under that `seq` binder are accepted by `checkP`: the binder is ω,
and one computational use of ω is legal. `spawn` records a move
only for a finite point. An ω slot is copied and is not rewritten
to `awaitT`, `ignoreT`, or `ncheckT`. `await1` and the flush steps
match only those tagged forms, so a closed image does not run the
reply protocol. `await-seq.mbi`, `ignore-seq.mbi`, and
`nignore-seq.mbi` stop `stuck 0` with the bound nat.
`spawn-ignore.mbi` and `spawn-await.mbi` spawn, the child sends
the copied nat, and the parent stops `stuck 0` on the surface
form. That is a test of the schedule that actually runs. It is not
a run of `no-stray-reply`.

What this shows is `load` of the `String` the Haskell main passed
in, then one fuelled `drive` of `lowerP`. File IO is Haskell, so
Agda never sees the bytes, only that `String`. `cliRun` takes
`proj₁` of `drive`, so `PStep*` is typechecked into existence
rather than carried as a CLI witness. `drive-sound` is the
`PStep*` on that run. It does not show `budget-adequate`,
`MatchFree`, or `no-stray-reply`. A loaded `gmatch` is still
outside `MatchFree`. `lowerP-wf` and `lowerP-safe` are the
theorems that apply to a loaded process term. There is no
equation `load s ≡ ok p` for a particular file.

The Haskell main and the muro emitter are outside the TCB. `make
audit` does not see them. Hex muro 0.22.13 writes the checked-in
`suc.mbi` for `suc (suc 0)` and the checked-in `plus.mbi` for
`plus 2 3`. `make emit-check` runs that comparison in a private
`MIX_HOME` and then runs both files. The book archive stays 0.20.33.
That pin has no format-2 emitter. The lattice pin stays
`vendor/muro` `v0.20.32`.
