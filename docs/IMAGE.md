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
one-index shape. `checkP` accepts that shape only as the parent root
of a `spawn` whose thinning keeps the named slot and whose grade on
that slot moves. Anywhere else the reason is
`protocol is not a spawn reply`. A skipped or copied slot is
`protocol slot is not moved`.

`awaitT`, `ignoreT`, `flushT`, `ncheckT`, and `ndemonT` are not
surface syntax. `markProto` writes `awaitT`, `ignoreT`, and `ncheckT`
once a moved reply has an object index. `flushT` is what `arm1`
writes from `ignoreT`. `ndemonT` is what `npeek1` writes from
`ncheckT` when the mailbox does not hold the tag. A trace steps
through those forms. The parser refuses all five heads with
`not surface`.

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
`lowerP-safe` apply to anything loaded. The `AllInv` conjunct of
`lowerP-safe` is `residual-inv-refs`, which holds of every `Sys`.
The trace is used for `WF` only. The emitter is outside the
TCB for those two. `lower-safe` is not that claim: it is
`Step* (lower e)` for a pure `Checked`.
Non-consequences of `load`: `budget-adequate` is

```agda
(e : Checked) {s : Sys} →
NoEscape (term e) → MatchFree (term e) →
Step* (lower e) s → Inv tight s
```

`inB?` runs on a `seq` body (`boundaryOk (inB? (comps Γ) e)` in that
clause) and on each definition (`checkDef`). A `done`, `spawn`,
`send`, or `recv` entry does not call `inB?`. `load` of a root `seq`
runs it at `Γ = []` on the body `e`. That decision is `InB [] e` for
that body, not for an arbitrary entry.
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
`checkP` still accepts a hand-built tagged form: `replyTok` is
`sat g1 (finᶜ 1)`, which holds, and the continuation is checked
with `checkP`. Parse refuses those words with `not surface`, so
`load` never builds them. `markProto` writes `awaitT`, `ignoreT`,
and `ncheckT`. `arm1` writes `flushT`. `npeek1` writes `ndemonT`
when the mailbox does not hold the tag. Those runtime terms are
not re-checked.

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
`saved ∷ seg ∷ []` when the continuation is not `done`, except an
aliased non-g1 reply, which is refused. A `done` continuation on
that stack stays parked, so a pure image still never reaches `done`. The kept nat is the value on that returned
reference. A closure keeps nothing (`v-`). Fuel 0 does not step:
the line is `fuel [] h0l0p1 v-`.

A process image is the same path: `load`, then `lowerP`, then
`drive`. `spawn t[]` of two `done` terms halts. A bare `(done)`
halts. `examples/images/send-recv.mbi` binds `2` at ω, because the
continuation is `recv`. The child sends that variable to pid 0 and
the parent receives it at `(w 0)`. The send is `Kcopy`. The run
halts and keeps `v2`.

`seq` binds its result at grade 1 when the continuation is a reply
root: `spawn` of a `keep` whose parent root is `await`, `ignore`, or
`nignore` of the slot the thinning kept at index 0. `bind1` regrades
that returned cell from ω to `g1` when the cell is not already `g1`
and it is the only reference to its object. The following spawn
records a move, and `markProto` rewrites that parent root to the
tagged form the reply steps match. `spawn-await.mbi` and
`spawn-ignore.mbi` halt. The child sends
`ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0))))`
with kind `Kmove`, the schedule collects `(0 1 2 3)`, the fingerprint
is `h4l0p2`, and the kept nat is the seq payload `v0`.
`await-halted`, `await-val`, `ignore-halted`, and `ignore-val` are
regression pins: closed `refl`s for the hand-built terms `spawnAwait`
and `spawnIgnore` at `driveFuel` (16). They are not a load of
`spawn-await.mbi` or `spawn-ignore.mbi`. The files are what the
harness and the binary run. `await-line` and `ignore-line` are the
printed lines of those hand-built terms, the same kind of pin. That
schedule runs the reply. It is not a proof of `no-stray-reply`: that
theorem still needs `ReplyDone` at the start.

A protocol form that is not that spawn parent root is refused at
`checkP` with `protocol is not a spawn reply`. `await-seq.mbi`,
`ignore-seq.mbi`, and `nignore-seq.mbi` are that refusal. A bare
`seq` of `await`, `ignore`, or `nignore` never spawns. A protocol
buried under another constructor, including `seq` under `spawn`, is
the same refusal. `buried-await.mbi` is that shape.
`markProto` still rewrites only the root, so the checker refuses the
shape it would leave untouched. A spawn that skips the protocol slot,
or that keeps it at a copied grade, is refused with `protocol slot is
not moved`. `skip-await.mbi` is the skip. `copy-await.mbi` is a closed
`recv` at ω whose `keep` is a copy.

`nignore` at a spawn parent root takes the same grade-1 binding and
does run. `spawn-nignore.mbi` is that image. Its steps are the naive
peek and demonitor, so the reply is not flushed and one cell stays
live. The `showDrove` line keeps that cell: `tr-collect(1 2)`,
fingerprint `h3l1p2`, value `v0`. `nignore-halted`, `nignore-val`,
and `nignore-line` are regression pins for that run at `driveFuel`.
A bare `nignore`
under `seq` is the refusal above.

A reply root's `seq` body has to be a fresh head. `freshHead` is
`gze`, `gsu` (the successor cell, not the argument), `glam`, `gtyp`,
or `gpi`. `freshBody` also allows one `gref` whose definition is a
fresh head, and refuses a chain. `gvar`, `gapp`, and `gmatch` are not
fresh. `guardReply` refuses a non-fresh body with `reply result is not
fresh` after `decideB` and before the continuation. `alias-await.mbi`
is that refusal: the body is an application that can return a pointer
the closure still holds. `gmatch-await.mbi` is a `gmatch` body.
`gvar-await.mbi` is a `gvar` under `recv`. `gref-chain.mbi` is a
`gref` whose definition is itself a `gref`. The proofs are
`aliasAwait-no`, `gmatchAwait-no`, `gvarAwait-no`, and `grefChain-no`
on those hand-built terms. `seq-reply-fresh` says an accepted reply
`seq` has `freshBody ≡ true`.

`bind1` refuses an aliased non-g1 cell: that branch is `nothing`.
`bind-count-refuses` is that fact for every open reply stack whose
returned cell is not `g1` (`isG1 ≡ false`) and whose `count` is not 1.
A cell that is already `g1` does not consult the count. Under `WF`,
`hasG1 i (refsOf s) ≡ true` and `count i (refsOf s) ≢ 1` contradict
`Grade1Unique`, so an already-`g1` cell whose count is not 1 is not a
well-formed state. The branch still does not read the count. A second
`g1` alias would break `Grade1Unique`, and installing the ω reference
would leave `await` and `ignore` untagged. `bind-promotes` says that
when the returned cell is not `g1` and `count` of its object is 1, the
installed head is `regrade r g1`. `regrade-move` says that head is
`Kmove`. `split-head` says a kept move at index 0 is the head of the
move list. `reply-slot` says `applyMoves` of a list that starts with
`(zero , τ)` tags a protocol root. `spawn-reply-tag` is that fact
after `split-head`. It is not `reply-slot`. `bind-spawn-tag` composes
`bind-count-one`, `bind-promotes`, `regrade-move`, `split-keep-move`,
and `spawn-reply-tag`: a promoting `bind1` whose continuation is
`spawn (keep th) ch pa`, followed by one `spawn1`, puts
`protoTag (obj r) pa` in the parent. `bind-count-one` derives
`(count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) ≡ true` from
`bind1 ≡ just`, `isG1 (checked r) ≡ false`, and that reply stack:
the `false | false` clause is `nothing`, so the count bit is 1, and
that bit selects the promoting arm. The premises `bind1 ≡ just`
does not discharge are `isProtoAt zero pa ≡ true`,
`isG1 (checked r) ≡ false`, and
`splitGo (suc zero) (placeholder h) th (env ++ cenv) ≡ just (ce , pe , mv)`.
`isG1 ≡ false` stays a premise because the already-`g1` arm of
`bind1` returns `just` without consulting the count.
A later `keep` of a `g0` cell, or a thinning that does not match the
tail, is still `nothing`. `freshBody` is not a premise. The already-`g1`
branch is not this lemma. `openCont` of a `spawn` holds by computation.
`bind1` does not change the heap, so the placeholder is the cell
`spawn1` allocates. The conclusion names both processes: after `bind1`,
pid `i` has control `spawn (keep th)` with head `regrade r g1`; after
`spawn1`, that process has control `protoTag (obj r) pa`.
A fresh head allocates at `length` of the heap. Under `Bound` that
index was not named, and the returning step adds one reference.
That is why the count is 1 on the images the harness runs. It is the
allocator's story. It is not a theorem from `checkP` to the tag, and
`bind-spawn-tag` does not claim that a loaded fresh body promotes. `alias-await-probe` is a closed test of
`bind-count-refuses` on the hand-built term `spawnAwait`: the plant
adds a second reference and `bind1` is `nothing`. The string is
`refuse: aliased reply result`. `alias-bind.mbi` is a file with
that spawn shape and body `gsu gze`. `drive` of the file still
promotes and halts. `alias-bind-plant` is `aliasImage` of that
file's text, the same plant. `grefAwait-ok` is the hand-built direct fresh `gref`.
`examples/images/gref-await.mbi` is that program as a file: `load`
accepts it, and `drive` promotes the cell the definition allocates.
`glam` is a fresh head, and `evalTm` takes it only when
`not (anyG1 env)`. `guardGlam` refuses a direct `glam` reply body
when the context already has a `g1` (`glam reply under g1`).
`glamG1-no` is that equation. `glam-g1.mbi` is the file: a `recv` at
grade 1 whose `seq` body is `glam`. `inB?` refuses the same body.
`glam-reply.mbi` is that same `(glam (w 0) gze)` at scope 0, where
no `g1` is in scope, so `guardGlam` allows it. `load` accepts it.
`drive` promotes the closure and halts. The payload is not a nat, so
the line keeps `v-`. `gpi-reply.mbi` is a direct `(gpi (w 0) (gsu gze))`
reply. `evalTm` of `gpi` ignores the body and allocates nat zero, so
the `showDrove` line is that allocation (`v0`), not the successor
the body would be. `gtyp-reply.mbi` is a direct `(gtyp 0)`.
A scope-0 `gtyp` is `out of scope`, and a binder whose type grade is
0 is `type grade 0 does not allow 1 uses`. The image spawns a child
that sends a closure, `(glam (w 0) (gsu gze))`; the parent receives
it at `(w w)` and the reply body is `(gtyp 0)`. `drive` keeps the
first delivered nat. `readNat` of a closure is nothing, so `v0` is
the cell `evalTm` allocated for `gtyp`, not the received value. A
child that sent `gsu gze` would keep `v1`. The run promotes that
cell and halts (`h6l0p3 v0`).
A `gref` of a `glam` runs under `[]`, so `guardGlam` does not refuse
it. An ω binder can still hold a runtime `g1` reference;
`guardGlam` does not see that. A nested `seq` does not inherit the
image's definition list (`toP` builds `seq []`). `nested-seq.mbi`
is a root `seq` of `gze` whose continuation is `seq (gref 0)`, with
one definition `gze`. The nested body is `bad gref`. The files `spawn-await.mbi` and
`spawn-ignore.mbi` are the fresh `gze` images the harness runs.
The halt pins are `await-halted` and `ignore-halted` on the
hand-built terms `spawnAwait` and `spawnIgnore`. `glam-halted`,
`gpi-halted`, and `gtyp-halted` are the same kind of pin for
`glamReply`, `gpiReply`, and `gtypReply`.

`run` in the pid-0 harness is `seq1` then `runFor`. It does not call
`bind1`. `run` of `send-recv.mbi` prints `nat 2`, the seq payload,
with the spawn still parked. `run` of `spawn-done.mbi` prints
`stuck`, because `seq1` does not return a value. `run` of
`spawn-await.mbi` prints `nat 0`. Calling `bind1` after that eval
would resume the spawn, and the harness would print `stuck`.

`imgFuel` is 1000, the same default as `scripts/build_runner.py`
`DEFAULT_FUEL`. `drive` of `plus.mbi` at that fuel stops `stuck 0`
and keeps `v5` on both the harness and the binary. `driveFuel` in
`MuroBeam.SchedThm` stays 16. The closed spawn proofs and the
`glam` and `gpi` reply pins finish inside it. `gtypReply` does not:
it is out of fuel at 16 and halted at `gtypFuel` (20). `drive-fuel` says a run that has already halted at
fuel n returns the same `Drove` at every m ≥ n. `await-fuel`,
`ignore-fuel`, and `nignore-fuel` are that fact for the three reply
images at `imgFuel`. `await-line`, `ignore-line`, and `nignore-line`
are the `showDrove` content pins at `driveFuel`. `await-img`,
`ignore-img`, and `nignore-img` are the fuel-bridge equalities:
the line at `imgFuel` equals the line at `driveFuel`. `glam-line`,
`gpi-line`, and `gtyp-line` are the same kind of pin for
`glamReply`, `gpiReply`, and `gtypReply`. `glam` and `gpi` halt at
`driveFuel`. `gtypReply` is out of fuel at 16 and halts at
`gtypFuel` (20); `gtyp-img` bridges that line to `imgFuel`. These
pins are not a load of the files, and they do not discharge
`isProtoAt zero pa`, `isG1 (checked r) ≡ false`, or the tail
`splitGo`. The harness `drove` pins the content lines, and the
binary's line is the same text plus a newline.

What this shows is `load` of the `String` the Haskell main passed
in, then one fuelled `drive` of `lowerP`. File IO is Haskell, so
Agda never sees the bytes, only that `String`. `cliRun` keeps
`proj₁` of `drive` and discards `proj₂`. `cli-drove` is that
equation: a successful `load` makes `cliRun` the `cliBody` of that
`proj₁`. `drive-sound` names `proj₂` when a `Drove` is matched. It
is not a witness for the string `cliRun` returns. It does not show `budget-adequate`,
`MatchFree`, or `no-stray-reply`. A loaded `gmatch` is still
outside `MatchFree`. `lowerP-wf` and `lowerP-safe` are the
theorems that apply to a loaded process term. The `AllInv`
conjunct of `lowerP-safe` holds of every `Sys`, so it is not
information about the trace. There is no
equation `load s ≡ ok p` for a particular file. `load-sound` is
the `packLoad` equation for whatever string did load: a success
is that pack of the program `checkP` accepted. `load-checks` is
the checker equation, derived from it.

The Haskell main and the muro emitter are outside the TCB. `make
audit` does not see them. Hex muro 0.22.13 writes the checked-in
`suc.mbi` for `suc (suc 0)` and the checked-in `plus.mbi` for
`plus 2 3`. `make emit-check` runs that comparison in a private
`MIX_HOME` and then runs both files. The book archive stays 0.20.33.
That pin has no format-2 emitter. The lattice pin stays
`vendor/muro` `v0.20.32`.
