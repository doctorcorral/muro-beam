# Image format

v1 is the S-expression muro writes for `--backend mbi` today. The
grammar and the byte-level rules of that line are muro's
`manual/mbi.md` at commit
`3f1cae2ae987d1ad27b301e0b1e1ddb03abdd988`. The printer there is
`Muro.Beam.showPure`. v2 is the same line with a `(defs …)` section
between the boundary and the entry. v3 (B4a) is the v1 or v2 line
run with the host console at pid 1, and v4 (B4b) is that line run
with the console and the host input port at pid 2 (below). This
repository parses all four. The emitter that writes the defs section
is not in this repository, and no emitter writes v3 or v4 yet.

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
        | (gref <nat>) | (gcon <nat> <btm>*) | (gcase <btm> <garm>+)
garm  ::= (garm <nat> <nat> <btm>)
pair  ::= (<grade> <grade>)
grade ::= <point> | (iv <point> <point>)
point ::= <nat> | w
```

`gcon` / `gcase` / `garm` are the B1d data forms. There is no format number bump: version 1 and 2 wrappers stay, and the `btm` grammar grows. `(gcon tag a0 … a_{k-1})` is a fully applied constructor; `tag` is the 0-based constructor index. `(garm tag arity body)` binds `arity` fields, last field nearest (de Bruijn 0), matching muro `to_db`. First matching tag wins. A tag hit with the wrong arity is stuck: `pickArms` stops at the first arm whose tag matches and does not fall through to a later arm with the same tag and the right arity (`case-arity.mbi`). With two arms on the same tag and arity, the first one runs (`case-first.mbi`). `garm+` is the grammar `decideB` accepts. `Parse` also reads `(gcase e)` with no arms; `decideB` then refuses it (`empty gcase`, `empty-gcase.mbi`). The parser does not check arity against a data table: there is none in the file. `gze` / `gsu` / `gmatch` are unchanged: `gcase` does not match `nat` / `suc↑`, and `gmatch` does not match `con`. The payload is `con tag fields`, a pointer like `suc↑` and `clo`. A `gcase` on a `g1` variable inherits the `gmatch` limit in `docs/DESIGN.md`: the pointer moves, the binder's slot becomes `g0`, the fields bind at `g0`, and a use of one is stuck (`case-g1.mbi`). The same term with an `ω` binder runs (`case-w.mbi`). `MuroBeam.DataPins` pins echo, run, and drive for every data image with `refl`. `muro emit --backend mbi` as of 0.22.x still refuses data (`mbi:data`); B1d is self-contained in muro-beam.

`<version>` is `1`, `2`, `3`, or `4`. Any other number is `bad version`. A file
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
of a `spawn` whose thinning keeps the named slot, whose grade on
that slot moves, and whose binder did not come from `recv`. A
recv-origin binder is refused even at `g1`. When that keep is the
protocol consumer the reason is `protocol slot came from recv`. A
keep that is not a protocol consumer is `kept slot came from recv`,
including a keep beside a protocol consumer of another slot.
A bare protocol form, or an untagged protocol form that is not the
spawn parent root, is `protocol is not a spawn reply`. That reason
is those forms. A skipped or copied slot is
`protocol slot is not moved`. The parent use of a kept moved slot has
to be exactly one computational use and zero type uses. A further
computational use, `seq (gvar 0) done` under `await 0`, is
`protocol slot is not one computational use`. `comp-await.mbi`,
`comp-ignore.mbi`, and `comp-nignore.mbi` are that file for `await`,
`ignore`, and `nignore`. `compAwait-no`, `compIgnore-no`, and
`compNignore-no` are the `refl`s. A type use in the
continuation, `seq (gtyp 0) done` under `await 0`, is
`protocol slot has a type use`. `type-await.mbi`, `type-ignore.mbi`,
and `type-nignore.mbi` are that file for the three consumers.
`typeAwait-no`, `typeIgnore-no`, and `typeNignore-no` are the `refl`s.

`awaitT`, `ignoreT`, `flushT`, `ncheckT`, and `ndemonT` are not
surface syntax. `markProto` writes `awaitT`, `ignoreT`, and `ncheckT`
once a moved reply has an object index. `flushT` is what `arm1`
writes from `ignoreT`. `ndemonT` is what `npeek1` writes from
`ncheckT` when the mailbox does not hold the tag. A trace steps
through those forms. The parser refuses all five heads with
`not surface`. A spawn whose parent is already one of them is
refused by `checkP` with `tagged spawn parent`, because `isProtoAt`
is false on a tag and the generic spawn arm would skip the move,
one-computational-use, and zero-type checks. `spawnTagAwait-no`,
`spawnTagIgnore-no`, `spawnTagFlush-no`, `spawnTagNcheck-no`, and
`spawnTagNdemon-no` are those equations on hand-built terms.
`tagged-spawn.mbi` is an `awaitT` parent. Parse refuses it with
`not surface` before `checkP`. The pin is not a load of the file.
A hand-built tagged form that is not the direct spawn parent is
refused with `tagged protocol`. `tagAwait-no`, `tagIgnore-no`,
`tagFlush-no`, `tagNcheck-no`, and `tagNdemon-no` are those
equations. A tag buried under `seq` as the spawn parent is the same
refusal: `containsTag` runs before the generic arm merges, so the
move, one-computational-use, and zero-type guards are not skipped.
`buriedTagAwait-no` and the four sibling pins are that equation.
`containsTag` also walks `send`, `recv`, `spawn`, `await`, `ignore`,
and `nignore`. `sendTagAwait-no`, `recvTagAwait-no`,
`spawnTagBuried-no`, `awaitUnderRecv-no`, `ignoreUnderRecv-no`, and
`nignoreUnderRecv-no` are those equations, each
`fail "tagged protocol"`. A tag in the continuation of a protocol
`await`, `ignore`, or `nignore` does not take that guard. `checkP`
of the continuation hits the tag clause. `awaitContTag-no`,
`ignoreContTag-no`, and `nignoreContTag-no` are those equations.
`tagAwait-no` is that same `tagged protocol` string for a tag that
is not a spawn parent. It is not `spawnTagAwait-no`, which is
`tagged spawn parent`.
`buried-awaitT.mbi` and its four siblings are the parse refusal
`not surface`. They are not a load of the pins. The old `replyTok`
clause accepted these forms. Promotion does not need that
acceptance: `markProto`, `arm1`, and `npeek1` write the tags after
`checkP`, and nothing runs `checkP` on them again.

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
format 1, 2, 3, or 4 and `boundary-version`, embeds the surface term, and
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
`checkP` refuses a hand-built tagged form that is not the direct
spawn parent (`tagged protocol`). It refuses a tagged spawn parent
with `tagged spawn parent`. Parse refuses those words with
`not surface`, so `load` never builds them. `markProto` writes
`awaitT`, `ignoreT`, and `ncheckT`. `arm1` writes `flushT`.
`npeek1` writes `ndemonT` when the mailbox does not hold the tag.
Those runtime terms are not re-checked. There is no theorem from
`checkP` or `load` to that promotion.

A complete sexp with no trailing newline, or a file that ends inside
an open sexp, is `truncated`. A newline while a sexp is still open is
`junk`, as is any other ill-formed token.

## Console (format 3, B4a)

A format-3 image is the format-1 or format-2 line with `3` in the
version slot. The grammar does not change, and `load` checks the
program exactly as it checks a v1 or v2 one. The number only reaches
the process layout. `MuroBeam.Load.loadIO` is `load` plus `Ports`
(`portsOf`: 4 is `stdio`, 3 is `console`, 1 and 2 are `none`). `loadIO-load` says a
`loadIO` success is a `load` success on the same text, so `load-sound`
and `load-checks` transfer. `loadIO-ports` says the ports are those of
the parsed format.

`MuroBeam.Port.lowerIO console p` is `lowerP p` with one more process
after the entry: pid 1, state `done`, control `idle`, no roots, an
empty inbox. That process is the console. Pids are entry 0, console 1,
and the first `spawn` is pid 2. A write is `(send 1 <index> <ptm>)`:
the existing `emit1` / `deliver1` pair, so the payload is moved or
copied by its `kind` exactly as for any other destination, and the
trace shows `tr-send <src> 1 …`. Nothing new enters `PTm`, `PStep`,
`checkP`, `decideB`, or the CEK. `deliver1` appends to a `done`
process's inbox and `wake` leaves it `done`, so `allDone` does not wait
on the console and a run can still halt. A format-1 or format-2 image
has no pid 1 until something spawns it: `(send 1 …)` from the entry
there is `blocked` and stops `stuck` (`out-v1.mbi`).

The host prints the console inbox of the system `drive` returns, one
line per message, in delivery order, before the summary line: a nat as
its decimal, a constructor as `con <tag>`, a closure as `closure`, and
a cell `readOut` cannot read as `stuck`. A `suc↑` chain is followed the
way `RunImage.readRef` does. The console is output only. In format 3
nothing feeds pid 0, so a `recv` entry with no sender deadlocks
(`out-recv.mbi`); format 4 adds the input port that does (Input,
below). On
`fuel`, `deadlock`, or `stuck`, the lines are what had been delivered
by then; a flight still in a sender's ether is not printed.

`lowerIO-wf` and `lowerIO-safe` are `lowerP-wf` and `lowerP-safe` for
that layout: the console holds no reference, so `refsOf` is still `[]`,
and every `PStep*` from it stays `WF`. `io-final-wf` applies
`drive-sound` and says the system the output is read from is `WF`.
`idle-quiet` says a `done` process with `idle` control has no enabled
wrapper, whatever its inbox, and `console-quiet-0` applies it to the
initial layout. Not proved: that every step keeps pid 1 `done` and
`idle`, that its inbox only grows, or that a halted run delivered
every flight. `checkP` does not look at pids, so a spawn reply sent to
pid 1 instead of the parent loads; the console prints it and the
parent's `await` deadlocks (`out-reply.mbi`).

`MuroBeam.IoPins` pins `ioImage` (`loadIO`, `drive` at `imgFuel` on
`lowerIO`, then the console lines and `showDrove`) on the text of every
`examples/images/out-*.mbi` file with `refl`, so `make agda` checks
those lines without GHC. `outv1-drove` pins that the format-1 file
prints the pre-B4 `droveImage` line. `make images` (`io` mode) and
`make runner` check the same strings through MAlonzo and the binary.

Why the format number and not a `(ports …)` section: the wrapper's
round trip `parse-show` is proved shape by shape (`legEmpty`,
`legCons`, `genEmpty`, `genCons`). A new section would add four more
shapes to that proof for one bit of information. The format field is
already read as any natural and round-trips. B4b's input port did not
need a section either: the image only says it wants the port (format
4); the values come from the host at run time, not from the file.

## Input (format 4, B4b)

A format-4 image is the format-1 or format-2 line with `4` in the
version slot. As for format 3, the grammar does not change and `load`
checks the program exactly as it checks a v1 or v2 one. `portsOf 4` is
`stdio`: the console at pid 1 and the input port at pid 2. Pids are
entry 0, console 1, input 2, and the first `spawn` is pid 3.

The values are naturals the host reads before the run. `muro-beam
IMAGE --input FILE` reads them from a file, and `--input -` from
stdin. `MuroBeam.Input.readInput` parses the text: decimal digit runs
separated by one or more spaces, tabs, carriage returns, or line
feeds, with leading and trailing separators allowed. An empty text is
no values. Leading zeros are read as the number. Any other character
is the load refusal `bad input`. Input to an image of format 1, 2, or
3 is the load refusal `no input port`, even when the text is empty.
Both refusals are exit 2 with `muro-beam:` and the reason on stderr.
The text is capped and decoded like the image (1 MiB, UTF-8); a read
failure is exit 1 with `muro-beam: cannot read input …` on stderr.

`MuroBeam.Port.lowerIn xs stdio p` is the console layout with one more
process: pid 2, state `ready`, no roots, an empty inbox, and the
control of `MuroBeam.Input.inputP xs` with an empty environment. That
term is, for each value, `(seq <numeral> (send 0 0 …))` with empty
defs, then `(done)`. So the port evaluates the numeral (`gsu` over
`gze`), binds it at ω (the continuation is a `send`, not a reply
root), sends it to pid 0 with `Kcopy`, and goes on to the next value.
The trace shows `tr-step 2` and `tr-send 2 0 …`. The program reads
with its own `recv`: an empty inbox parks pid 0 until the port
delivers. Nothing new enters `PTm`, `PStep`, `checkP`, `decideB`, or
the CEK. This is the BEAM port shape: a port delivers its data as
messages to the process it is connected to, and the owner reads them
from its mailbox. The console is still output only; input arrives at
pid 0, not through pid 1.

Values reach pid 0 in the order the host read them. A program that
receives more values than the host gave parks on an empty inbox after
the port has ended, and the run is a `deadlock` (`in-short`). Values
nobody receives stay in pid 0's inbox; a run that otherwise ends still
halts (`in-extra`). Without `--input`, a format-4 image runs with no
values: the port is `(done)` and ends at once, and a reading program
deadlocks. A numeral costs about `2n + 1` port steps and `n + 1`
cells, so a large value spends fuel (`41` is 83 steps).

`lowerIn-wf`, `lowerIn-safe`, and `in-final-wf` are the B4a facts for
every input: the port's control holds no reference at boot, so
`refsOf` is `[]` (`lowerIn-refs`), the layout is `WF` with an empty
heap, every `PStep*` from it stays `WF`, and the system `drive`
returns is `WF`. `lowerIO` is `lowerIn []`, and the B4a names are those
facts at `[]`. `stdio-quiet-0` is `console-quiet-0` for this layout.
`input-at` says pid 2 is `inputProc xs`, and `input-vals` reads `xs`
back out of `inputP xs`: every send goes to pid 0 and carries the slot
its `seq` just bound, in host order. `inputP-ok` is a closed `refl`
that `checkP` accepts the two-value port `3`, `0`. Not proved: that
`checkP` accepts `inputP xs` for every `xs` (the port is not a loaded
program, and boot does not run `checkP` on it), that every value
reaches pid 0 before the run stops, or how the port's sends interleave
with other senders to pid 0.

`MuroBeam.InPins` pins `ioImageIn` (`loadIO`, the port gate,
`readInput`, `drive` at `imgFuel` on `lowerIn`, then the console lines
and `showDrove`) on the text of every `examples/images/in-*.mbi` file
and its `in-*.in` input with `refl`, plus the no-input runs.
`make images` (`ioin` mode) and `make runner` (file and stdin) check
the same strings through MAlonzo and the binary.

## Runner

`muro-beam` reads one image file, an optional `--fuel N` (default
1000), and an optional `--input FILE` (`-` is stdin).
`scripts/build_runner.py` generates `MAlonzo/RunnerMain.hs` and
links it. That Haskell main is not an Agda module.
`MuroBeam.RunImage.cliRun` calls `loadIO`, then `drive` at that fuel
on `lowerIO`, from cursor 0, with no meetings and no kept nat. Formats
1 and 2 boot `lowerP` (`lowerIO none`); format 3 adds the console at
pid 1; format 4 adds the console and the input port at pid 2. With
`--input`, the main calls `cliRunIn` with the input text instead:
`loadIO`, the port gate (`no input port` unless format 4),
`readInput`, then `drive` on `lowerIn` (`bootIn`). The other entries
in that module (`runImage`, `driveImage`, `droveImage`, `aliasImage`,
`aliasCli`, `ioImage`) boot the same way with no input, through
`bootSys`. Stdout is zero or more console lines (formats 3 and 4
only, one per delivered message, see Console above) and then the
summary line: the outcome, the events, the fingerprint
`h<heap>l<live>p<procs>`, and the kept nat. The fingerprint counts
the ports as processes. The event spelling and the decimals are
`MuroBeam.Show`, the same module `MuroBeam.Conform` uses for the book,
so `make conformance` pins the CLI line as well. A numeral past eight
digits is `overflow`.

Exit 0 is `halted`, `deadlock`, or `stuck`. `muro-beam --alias-bind`
on a loaded image also exits 0 and prints `refuse: aliased reply result`.
A load refusal under that flag is exit 2. Exit 2 is a parse or load
refusal, and stderr is `muro-beam:` plus the reason (`bad version`,
`bad gref`, `junk`, `truncated`, `outside the boundary`, and the
others `load` returns, plus `no input port` and `bad input` under
`--input`). Exit 3 is out of fuel: stderr says so, and
stdout is still the partial line. Exit 1 is usage, a fuel argument
that is not a natural, or a file the main cannot read: a missing
file, permission denied, a directory, invalid UTF-8, or a file
larger than 1 MiB. Those read failures print `muro-beam: cannot
read …` on stderr (`cannot read input …` for the `--input` text). A
second `--input`, or `--input` with no file, is exit 1.

A pure image stops `stuck 0`. `seq1` pushes `saved` over `seg`.
`bind1` resumes a singleton `saved` stack, and it resumes
`saved ∷ seg ∷ []` when the continuation is not `done`, except an
aliased non-g1 reply, which is refused. A `done` continuation on
that stack stays parked, so a pure image still never reaches `done`. The kept nat is the value on that returned
reference. A closure keeps nothing (`v-`). Fuel 0 does not step:
the summary is `fuel [] h0l0p1 v-` for formats 1 and 2,
`fuel [] h0l0p2 v-` for format 3 (the console is the second process,
and nothing has been delivered, so no console line is printed), and
`fuel [] h0l0p3 v-` for format 4 (the input port is the third).

A process image is the same path: `loadIO`, then `lowerIO` (or
`lowerIn` with input), then `drive`. `spawn t[]` of two `done` terms halts. A bare `(done)`
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
`spawn-ignore.mbi` halt on the harness and on the binary.
`await-halted`, `await-val`, `ignore-halted`, and `ignore-val` are
regression pins: closed `refl`s for the hand-built terms `spawnAwait`
and `spawnIgnore` at `driveFuel` (16). They are not a load of
`spawn-await.mbi` or `spawn-ignore.mbi`. The files are what the
harness and the binary run. The exact `showDrove` schedule those
runs print, and that `await-line` and `ignore-line` pin on the
hand-built terms, is the child sending
`ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0))))`
with kind `Kmove`, collect `(0 1 2 3)`, fingerprint `h4l0p2`, and
kept nat `v0`. That schedule is the runner's line and the hand-built
pin. It is not an Agda theorem that `load` of either file is that
term. `await-line` and `ignore-line` are the printed lines of those
hand-built terms, the same kind of pin. That schedule runs the
reply. It is not a proof of `no-stray-reply`: that theorem still
needs `ReplyDone` at the start.

An untagged protocol form that is not that spawn parent root is
refused at `checkP` with `protocol is not a spawn reply`.
`await-seq.mbi`, `ignore-seq.mbi`, and `nignore-seq.mbi` are that
refusal. A bare `seq` of `await`, `ignore`, or `nignore` never
spawns. An untagged protocol buried under another constructor,
including `seq` under `spawn`, is the same refusal.
`buried-await.mbi` is that shape. A tagged form in that position is
`tagged protocol`, not this string. `buried-awaitT.mbi` does not
reach `checkP`: parse refuses it with `not surface`.
`markProto` still rewrites only the root, so the checker refuses the
shape it would leave untouched. A spawn that skips the protocol slot,
or that keeps it at a copied grade, is refused with `protocol slot is
not moved`. `skip-await.mbi` is the skip. `copy-await.mbi` is a closed
`recv` at ω whose `keep` is a copy. That sentence is the checker, not
a theorem that `spawn1` agrees with the binder grade. A `recv` binder
whose annotation is a move is a different refusal. `recvStep` installs
the sender's reference and does not regrade it, and `spawn1` moves or
copies by `kind (checked r)`. `kind g1` is `Kmove`. The annotation is
not a move guarantee. `checkP` refuses a protocol use of that slot with
`protocol slot came from recv`, including when the annotation is `g1`.
`recv-move.mbi` is the shape: the child binds `(gsu gze)` at ω because
the continuation is `send`, sends that cell with `Kcopy`, and the
parent receives it at `(1 0)` and awaits the slot. `recvMoveAwait-no`
is the `checkP` equation. `recv-move-ignore.mbi` and
`recv-move-nignore.mbi` are that same term shape and the same guard
for `ignore` and `nignore`. `recvMoveIgnore-no` and
`recvMoveNignore-no` are those equations. For that `Kcopy` payload,
`spawn1` would copy, the move list would be empty, and the parent
protocol form would stay untagged. On `recv-move.mbi` that means
`await1` would not match the `await`. The ignore and nignore files
are the same copy under those forms. A receive whose payload is
actually `Kmove` is not those three files: `spawn1` would move that
reference. There is no theorem that a `g1` annotation is that
payload. `recv-move-shift.mbi` is a different term. It awaits the
`recv` binder at index 1, under a later `seq`, and it has no such
sender. `recvMoveShift-no` is the same guard on that shape. The
`Kcopy` stick is not a claim about the shift image. A keep that is
not a protocol consumer is refused before `kind` is read, with
`kept slot came from recv`. That includes a keep of a recv binder
beside a protocol consumer of another slot: `isProtoAt` of the kept
index is false even though the parent is `await`, `ignore`, or
`nignore` of another slot. `recv-keep.mbi`
is the same `g1` annotation and the same `Kcopy` sender, with parent
`done`. `recvKeep-no` is that equation. `recv-keep-copy.mbi` is an ω
annotation (`Kcopy`) with parent `done`. `recvKeepCopy-no` is that
equation. `recv-keep-beside.mbi` keeps the recv binder beside an
`await` of the `seq` slot, and `recvKeepBeside-no` is that equation.
`recv-keep-beside-ignore.mbi` and `recv-keep-beside-nignore.mbi`
are that keep beside `ignore` and `nignore`.
`recvKeepBesideIgnore-no` and `recvKeepBesideNignore-no` are those
equations. All five are hand-built `refl` pins of the checker.
They are not a load of the files. None is a theorem that the
payload's kind differs from the annotation. `sendGate` is
unchanged. It still
classifies a send by the annotation. That is not a theorem that
`emit1` uses `kind (checked r)`. There is still no theorem from
`checkP` or `load` to promotion and tagging.

`nignore` at a spawn parent root takes the same grade-1 binding and
does run. `spawn-nignore.mbi` is that image. Its steps are the naive
peek and demonitor, so the reply is not flushed and one cell stays
live. The `showDrove` line keeps that cell: `tr-collect(1 2)`,
fingerprint `h3l1p2`, value `v0`. `nignore-halted`, `nignore-val`,
and `nignore-line` are regression pins of the hand-built term
`spawnNignore` at `driveFuel`. They are not a load of
`spawn-nignore.mbi`. `nignore-img` equates the line at `imgFuel`.
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
`gref` whose definition is itself a `gref`. The pins are
`aliasAwait-no`, `gmatchAwait-no`, `gvarAwait-no`, and `grefChain-no`,
the `checkP` equations on those hand-built terms. `seq-reply-fresh`
says an accepted reply `seq` has `freshBody ≡ true`.

`bind1` refuses an aliased non-g1 cell: that branch is `nothing`.
`bind-count-refuses` is that fact for every open reply stack whose
returned cell is not `g1` (`isG1 ≡ false`) and whose `count` is not 1.
A cell that is already `g1` does not consult the count. `reply-hasG1`
is `isG1 (checked r) ≡ true` to `hasG1 (obj r) (refsOf s)` when that
cell is the `rv` head on `saved ∷ seg ∷ []`. `reply-g1-count` applies
`Grade1Unique`, so under `WF` the count is 1. A count other than 1
is not a well-formed state. The branch still does not read the count. A second
`g1` alias would break `Grade1Unique`, and installing the ω reference
would leave `await`, `ignore`, and `nignore` untagged. `bind-promotes` says that
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
that bit selects the promoting arm. The hypotheses `bind1 ≡ just`
does not discharge are the continuation `spawn (keep th) ch pa`
(so the head slot is the one `keep` moves), `isProtoAt zero pa ≡ true`,
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
`bind-spawn-tag` does not claim that a loaded fresh body promotes. `spawnAwait-alias` is a closed test of
`bind-count-refuses` on the hand-built term `spawnAwait`: the plant
adds a second reference and `bind1` is `nothing`. It is not a load of
`alias-await.mbi`. `aliasAwait-no` is `checkP` of the hand-built
term `aliasAwait`, `fail "reply result is not fresh"`. The file is
the same reason at the loader. There is no proof that `load` of the
file is that term, and `bind1` does not run on a refused file. The
plant string `refuse: aliased reply result` is `spawnAwait-alias`
and `alias-bind-plant`, not `aliasAwait-no`. `alias-bind.mbi` is a file with
that spawn shape and body `gsu gze`. The runner's `drive` of the
file promotes and halts. That is an operational result of the
harness and the binary. It is not an Agda equation `load` of the
file. `alias-bind-plant` is `aliasImage` of that
file's text, the same plant. `grefAwait-ok` is the hand-built direct fresh `gref`.
`examples/images/gref-await.mbi` is that program as a file. The
runner's `load` accepts it, and the runner's `drive` promotes the
cell the definition allocates. That is the same kind of operational
result. It is not an Agda equation `load` of the file.
`glam` is a fresh head, and `evalTm` takes it only when
`not (anyG1 env)`. `guardGlam` refuses a direct `glam` reply body
when the context already has a `g1` (`glam reply under g1`).
`glamG1-no` is that equation. `glam-g1.mbi` is the file: a `recv` at
grade 1 whose `seq` body is `glam`. `inB?` refuses the same body.
`glam-reply.mbi` is that same `(glam (w 0) gze)` at scope 0, where
no `g1` is in scope, so `guardGlam` allows it. The runner's `load`
accepts the file, and the runner's `drive` promotes the closure and
halts. That is an operational result of the harness and the binary.
It is not an Agda equation `load` of the file. The payload is not a nat, so
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
child that sent `gsu gze` would keep `v1`. The runner's `load`
accepts the file, and the runner's `drive` promotes that cell and
halts (`h6l0p3 v0`). That is an operational result of the harness
and the binary. It is not an Agda equation `load` of the file.
A `gref` of a `glam` runs under `[]`, so `guardGlam` does not refuse
it. An ω binder can still hold a runtime `g1` reference;
`guardGlam` does not see that. A nested `seq` does not inherit the
image's definition list (`toP` builds `seq []`). `nested-seq.mbi`
is a root `seq` of `gze` whose continuation is `seq (gref 0)`, with
one definition `gze`. The nested body is `bad gref`. `nestedSeq-no` is that `checkP` equation
on the hand-built term. It is not a load of the file. The files `spawn-await.mbi` and
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
`ignore-fuel`, and `nignore-fuel` are that fact for the three
hand-built reply terms `spawnAwait`, `spawnIgnore`, and `spawnNignore`
at `imgFuel`. `await-line`, `ignore-line`, and `nignore-line`
are the `showDrove` content pins at `driveFuel`. `await-img`,
`ignore-img`, `nignore-img`, `glam-img`, and `gpi-img` are the
fuel-bridge equalities: the line at `imgFuel` equals the line at
`driveFuel`. `glam-line`, `gpi-line`, and `gtyp-line` are the
content pins for `glamReply`, `gpiReply`, and `gtypReply`. `glam`
and `gpi` halt at `driveFuel`. `gtypReply` is out of fuel at 16 and
halts at `gtypFuel` (20); `gtyp-img` bridges that line to `imgFuel`.
These
pins are not a load of the files, and they do not discharge the
continuation `spawn (keep th)`, `isProtoAt zero pa`,
`isG1 (checked r) ≡ false`, or the tail `splitGo`. `spawn-done-line`,
`bare-done-line`, `send-recv-line`, `def-spawn-line`, `gref-await-line`,
and `alias-bind-line` are the same kind of `refl` for the hand-built
terms `spawnClosed`, `doneClosed`, `sendRecv`, `defSpawn`, `grefAwait`,
and `aliasBind`, at `driveFuel`. `spawn-done-img`, `bare-done-img`,
`send-recv-img`, `def-spawn-img`, `gref-await-img`, and
`alias-bind-img` bridge those six lines to `imgFuel` by `drive-fuel`
and `cong showDrove`. They are not a load of the files. Equality of
the binary's line with the file bytes is what Python tests.
`nestedSeq-no` is `checkP` of the
nested `(gref 0)`, `fail "bad gref"`. Agda builds those terms by hand.
Nothing in Agda reads the `.mbi` bytes or proves that `load` of a file
is that term. `scripts/test_runner.py` is what runs the file and
compares the binary's line, including the newline the Haskell main
adds. The pure images in that file's `VALUES` table (`plus`, `half`,
`suc`, and the rest) stay Python-only. The harness `drove` pins the
content lines, and the binary's line is the same text plus a newline.

What this shows is `loadIO` of the `String` the Haskell main passed
in, then one fuelled `drive` of `lowerIO`. File IO is Haskell, so
Agda never sees the bytes, only that `String`. `cliRun` keeps
`proj₁` of `drive` and discards `proj₂`. `cli-drove` is that
equation: a successful `loadIO` makes `cliRun` the `ioBody` of that
`proj₁`. `cli-drove-none` is the format-1 and format-2 case: the
`cliBody` of `drive` on `lowerP`, the pre-B4 line. `drive-sound` names `proj₂` when a `Drove` is matched. It
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
