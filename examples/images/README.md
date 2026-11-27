# Images

The `.mbi` files here are copied from murolang/muro commit
`3f1cae2ae987d1ad27b301e0b1e1ddb03abdd988` (`examples/images/`).
That commit is the emitter (`manual/mbi.md`, `Muro.Beam.showPure`).
Do not edit them to match a local printer.

`pi.mbi` is in the grammar. `checkP` refuses it: a Π is checked in
spec, and the binder's type grade does not pay for the use.
`make images` records the reason.

`once` applied to `suc 0` is not an emitter golden. The harness
builds that image itself. On muro `3f1cae2`, compiled with
`MIX_BUILD_PATH=/private/tmp/beam-b2-build`, `Muro.Load.file` then
`Muro.Session.eval_run("once", [1], book)` and
`eval_run("applied", [], book)` both returned `1`. `drive` of that
image stops `stuck 0` and keeps `v1`.

`plus.mbi` is the image Hex muro 0.22.13 writes for
`def main : run Nat := plus 2 3`. That `plus` is the prelude. The
file is format 2: one closed definition, then the entry. `make
emit-check` diffs those bytes and runs both copies. `half.mbi` and
`iseven.mbi` are not emitter goldens. They are written by hand in
the same shape. `half` is `examples/half_ok.muro`. There is no
`isEven` run in that tree. `IsEven` there is a `spec` of `Type`.
`iseven.mbi` is a `Nat` transcription of that recursion (even is
`suc 0`, odd is `0`), so the harness can print a nat.

`Muro.Session.eval_run` on those three names does not return a nat.
On muro `e41936b` (`v0.20.15-3-ge41936b`), compiled with
`MIX_BUILD_PATH=/tmp/b1c-mix2`, `eval_run` returned:

- `plus` `[2, 3]` → `{:run, "plus", [2, 3]}` (prelude and `half_ok`)
- `half` `[0]`, `[1]`, `[4]`, `[5]` → `{:run, "half", args}`
- `IsEven` `[0]`, `[1]`, `[4]`, `[5]` → `{:run, "IsEven", args}`

The same `plus` and `half` calls on muro `3f1cae2`
(`MIX_BUILD_PATH=/private/tmp/beam-b2-build`, `examples/half_ok.muro`)
returned `{:run, "plus", [0, 3]}`, `{:run, "plus", [2, 0]}`,
`{:run, "half", [0]}`, and `{:run, "half", [5]}`.

`spawn-done.mbi`, `bare-done.mbi`, `send-recv.mbi`, `await-seq.mbi`,
`ignore-seq.mbi`, `nignore-seq.mbi`, `spawn-ignore.mbi`,
`spawn-await.mbi`, `spawn-nignore.mbi`, `def-spawn.mbi`,
`skip-await.mbi`, `copy-await.mbi`, `buried-await.mbi`,
`alias-await.mbi`, `gmatch-await.mbi`, `gvar-await.mbi`,
`gref-chain.mbi`, `alias-bind.mbi`, `gref-await.mbi`, `glam-g1.mbi`,
`glam-reply.mbi`, `gpi-reply.mbi`, `gtyp-reply.mbi`,
`nested-seq.mbi`, `comp-await.mbi`, `comp-ignore.mbi`,
`comp-nignore.mbi`, `type-await.mbi`, `type-ignore.mbi`,
`type-nignore.mbi`, `recv-move.mbi`, `recv-move-ignore.mbi`,
`recv-move-nignore.mbi`, `recv-move-shift.mbi`, `recv-keep.mbi`,
`recv-keep-copy.mbi`, `recv-keep-beside.mbi`,
`recv-keep-beside-ignore.mbi`, and `recv-keep-beside-nignore.mbi`
are not emitter goldens.
They are surface process entries written for this loader.
`tagged-spawn.mbi`, `buried-awaitT.mbi`, `buried-ignoreT.mbi`,
`buried-flushT.mbi`, `buried-ncheckT.mbi`, and `buried-ndemonT.mbi`
are not surface entries. Parse refuses each with `not surface`.

`spawn-done.mbi` and `bare-done.mbi`
halt. `send-recv.mbi` binds at ω and halts with `v2`. `def-spawn.mbi`
halts with `v0`. `spawn-await.mbi` and `spawn-ignore.mbi` halt with
`v0`. The harness and the binary check those files. `await-halted`
and `ignore-halted` are `refl` pins of the hand-built terms
`spawnAwait` and `spawnIgnore`, not of a load of the files. `spawn-nignore.mbi` is the same spawn with `nignore`. It
halts with `v0` and fingerprint `h3l1p2`: the reply is not flushed,
so collect leaves the cell at index 0. `await-seq.mbi`,
`ignore-seq.mbi`, and `nignore-seq.mbi` are refused at load
(`protocol is not a spawn reply`). `buried-await.mbi` is the same
refusal. `skip-await.mbi` and `copy-await.mbi` are refused with
`protocol slot is not moved`. `recv-move.mbi` is a `g1` `recv`
binder holding the ω cell `(gsu gze)` that the child sends.
`checkP` refuses it with `protocol slot came from recv`.
`recvMoveAwait-no` is that equation. It is not a run of the file.
`recv-move-ignore.mbi` and `recv-move-nignore.mbi` are that same
term shape and the same refusal for `ignore` and `nignore`.
`recvMoveIgnore-no` and `recvMoveNignore-no` are those equations.
`recv-move-shift.mbi` is a different term: an `await` of that binder
at index 1, under a later `seq`, with no `Kcopy` sender.
`recvMoveShift-no` is the same guard on that shape.
`recv-keep.mbi` is that `g1` annotation with parent `done`. The keep
is not a protocol consumer, so `checkP` refuses it with `kept slot came
from recv`. `recvKeep-no` is that equation. `recv-keep-copy.mbi` is
an ω annotation with parent `done`, and `recvKeepCopy-no` is that
equation. `recv-keep-beside.mbi` keeps the recv binder beside an
`await` of another slot, and `recvKeepBeside-no` is that equation.
`recv-keep-beside-ignore.mbi` and `recv-keep-beside-nignore.mbi`
are that keep beside `ignore` and `nignore`.
`recvKeepBesideIgnore-no` and `recvKeepBesideNignore-no` are those
equations. The five pins are hand-built `refl`s. They are not a
load of the files, and they are not a grade theorem. `sendGate`
is unchanged.
`kind g1` is `Kmove`. The refusal is not a theorem that
the payload's kind matches the annotation. The stick on a bare
`await` is `recv-move.mbi`'s `Kcopy` payload, not a receive whose payload
is `Kmove`. `alias-await.mbi` is refused with
`reply result is not fresh`. `gmatch-await.mbi` is a `gmatch`
body, `gvar-await.mbi` is a `gvar` under `recv`, and
`gref-chain.mbi` is a `gref` whose definition is itself a `gref`.
Those three are the same refusal. `gref-await.mbi` is a loadable
direct fresh `gref` of `gze` whose continuation awaits the moved
slot. `glam-g1.mbi` is a `recv` at grade 1 whose `seq` body is a
`glam`. `checkP` refuses it with `glam reply under g1`.
`glam-reply.mbi` is that `(glam (w 0) gze)` at scope 0. No `g1` is
in scope, so load accepts it. `drive` halts and keeps `v-`: the
payload is a closure. `gpi-reply.mbi` is a direct `(gpi (w 0) (gsu gze))`
reply. `evalTm` ignores the successor body and allocates nat zero,
so the line is `v0`, not that successor. `gtyp-reply.mbi` is a
direct `(gtyp 0)`. The child sends a closure, `(glam (w 0) (gsu gze))`,
the parent receives it at `(w w)`, and the reply body names that
variable. `drive` keeps the first delivered nat. A closure is not a
nat, so `v0` is the cell `evalTm` allocated for `gtyp`. A child
that sent `gsu gze` would keep `v1`. The runner's `load` accepts
the file, and the runner's `drive` promotes the cell and halts
(`h6l0p3 v0`). That is an operational result of the harness and
the binary. It is not an Agda equation `load` of the file. A
scope-0 `gtyp` is out of scope.
`nested-seq.mbi` puts `(gref 0)` in a nested `seq`. The image's
definition list is attached only to the root `seq`, so that body
is `bad gref`. `nestedSeq-no` is the `checkP` pin of that hand-built
term. `comp-await.mbi` is `seq (gvar 0) done` under `await 0`.
`checkP` refuses it with `protocol slot is not one computational use`.
`compAwait-no` is that equation. `comp-ignore.mbi` and
`comp-nignore.mbi` are the same body under `ignore` and `nignore`.
`compIgnore-no` and `compNignore-no` are those equations.
`type-await.mbi` is `seq (gtyp 0) done` under `await 0`. `checkP`
refuses it with `protocol slot has a type use`. `typeAwait-no` is
that equation. `type-ignore.mbi` and `type-nignore.mbi` are the same
body under `ignore` and `nignore`. `typeIgnore-no` and
`typeNignore-no` are those equations. `tagged-spawn.mbi` is a spawn
whose parent is `awaitT`. Parse refuses it with `not surface`.
`spawnTagAwait-no` is `checkP` of the hand-built term, `fail "tagged
spawn parent"`. It is not a load of the file. `buried-awaitT.mbi`
is `seq` of `awaitT` as that parent, and the four siblings are
`ignoreT`, `flushT`, `ncheckT`, and `ndemonT`. Parse refuses each
with `not surface`. `buriedTagAwait-no` and the four sibling pins
are `checkP` of the hand-built terms, `fail "tagged protocol"`.
`tagAwait-no` and its four siblings are the same refusal for a tag
that is not under `spawn`. Those equations are not a load of the
files. The old `replyTok` clause accepted the non-parent tags.
Promotion does not re-run `checkP`, so that acceptance is not
required. There is no theorem from `checkP` or `load` to promotion
and tagging. The `*-line` pins in `SchedThm`
are hand-built terms. This directory's files are what
`scripts/test_runner.py` runs. There is no Agda proof that `load`
of a file is the hand-built term. `spawnAwait-alias` plants on
`spawnAwait`, not on `alias-await.mbi`. `alias-bind.mbi` is a fresh `gsu`
reply. The runner's `load` accepts the file, and the runner's
`drive` promotes that cell and halts with `v1`. That is an
operational result of the harness and the binary. It is not an
Agda equation `load` of the file.
`--alias-bind` loads the same file, plants a second reference to
the returned cell, and `bind1` refuses (`aliased reply result`,
exit 0). A load refusal under `--alias-bind` exits 2 and writes
`muro-beam:` plus the reason on stderr.
Do not treat any of these as bytes `muro emit --backend mbi` writes.

`plus` and `half` are `run` definitions. `eval_def` asks `calls_out?`
of the whole body, including both match arms, and returns
`{:error, "run definition calls itself"}` before it steps.
`eval_run` turns any result other than `{:ok, v}` into
`{:run, name, args}`. `IsEven` is a `spec`, so it is not in the run
table and `eval_run` returns the same shape for that reason. A
non-recursive run in the same build does return a nat (`id 4` is
`4`). The harness numbers are what the CEK prints at fuel 200. They are
not Elixir results. `plus.mbi` is plus 2 3 and prints `nat 5`.
`half.mbi` is half 4 and prints `nat 2`. `iseven.mbi` is the
transcription at 4 and prints `nat 1`. The same definitions at the
other arguments Elixir was asked for print: half 0 `nat 0`, half 1
`nat 0`, half 5 `nat 2`, isEven 0 `nat 1`, isEven 1 `nat 0`, isEven 5
`nat 0`. plus 0 3 prints `nat 3` and plus 2 0 prints `nat 2`.

## B1d data images

`con0.mbi`, `con1.mbi`, `case0.mbi`, `case1.mbi`, `empty-gcase.mbi`,
and `case-miss.mbi` are hand-written. They are not emitter goldens:
`muro emit --backend mbi` still refuses data (`mbi:data`). `con0` is
nullary `(gcon 0)` and prints `con 0`. `con1` is `(gcon 1 gze)`.
`case0` matches tag 0 at arity 0 and returns `nat 0`. `case1` binds
the one field of `(gcon 1 gze)` and returns that nat. `empty-gcase`
is refused at `decideB` (`empty gcase`). `case-miss` loads and runs
to `stuck` (no matching tag).

Edge cases, also hand-written:

- `con2` is `(gcon 0 gze (gsu gze))` and prints `con 0`.
- `case2-last` binds both fields of `con2` and returns `gvar 0`, the
  last field: `nat 1`. `case2-first` returns `gvar 1`, the first
  field: `nat 0`.
- `case-first` has two arms on tag 1, arity 1. The first,
  `(gsu (gvar 0))`, wins: `nat 1`.
- `case-arity` has an arm on tag 0 with arity 1, then an arm on tag 0
  with arity 0. The scrutinee is `(gcon 0)`. The first tag hit has the
  wrong arity, and the run is `stuck`: `pickArms` does not fall
  through to the second arm.
- `gmatch-con` is `gmatch` on `(gcon 0)`. `gmatch` does not match a
  `con`, so it is `stuck`, like `gcase` on a nat.
- `case-w` matches an `ω` binder holding `(gcon 0 gze)` and returns
  the field: `nat 0`. `case-g1` is the same term with a `g1` binder.
  The pointer moves before the `cs` frame reads `predComp`, so the
  field binds at `g0` and the run is `stuck`. That is the `gmatch`
  limit in `docs/DESIGN.md`.

`drive` keeps no nat for a `con` result (`v-`). `MuroBeam.DataPins`
pins echo, run, and drive for every data image with `refl`, so
`make agda` checks these lines without GHC. It also pins the
`badFields` refusal of an aliased `g1` field on a hand-built heap,
because no image reaches that branch.

## B4a console images

The `out-*.mbi` files are hand-written format-3 images. No emitter
writes format 3 yet. The console is pid 1, so `(send 1 x k)` is a
write and the first spawned child is pid 2. `muro-beam` prints one
line per console message, then the summary line. `MuroBeam.IoPins`
pins every line below with `refl`.

- `out-one` writes `suc (suc 0)`: `2`, then `halted`.
- `out-two` writes `0` then `1`, in program order.
- `out-plus` is format 3 with the `plus` definition: `5`.
- `out-child`: a spawned child (pid 2) writes `1`.
- `out-relay`: the child sends `3` to pid 0, and pid 0 receives it and
  writes it to the console.
- `out-con` writes `(gcon 1 gze)`: `con 1`. `out-clo` writes a
  closure: `closure`.
- `out-none` is a format-3 pure entry. No line is written, and the run
  stops `stuck 0` with two processes.
- `out-v1` is the `out-one` shape in format 1. Format 1 boots no
  console, so pid 1 does not exist and the write never happens: the
  run stops `stuck 0` with one process (`p1`) and no output line.
  `outv1-drove` pins that its line equals `droveImage`.
- `out-recv` is a bare `recv` entry. The console is output only, so it
  deadlocks.
- `out-reply` sends a spawn reply to pid 1 instead of the parent. It
  loads (`checkP` does not read pids). The console prints `0`, and the
  parent's `await` deadlocks.

## B4b input images

The `in-*.mbi` files are hand-written format-4 images, and each
`in-*.in` file is the host input `make runner` passes with `--input`.
No emitter writes format 4 yet. Pids are entry 0, console 1, input
port 2, so the first spawned child is pid 3. The port sends each input
value to pid 0 in order; the entry reads them with `recv`. Each value
`n` costs the port about `2n + 1` steps (`tr-step 2`) before its
`tr-send 2 0`. `MuroBeam.InPins` pins every line below with `refl`.

- `in-echo` with `7`: receives one value and writes it: `7`.
- `in-two` with `3 5`: receives two values and writes them back in
  order: `3`, `5`.
- `in-succ` with `4`: writes `suc` of the value: `5`.
- `in-pred` with `3`: matches the value and writes its predecessor: `2`.
- `in-short` with `4`: receives twice but is given one value. There is
  no end-of-input message, so the second `recv` deadlocks after `4`.
- `in-echo` with `in-extra.in` (`1 2`): the second value is sent and
  stays in pid 0's inbox; the run still halts after `1`.
- `in-child` with `9`: the spawned child (pid 3) writes `1`, and pid 0
  echoes the input: `1`, `9`.
- `in-none` is a format-4 entry that ignores input: `1`. Run without
  `--input` it also writes `1` (`innone-empty`), and `in-echo` without
  `--input` deadlocks with three processes (`inecho-empty`).
- `in-v3` is `in-echo` in format 3. Format 3 has no input port, so
  `--input` is refused: `refuse: no input port`, exit 2.
- `in-bad.in` (`7 x`) is not naturals separated by whitespace:
  `refuse: bad input`, exit 2.
