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
`glam-reply.mbi`, `gpi-reply.mbi`, `gtyp-reply.mbi`, and
`nested-seq.mbi` are not emitter goldens. They are surface process
entries written for this loader. `spawn-done.mbi` and `bare-done.mbi`
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
`protocol slot is not moved`. `alias-await.mbi` is refused with
`reply result is not fresh`. `gmatch-await.mbi` is a `gmatch`
body, `gvar-await.mbi` is a `gvar` under `recv`, and
`gref-chain.mbi` is a `gref` whose definition is itself a `gref`.
Those three are the same refusal. `gref-await.mbi` is a loadable
direct fresh `gref` of `gze` whose continuation awaits the moved
slot. `glam-g1.mbi` is a `recv` at grade 1 whose `seq` body is a
`glam`. `checkP` refuses it with `glam reply under g1`.
`glam-reply.mbi` is that `(glam (w 0) gze)` at scope 0. No `g1` is
in scope, so load accepts it. `drive` halts and keeps `v-`: the
payload is a closure. `gpi-reply.mbi` is a direct `(gpi (w 0) gze)`
reply. It allocates nat zero and halts with the same line as the
`gze` reply. `gtyp-reply.mbi` is a direct `(gtyp 0)`. The child
sends a nat, the parent receives it at `(w w)`, and the reply body
names that variable. `drive` promotes the cell and halts
(`h6l0p3 v0`). A scope-0 `gtyp` is out of scope.
`nested-seq.mbi` puts `(gref 0)` in a nested `seq`. The image's
definition list is attached only to the root `seq`, so that body
is `bad gref`. `alias-bind.mbi` is a fresh `gsu`
reply. A normal run promotes that cell and halts with `v1`.
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
