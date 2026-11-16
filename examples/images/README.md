# Images

The `.mbi` files here are copied from murolang/muro commit
`3f1cae2ae987d1ad27b301e0b1e1ddb03abdd988` (`examples/images/`).
That commit is the emitter (`manual/mbi.md`, `Muro.Beam.showPure`).
Do not edit them to match a local printer.

`pi.mbi` is in the grammar. `checkP` refuses it: a Π is checked in
spec, and the binder's type grade does not pay for the use.
`make images` records the reason.

`once` applied to `suc 0` is not an emitter golden. The harness
builds that image itself. The Elixir value for the same def, from a
throwaway build of this commit, is 1.
