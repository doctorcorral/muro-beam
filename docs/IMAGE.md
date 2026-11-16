# Image format v1

An image is the S-expression muro writes for `--backend mbi`. The
grammar and the byte-level rules are muro's `manual/mbi.md` at commit
`3f1cae2ae987d1ad27b301e0b1e1ddb03abdd988`. The printer is
`Muro.Beam.showPure`. This repository parses that text. It does not
define a second format.

One line, tokens separated by one space, a trailing newline. Naturals
are decimal with no leading zero except `0`. `w` is ω.

```
image ::= (muro-beam-image 1 (boundary 1) (entry <prog>))
prog  ::= (seq <gtm> (done))
gtm   ::= (gvar <nat>) | (gtyp <nat>) | (glam <pair> <gtm>) | (gpi <pair> <gtm>)
        | (gapp <gtm> <gtm>) | gze | (gsu <gtm>) | (gmatch <gtm> <gtm> <gtm>)
pair  ::= (<grade> <grade>)
grade ::= <point> | (iv <point> <point>)
point ::= <nat> | w
```

De Bruijn index 0 is the nearest binder. Domain types, annotations,
and match motives are not in the file. The grammar has `gtyp` even
though the emitter does not write it today. v1 has no `def` and no
process form. A program that needs those is not an image.

`MuroBeam.Image` is the record (`format`, `boundary`, the `<gtm>`) and
the printer. `MuroBeam.Parse` reads `String` to `Maybe Image`, and
refuses an index that does not fit its scope. `MuroBeam.Load.load`
accepts format 1 and `boundary-version`, then runs `checkP`. A success
is a `CheckedP`, built only after that check returns `ok []`.
`lowerP-wf` and `lowerP-safe` apply to anything loaded. The emitter
is outside the TCB for those two. Non-consequences of `load`:
`lower-safe` is not on the `lowerP` path (`Step* (lower e)` for a
pure `Checked`). `budget-adequate` is

```agda
(e : Checked) {s : Sys} →
NoEscape (term e) → MatchFree (term e) →
Step* (lower e) s → Inv tight s
```

`checkP` on `seq` runs `boundaryOk (inB? (comps Γ) e)`. `load` calls
that at `Γ = []` on the entry, so a success implies `InBoundary` of
the entry, and `inBoundary→noEscape` gives `NoEscape`. What is missing
is `MatchFree` (`match.mbi` loads and contains `gmatch`; `MatchFree`
has no `gmatch` clause) and the theorem's path: pure `Checked` /
`lower` / `Step*`, not `CheckedP` / `lowerP` / `PStep*`.
`no-stray-reply` needs `ReplyDone`.

The round trip `parse-show` is proved on the character list `render`
produces. `toList ∘ fromList` is not a `--safe` lemma, so the String
statement is not the theorem.

The plan's sketch said `--backend beam` and an arbitrary `PTm` entry.
The emitter writes `--backend mbi` and only `(seq <gtm> (done))`. The
emitted text is the one parsed here.

A complete sexp with no trailing newline, or a file that ends inside
an open sexp, is `truncated`. A newline while a sexp is still open is
`junk`, as is any other ill-formed token.
