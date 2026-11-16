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
accepts format 1 and `boundary-version`, then runs `checkP`. `lowerP`
is the initial system. The round trip `parse-show` is proved on the
character list `render` produces. `toList ∘ fromList` is not a
`--safe` lemma, so the String statement is not the theorem.

The plan's sketch said `--backend beam` and an arbitrary `PTm` entry.
The emitter writes `--backend mbi` and only `(seq <gtm> (done))`. The
emitted text is the one parsed here.

A complete sexp with no trailing newline, or a file that ends inside
an open sexp, is `truncated`. A newline while a sexp is still open is
`junk`, as is any other ill-formed token.
