# Check the v1a book. Agda 2.7 and 2.8 both accept these flags.
# CI installs `agda` on PATH. A command-line AGDA= overrides this default.
AGDA  ?= agda
# Cap the Haskell RTS so a check stays inside a few gigabytes.
RTS   ?= +RTS -M3G -A64M -RTS
# --no-libraries: the vendored stdlib ships extra .agda-lib files.
AFLAGS := --no-libraries \
	-i agda \
	-i vendor/muro/agda \
	-i vendor/agda-stdlib/src \
	--warning=noUnsupportedIndexedMatch

.PHONY: agda audit book book-show conformance
agda:
	$(AGDA) $(RTS) $(AFLAGS) --safe agda/MuroBeam.agda

# MAlonzo event lists against the book printer. agda writes the Haskell
# and does not call GHC. scripts/conform.py compiles the driver with
# -O0 -j1 and diffs the two runs. --ghc-dont-call-ghc keeps the audit
# on --safe modules: the driver is scripts/, not an Agda main.
conformance: book-show
	$(AGDA) $(RTS) $(AFLAGS) --safe --ghc --ghc-dont-call-ghc \
		--compile-dir=. \
		agda/MuroBeam/Conform.agda
	python3 scripts/conform.py

# The Muro book. smoke.muro imports the rest, and muro flattens imports,
# so this one check covers book/ except the conformance printer.
# The archive is Hex muro 0.20.33. show.muro is book-show, so a printer
# typo fails that target and does not have to ride inside smoke.muro.
book:
	mix muro.check book/smoke.muro

book-show:
	mix muro.check book/show.muro

# Refuse holes, postulated code, and a module that is not --safe.
audit:
	python3 scripts/audit.py
