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

.PHONY: agda audit book book-show conformance images \
	malonzo-image muro-beam build runner emit-check
agda:
	$(AGDA) $(RTS) $(AFLAGS) --safe agda/MuroBeam.agda

# MAlonzo event lists against the book printer. agda writes the Haskell
# and does not call GHC. scripts/conform.py compiles the driver with
# -O0 -j1 and diffs the two runs. --ghc-dont-call-ghc keeps the audit
# on --safe modules: the driver is scripts/, not an Agda main.
# Conform and the muro-beam CLI share MuroBeam.Show, so this
# comparison also pins the binary's event spelling and decimals.
conformance: book-show
	$(AGDA) $(RTS) $(AFLAGS) --safe --ghc --ghc-dont-call-ghc \
		--compile-dir=. \
		agda/MuroBeam/Conform.agda
	python3 scripts/conform.py

# The Muro book. smoke.muro imports the runtime book except the
# scheduler and the conformance printer. book/show.muro imports both.
# The archive is Hex muro 0.20.33. show.muro is book-show, so a printer
# typo fails that target and does not have to ride inside smoke.muro.
book:
	mix muro.check book/smoke.muro

book-show:
	mix muro.check book/show.muro

# Refuse holes, postulated code, and a module that is not --safe.
audit:
	python3 scripts/audit.py

# Parse, load, and run the checked-in images. agda writes the Haskell
# and does not call GHC. scripts/run_image.py compiles the pid-0 driver.
# scripts/build_runner.py writes MAlonzo/RunnerMain.hs and links
# muro-beam. That main reads the file, the fuel, and the optional
# --input bytes. load, the input parser, and drive stay in RunImage,
# which is --safe. The printed line is showDrove
# from MuroBeam.Show, the same printer make conformance checks.
malonzo-image:
	$(AGDA) $(RTS) $(AFLAGS) --safe --ghc --ghc-dont-call-ghc \
		--compile-dir=. \
		agda/MuroBeam/RunImage.agda

images: malonzo-image
	python3 scripts/run_image.py

muro-beam: malonzo-image
	python3 scripts/build_runner.py

build: muro-beam

runner: muro-beam
	python3 scripts/test_runner.py

# Hex muro 0.22.13 emits suc and plus 2 3 into a private MIX_HOME.
# The book pin stays 0.20.33. vendor/muro stays v0.20.32.
emit-check: muro-beam
	python3 scripts/emit_check.py
