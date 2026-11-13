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

.PHONY: agda audit book
agda:
	$(AGDA) $(RTS) $(AFLAGS) --safe agda/MuroBeam.agda

# The Muro book. smoke.muro imports the rest, and muro flattens imports,
# so this one check covers book/. The archive is Hex muro 0.20.33.
book:
	mix muro.check book/smoke.muro

# Refuse holes, postulated code, and a module that is not --safe.
audit:
	python3 scripts/audit.py
