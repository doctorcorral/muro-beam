# Check the v0 book. Agda 2.7 and 2.8 both accept these flags.
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

.PHONY: agda
agda:
	$(AGDA) $(RTS) $(AFLAGS) --safe agda/MuroBeam.agda
