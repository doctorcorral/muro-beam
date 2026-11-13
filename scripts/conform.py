#!/usr/bin/env python3
# Diff the MAlonzo report against the book printer.
#
# agda --ghc --ghc-dont-call-ghc has already written
# MAlonzo/Code/MuroBeam/Conform.hs. The Agda name `report` becomes
# d_report_<id>. The id is not stable, so this script reads it.
# The driver is handwritten Haskell: an Agda main would be IO, and IO
# is not --safe, and a non-safe file under agda/ fails scripts/audit.py.
#
# The book side is scripts/book_show.exs. It evaluates the closed show
# definitions. This script does not contain a copy of the expected list.

import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HS = os.path.join(ROOT, "MAlonzo", "Code", "MuroBeam", "Conform.hs")
MAIN = os.path.join(ROOT, "MAlonzo", "ConformMain.hs")
BIN = os.path.join(ROOT, "conform-malonzo")


def fail(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def report_symbol():
    if not os.path.isfile(HS):
        fail("missing " + HS + " (run agda --ghc first)")
    names = []
    with open(HS, encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r"^(d_report_\d+)\s+::", line)
            if m:
                names.append(m.group(1))
    if len(names) != 1:
        fail("expected one d_report binding, found " + repr(names))
    return names[0]


def write_main(symbol):
    os.makedirs(os.path.dirname(MAIN), exist_ok=True)
    with open(MAIN, "w", encoding="utf-8") as fh:
        fh.write(
            "\n".join(
                [
                    "module Main where",
                    "import qualified Data.Text.IO as TIO",
                    "import MAlonzo.Code.MuroBeam.Conform (" + symbol + ")",
                    "main :: IO ()",
                    "main = TIO.putStr " + symbol,
                    "",
                ]
            )
        )


def rte_dir():
    agda = os.environ.get("AGDA", "agda")
    data = subprocess.check_output(
        [agda, "--print-agda-data-dir"], text=True
    ).strip()
    rte = os.path.join(data, "MAlonzo", "src")
    if not os.path.isfile(os.path.join(rte, "MAlonzo", "RTE.hs")):
        fail("MAlonzo RTE not at " + rte)
    return rte


def muro_ebin():
    home = os.environ.get("MIX_HOME", os.path.expanduser("~/.mix"))
    ebin = os.path.join(home, "archives", "muro-0.20.33", "muro-0.20.33", "ebin")
    if not os.path.isdir(ebin):
        hits = sorted(glob.glob(os.path.join(home, "archives", "muro-*", "*", "ebin")))
        fail("muro 0.20.33 archive not in " + home + " (saw " + repr(hits) + ")")
    return ebin


def run(cmd, **kw):
    print("+ " + " ".join(cmd), file=sys.stderr)
    return subprocess.run(cmd, check=True, cwd=ROOT, **kw)


def capture(cmd):
    print("+ " + " ".join(cmd), file=sys.stderr)
    proc = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=None)
    if proc.returncode != 0:
        fail("command failed: " + " ".join(cmd))
    return proc.stdout


def main():
    if shutil.which("ghc") is None:
        fail("ghc is not on PATH")
    if shutil.which("elixir") is None:
        fail("elixir is not on PATH")
    symbol = report_symbol()
    print("report symbol " + symbol, file=sys.stderr)
    write_main(symbol)
    rte = rte_dir()
    run(
        [
            "ghc",
            "-O0",
            "-j1",
            "-i" + ROOT,
            "-i" + rte,
            "-package",
            "text",
            "-o",
            BIN,
            MAIN,
        ]
    )
    malonzo = capture([BIN])
    book = capture(["elixir", "-pa", muro_ebin(), os.path.join(ROOT, "scripts", "book_show.exs")])
    if malonzo == book:
        sys.stdout.buffer.write(malonzo)
        print("MATCH", file=sys.stderr)
        return
    out = os.path.join(tempfile.gettempdir(), "beam-conf-mismatch")
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "malonzo.txt"), "wb") as fh:
        fh.write(malonzo)
    with open(os.path.join(out, "book.txt"), "wb") as fh:
        fh.write(book)
    print("MISMATCH", file=sys.stderr)
    print("--- malonzo", file=sys.stderr)
    sys.stderr.buffer.write(malonzo)
    print("--- book", file=sys.stderr)
    sys.stderr.buffer.write(book)
    print("wrote " + out, file=sys.stderr)
    sys.exit(1)


if __name__ == "__main__":
    main()
