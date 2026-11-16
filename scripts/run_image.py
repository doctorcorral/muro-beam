#!/usr/bin/env python3
# Run the checked-in images through the MAlonzo harness.
#
# agda --ghc --ghc-dont-call-ghc has written
# MAlonzo/Code/MuroBeam/RunImage.hs. The ids on d_runImage and
# d_echoImage are not stable, so this script reads them. The driver
# is handwritten Haskell under MAlonzo/, same rule as conform.py:
# IO stays out of agda/.

import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HS = os.path.join(ROOT, "MAlonzo", "Code", "MuroBeam", "RunImage.hs")
MAIN = os.path.join(ROOT, "MAlonzo", "ImageMain.hs")
BIN = os.path.join(ROOT, "image-malonzo")
IMG = os.path.join(ROOT, "examples", "images")

# Emitter goldens. Copied from muro 3f1cae2. once-app is not one of them.
GOLDENS = [
    "affine",
    "app",
    "drop",
    "iv",
    "match",
    "once",
    "pi",
    "reuse",
    "suc",
    "twice",
]

# Closures are values. app/match/suc compute. pi is outside the
# fragment checkP accepts (a Π body is checked in spec, and this
# binder's type grade is 0).
EXPECT = {
    "affine": "closure",
    "app": "nat 0",
    "drop": "closure",
    "iv": "closure",
    "match": "nat 0",
    "once": "closure",
    "pi": "refuse: type grade 0 does not allow 1 uses",
    "reuse": "closure",
    "suc": "nat 2",
    "twice": "closure",
}

# once (suc 0). Elixir, muro 3f1cae2 (0.21.11), MIX_BUILD_PATH
# /private/tmp/beam-b1b-build, Muro.Load.file of a one-shot book then
# Muro.Session.eval_run("once", [1], book) and eval_run("applied", [], book)
# both returned 1. The book has two run defs, so emit_mbi will not
# write it; the image below is the same term by hand.
ONCE_APP = (
    "(muro-beam-image 1 (boundary 1) (entry (seq "
    "(gapp (glam (1 0) (gvar 0)) (gsu gze)) (done))))\n"
)

# Outer g1, inner glams. InBoundary refuses a glam under a live g1.
CEX = (
    "(muro-beam-image 1 (boundary 1) (entry (seq (glam (1 0) "
    "(gapp (glam (w 0) (gapp (gvar 0) (gvar 0))) "
    "(glam ((iv 0 1) 0) (gvar 1)))) (done))))\n"
)

WRAP = "(muro-beam-image 1 (boundary 1) (entry (seq {body} (done))))\n"


def fail(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def symbol(prefix):
    if not os.path.isfile(HS):
        fail("missing " + HS + " (run agda --ghc first)")
    names = []
    with open(HS, encoding="utf-8") as fh:
        for line in fh:
            m = re.match(r"^(" + prefix + r"_\d+)\s+::", line)
            if m:
                names.append(m.group(1))
    if len(names) != 1:
        fail("expected one " + prefix + " binding, found " + repr(names))
    return names[0]


def rte_dir():
    agda = os.environ.get("AGDA", "agda")
    data = subprocess.check_output([agda, "--print-agda-data-dir"], text=True).strip()
    rte = os.path.join(data, "MAlonzo", "src")
    if not os.path.isfile(os.path.join(rte, "MAlonzo", "RTE.hs")):
        fail("MAlonzo RTE not at " + rte)
    return rte


def build():
    run_sym = symbol("d_runImage")
    echo_sym = symbol("d_echoImage")
    with open(MAIN, "w", encoding="utf-8") as fh:
        fh.write(
            "\n".join(
                [
                    "module Main where",
                    "import System.Environment (getArgs)",
                    "import qualified Data.Text as T",
                    "import qualified Data.Text.IO as TIO",
                    "import MAlonzo.Code.MuroBeam.RunImage (" + run_sym + ", " + echo_sym + ")",
                    "main :: IO ()",
                    "main = do",
                    "  args <- getArgs",
                    "  case args of",
                    '    ["run", path, fuel] -> do',
                    "      src <- TIO.readFile path",
                    "      TIO.putStr (" + run_sym + " src (read fuel :: Integer))",
                    '    ["echo", path] -> do',
                    "      src <- TIO.readFile path",
                    "      TIO.putStr (" + echo_sym + " src)",
                    '    _ -> fail "usage: image-malonzo run PATH FUEL | echo PATH"',
                    "",
                ]
            )
        )
    rte = rte_dir()
    subprocess.run(
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
        ],
        check=True,
        cwd=ROOT,
    )


def call(mode, path, fuel="200"):
    cmd = [BIN, mode, path] if mode == "echo" else [BIN, "run", path, fuel]
    proc = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE)
    if proc.returncode != 0:
        fail("harness failed: " + " ".join(cmd))
    return proc.stdout.decode("utf-8")


def write_tmp(text):
    fh = tempfile.NamedTemporaryFile("w", suffix=".mbi", delete=False)
    fh.write(text)
    fh.close()
    return fh.name


def check(name, got, want):
    if got != want:
        fail(name + ": got " + repr(got) + " want " + repr(want))
    print("ok " + name)


def main():
    if not os.path.isfile(BIN) or os.path.getmtime(HS) > os.path.getmtime(BIN):
        build()
    problems = 0
    try:
        for name in GOLDENS:
            path = os.path.join(IMG, name + ".mbi")
            with open(path, encoding="utf-8") as fh:
                raw = fh.read()
            echoed = call("echo", path)
            if echoed != raw:
                fail(name + " echo: got " + repr(echoed) + " want " + repr(raw))
            print("ok echo " + name)
            check(name, call("run", path), EXPECT[name])
        path = write_tmp(ONCE_APP)
        check("once-app", call("run", path), "nat 1")
        path = write_tmp(CEX)
        check("cex", call("run", path), "refuse: outside the boundary")
        cases = [
            ("bad-version", WRAP.format(body="gze").replace("image 1 ", "image 2 ", 1), "refuse: bad version"),
            ("bad-boundary", WRAP.format(body="gze").replace("(boundary 1)", "(boundary 2)", 1), "refuse: bad boundary version"),
            ("out-of-scope", WRAP.format(body="(gvar 0)"), "refuse: out of scope"),
            ("truncated", WRAP.format(body="gze").rstrip("\n"), "refuse: truncated"),
            # End of file inside an open sexp. No trailing newline.
            ("unclosed", "(muro-beam-image 1 (boundary 1) (entry (seq gze (done)))", "refuse: truncated"),
            # A newline while the outer sexp is still open is not a legal token.
            ("newline-open", "(muro-beam-image 1 (boundary 1) (entry (seq gze (done)))\n", "refuse: junk"),
            ("junk", "not-an-image\n", "refuse: junk"),
            ("junk-tail", WRAP.format(body="gze") + "x", "refuse: junk"),
            ("leading-zero", WRAP.format(body="(glam (1 0) (gvar 01))"), "refuse: junk"),
        ]
        # bad-version replacement is fragile if "image 1 " matches twice.
        # The string has one "image 1 ".
        for name, text, want in cases:
            path = write_tmp(text)
            check(name, call("run", path), want)
    except SystemExit:
        raise
    print("images ok")
    return problems


if __name__ == "__main__":
    sys.exit(main())
