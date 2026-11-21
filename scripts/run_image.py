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

# Hand-written v2 images, not emitter goldens. The strings are what
# the CEK harness prints. Elixir's eval_run does not return these
# nats; see examples/images/README.md.
HAND = {
    "plus": "nat 5",
    "half": "nat 2",
    "iseven": "nat 1",
}

# once (suc 0). Elixir, muro 3f1cae2 (0.21.11), compiled with
# MIX_BUILD_PATH=/private/tmp/beam-b2-build. Muro.Load.file then
# Muro.Session.eval_run("once", [1], book) and eval_run("applied", [], book)
# both returned 1. The book has two run defs, so emit_mbi will not
# write it; the image below is the same term by hand. The continuation
# is done, so bind1 leaves the value on saved over seg. drive keeps
# that nat and stops stuck.
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

# Format 2 with no defs section. The printer keeps the number and
# reprints the four-sexp line.
V2_EMPTY = "(muro-beam-image 2 (boundary 1) (entry (seq gze (done))))\n"

# A definition whose body is a lam under a live g1.
OUT_DEF = (
    "(muro-beam-image 2 (boundary 1) (defs (glam (1 0) "
    "(glam (w 0) (gref 0)))) (entry (seq gze (done))))\n"
)

# First of two definitions names the second. Ordered recursion refuses it.
FORWARD = (
    "(muro-beam-image 2 (boundary 1) (defs "
    "(glam ((iv 0 1) 0) (gref 1)) gze) "
    "(entry (seq gze (done))))\n"
)

WRAP = "(muro-beam-image 1 (boundary 1) (entry (seq {body} (done))))\n"

# Process entries. Not emitter goldens. `drove` is load then drive
# at imgFuel (1000). The string is showDrove, the same line the binary
# prints without the newline the Haskell main adds. Bare protocol
# forms are refusals and are checked below, on drive and on run.
REPLY = (
    "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 "
    "ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
    "Kmove, tr-collect(0 1 2 3)] h4l0p2 v0"
)
PROC = {
    "spawn-done": "halted [tr-spawn 0 1, tr-collect(0)] h1l0p2 v-",
    "bare-done": "halted [tr-collect()] h0l0p1 v-",
    "send-recv": (
        "halted [tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, "
        "tr-spawn 0 1, tr-send 1 0 ref(2,pt(inf),pt(inf),omega-kept) Kcopy, "
        "tr-recv 0 ref(2,pt(inf),pt(inf),omega-kept), "
        "tr-collect(0 1 2 3)] h4l0p2 v2"
    ),
    "spawn-ignore": REPLY,
    "spawn-await": REPLY,
    "def-spawn": (
        "halted [tr-step 0, tr-step 0, tr-step 0, tr-spawn 0 1, "
        "tr-collect(0 1)] h2l0p2 v0"
    ),
    "spawn-nignore": (
        "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 "
        "ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(1 2)] h3l1p2 v0"
    ),
    # Fresh gsu. drive promotes. The alias probe plants a second ref.
    "alias-bind": (
        "halted [tr-step 0, tr-step 0, tr-step 0, tr-spawn 0 1, tr-send 1 0 "
        "ref(1,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(0 1 2 3 4)] h5l0p2 v1"
    ),
    # Direct fresh gref of gze. Three eval steps, then the same move.
    "gref-await": (
        "halted [tr-step 0, tr-step 0, tr-step 0, tr-spawn 0 1, tr-send 1 0 "
        "ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(0 1 2 3)] h4l0p2 v0"
    ),
    # Direct glam at scope 0. No g1 is in scope, so guardGlam allows it.
    # The payload is a closure, which drive does not keep as a nat.
    "glam-reply": (
        "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 "
        "ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(0 1 2 3)] h4l0p2 v-"
    ),
    # Direct gpi. The body is (gsu gze). evalTm ignores it and
    # allocates nat zero, so the line is that allocation, not the
    # successor the body would be.
    "gpi-reply": REPLY,
    # gtyp names a variable. The child sends a closure, not a nat.
    # drive keeps the first delivered nat, and readNat of a closure
    # is nothing, so v0 is the cell evalTm allocated for (gtyp 0).
    # A child that sent (gsu gze) would keep v1, the received value.
    "gtyp-reply": (
        "halted [tr-spawn 0 1, tr-step 1, tr-send 1 0 "
        "ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 "
        "ref(1,pt(inf),pt(inf),omega-kept), tr-step 0, tr-spawn 0 2, "
        "tr-send 2 0 ref(2,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(0 1 2 3 4 5)] h6l0p3 v0"
    ),
}
REFUSE = [
    ("await-seq", "protocol is not a spawn reply"),
    ("ignore-seq", "protocol is not a spawn reply"),
    ("nignore-seq", "protocol is not a spawn reply"),
    ("skip-await", "protocol slot is not moved"),
    ("copy-await", "protocol slot is not moved"),
    ("buried-await", "protocol is not a spawn reply"),
    ("alias-await", "reply result is not fresh"),
    ("gmatch-await", "reply result is not fresh"),
    ("gvar-await", "reply result is not fresh"),
    ("gref-chain", "reply result is not fresh"),
    ("glam-g1", "glam reply under g1"),
    ("nested-seq", "bad gref"),
    ("comp-await", "protocol slot is not one computational use"),
    ("comp-ignore", "protocol slot is not one computational use"),
    ("comp-nignore", "protocol slot is not one computational use"),
    ("type-await", "protocol slot has a type use"),
    ("type-ignore", "protocol slot has a type use"),
    ("type-nignore", "protocol slot has a type use"),
    # g1 recv annotation, ω payload. checkP refuses the protocol slot.
    # recvMoveAwait-no is that equation. The file is not a run.
    ("recv-move", "protocol slot came from recv"),
]
# Tagged heads are not surface syntax, so echo is not the source.
# drive and run both print the parse reason. spawnTagAwait-no is
# the checkP equation for a tagged spawn parent
# (fail "tagged spawn parent"). tagAwait-no is a different equation:
# a tag that is not a spawn parent is fail "tagged protocol".
# buriedTagAwait-no is the equation for a tag under seq as that
# parent, the same "tagged protocol" string, not the parent equation.
# sendTagAwait-no, recvTagAwait-no, and awaitUnderRecv-no pin a tag
# under send, recv, and await. None of them is a load of these files.
PARSE_REFUSE = [
    ("tagged-spawn", "not surface"),
    ("buried-awaitT", "not surface"),
    ("buried-ignoreT", "not surface"),
    ("buried-flushT", "not surface"),
    ("buried-ncheckT", "not surface"),
    ("buried-ndemonT", "not surface"),
]


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
    drive_sym = symbol("d_driveImage")
    drove_sym = symbol("d_droveImage")
    alias_sym = symbol("d_aliasImage")
    with open(MAIN, "w", encoding="utf-8") as fh:
        fh.write(
            "\n".join(
                [
                    "module Main where",
                    "import System.Environment (getArgs)",
                    "import qualified Data.Text as T",
                    "import qualified Data.Text.IO as TIO",
                    "import MAlonzo.Code.MuroBeam.RunImage ("
                    + run_sym + ", " + echo_sym + ", " + drive_sym + ", " + drove_sym
                    + ", " + alias_sym + ")",
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
                    '    ["drive", path] -> do',
                    "      src <- TIO.readFile path",
                    "      TIO.putStr (" + drive_sym + " src)",
                    '    ["drove", path] -> do',
                    "      src <- TIO.readFile path",
                    "      TIO.putStr (" + drove_sym + " src)",
                    '    ["alias", path] -> do',
                    "      src <- TIO.readFile path",
                    "      TIO.putStr (" + alias_sym + " src)",
                    '    _ -> fail "usage: image-malonzo run PATH FUEL | echo PATH | drive PATH | drove PATH | alias PATH"',
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
    if mode == "echo":
        cmd = [BIN, "echo", path]
    elif mode == "drive":
        cmd = [BIN, "drive", path]
    elif mode == "drove":
        cmd = [BIN, "drove", path]
    elif mode == "alias":
        cmd = [BIN, "alias", path]
    else:
        cmd = [BIN, "run", path, fuel]
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


def nat(n):
    s = "gze"
    for _ in range(n):
        s = "(gsu " + s + ")"
    return s


def with_arg(src, old, new):
    text = src.replace(old, new, 1)
    if text == src:
        fail("argument not found: " + old)
    return text


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
        for name, want in HAND.items():
            path = os.path.join(IMG, name + ".mbi")
            with open(path, encoding="utf-8") as fh:
                raw = fh.read()
            echoed = call("echo", path)
            if echoed != raw:
                fail(name + " echo: got " + repr(echoed) + " want " + repr(raw))
            print("ok echo " + name)
            check(name, call("run", path), want)
        check("plus-fuel", call("run", os.path.join(IMG, "plus.mbi"), "20"), "fuel")
        # Same definitions, other arguments. Numbers are the CEK print.
        half = open(os.path.join(IMG, "half.mbi"), encoding="utf-8").read()
        even = open(os.path.join(IMG, "iseven.mbi"), encoding="utf-8").read()
        plus = open(os.path.join(IMG, "plus.mbi"), encoding="utf-8").read()
        h4 = "(gsu (gsu (gsu (gsu gze))))"
        p23 = "(gapp (gapp (gref 0) (gsu (gsu gze))) (gsu (gsu (gsu gze))))"
        calls = [
            ("half-0", with_arg(half, "(gapp (gref 0) " + h4 + ")", "(gapp (gref 0) " + nat(0) + ")"), "nat 0"),
            ("half-1", with_arg(half, "(gapp (gref 0) " + h4 + ")", "(gapp (gref 0) " + nat(1) + ")"), "nat 0"),
            ("half-5", with_arg(half, "(gapp (gref 0) " + h4 + ")", "(gapp (gref 0) " + nat(5) + ")"), "nat 2"),
            ("iseven-0", with_arg(even, "(gapp (gref 0) " + h4 + ")", "(gapp (gref 0) " + nat(0) + ")"), "nat 1"),
            ("iseven-1", with_arg(even, "(gapp (gref 0) " + h4 + ")", "(gapp (gref 0) " + nat(1) + ")"), "nat 0"),
            ("iseven-5", with_arg(even, "(gapp (gref 0) " + h4 + ")", "(gapp (gref 0) " + nat(5) + ")"), "nat 0"),
            ("plus-0-3", with_arg(plus, p23, "(gapp (gapp (gref 0) gze) (gsu (gsu (gsu gze))))"), "nat 3"),
            ("plus-2-0", with_arg(plus, p23, "(gapp (gapp (gref 0) (gsu (gsu gze))) gze)"), "nat 2"),
        ]
        for name, text, want in calls:
            path = write_tmp(text)
            echoed = call("echo", path)
            if echoed != text:
                fail(name + " echo: got " + repr(echoed) + " want " + repr(text))
            check(name, call("run", path), want)
        for name, want in PROC.items():
            path = os.path.join(IMG, name + ".mbi")
            with open(path, encoding="utf-8") as fh:
                raw = fh.read()
            echoed = call("echo", path)
            if echoed != raw:
                fail(name + " echo: got " + repr(echoed) + " want " + repr(raw))
            print("ok echo " + name)
            check(name, call("drove", path), want)
        # checkP refusals. driveImage and runImage both print the reason.
        for name, reason in REFUSE:
            path = os.path.join(IMG, name + ".mbi")
            with open(path, encoding="utf-8") as fh:
                raw = fh.read()
            echoed = call("echo", path)
            if echoed != raw:
                fail(name + " echo: got " + repr(echoed) + " want " + repr(raw))
            print("ok echo " + name)
            text = "refuse: " + reason
            check(name + "-drive", call("drive", path), text)
            check(name + "-run", call("run", path), text)
        for name, reason in PARSE_REFUSE:
            path = os.path.join(IMG, name + ".mbi")
            text = "refuse: " + reason
            check(name + "-drive", call("drive", path), text)
            check(name + "-run", call("run", path), text)
        # Fresh body, so load and drive succeed. The probe plants a
        # second reference on the returned cell. bind1 refuses it.
        check(
            "alias-bind-plant",
            call("alias", os.path.join(IMG, "alias-bind.mbi")),
            "refuse: aliased reply result",
        )
        # runSys is seq1 then runFor. It does not call bind1.
        # send-recv prints the seq nat; the spawn stays parked.
        # spawn-done's seq1 returns nothing. spawn-await prints the
        # seq payload. A bind after that eval would resume the spawn
        # and the harness would print stuck.
        check("run-send-recv", call("run", os.path.join(IMG, "send-recv.mbi")), "nat 2")
        check("run-spawn-done", call("run", os.path.join(IMG, "spawn-done.mbi")), "stuck")
        check("run-spawn-await", call("run", os.path.join(IMG, "spawn-await.mbi")), "nat 0")
        # imgFuel is 1000, the same default the binary uses. plus
        # stops stuck and keeps 5. Fuel 32 is still out of fuel here.
        check("plus-drive", call("drive", os.path.join(IMG, "plus.mbi")), "stuck 0 v5")
        path = write_tmp(ONCE_APP)
        check("once-app", call("run", path), "nat 1")
        # Elixir eval_run of this def returns 1. drive keeps that nat.
        # The outcome word is whatever the fuelled scheduler stops on.
        driven = call("drive", path).strip()
        if not driven.endswith(" v1"):
            fail("once-drive: got " + repr(driven) + " want a line ending in v1")
        print("ok once-drive " + driven)
        path = write_tmp(CEX)
        check("cex", call("run", path), "refuse: outside the boundary")
        path = write_tmp(V2_EMPTY)
        echoed = call("echo", path)
        if echoed != V2_EMPTY:
            fail("v2-empty echo: got " + repr(echoed) + " want " + repr(V2_EMPTY))
        print("ok echo v2-empty")
        check("v2-empty", call("run", path), "nat 0")
        cases = [
            ("bad-version", WRAP.format(body="gze").replace("image 1 ", "image 3 ", 1), "refuse: bad version"),
            ("bad-gref", WRAP.format(body="(gref 0)"), "refuse: bad gref"),
            ("bad-gref-index",
             "(muro-beam-image 2 (boundary 1) (defs (glam ((iv 0 1) 0) (gref 3))) "
             "(entry (seq gze (done))))\n",
             "refuse: bad gref"),
            ("forward-gref", FORWARD, "refuse: bad gref"),
            ("out-def", OUT_DEF, "refuse: outside the boundary"),
            ("empty-defs",
             "(muro-beam-image 2 (boundary 1) (defs) (entry (seq gze (done))))\n",
             "refuse: junk"),
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
            ("not-surface",
             "(muro-beam-image 1 (boundary 1) (entry (awaitT 0 (done))))\n",
             "refuse: not surface"),
            ("not-surface-ignoreT",
             "(muro-beam-image 1 (boundary 1) (entry (ignoreT 0 (done))))\n",
             "refuse: not surface"),
            ("not-surface-flushT",
             "(muro-beam-image 1 (boundary 1) (entry (flushT 0 (done))))\n",
             "refuse: not surface"),
            ("not-surface-ncheckT",
             "(muro-beam-image 1 (boundary 1) (entry (ncheckT 0 (done))))\n",
             "refuse: not surface"),
            ("not-surface-ndemonT",
             "(muro-beam-image 1 (boundary 1) (entry (ndemonT 0 (done))))\n",
             "refuse: not surface"),
            ("spawn-ignoreT",
             "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (ignoreT 0 (done)))))\n",
             "refuse: not surface"),
            ("spawn-flushT",
             "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (flushT 0 (done)))))\n",
             "refuse: not surface"),
            ("spawn-ncheckT",
             "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (ncheckT 0 (done)))))\n",
             "refuse: not surface"),
            ("spawn-ndemonT",
             "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (ndemonT 0 (done)))))\n",
             "refuse: not surface"),
            ("defs-need-seq",
             "(muro-beam-image 2 (boundary 1) (defs gze) (entry (done)))\n",
             "refuse: defs need a seq entry"),
            ("defs-need-seq-spawn",
             "(muro-beam-image 2 (boundary 1) (defs gze) (entry (spawn t[] (done) (done))))\n",
             "refuse: defs need a seq entry"),
            # A scope-0 send has no de Bruijn index, so parse reports
            # `out of scope` before `noDefs`. The send here is under
            # `recv`, which is in scope, and the entry is not `seq`.
            ("defs-need-seq-send",
             "(muro-beam-image 2 (boundary 1) (defs gze) (entry (recv (w 0) (send 0 0 (done)))))\n",
             "refuse: defs need a seq entry"),
            ("defs-need-seq-recv",
             "(muro-beam-image 2 (boundary 1) (defs gze) (entry (recv (w 0) (done))))\n",
             "refuse: defs need a seq entry"),
            ("spawn-short",
             "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done))))\n",
             "refuse: junk"),
            ("send-scope",
             "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (send 0 0 (done)) (done))))\n",
             "refuse: out of scope"),
            ("thin-scope",
             "(muro-beam-image 1 (boundary 1) (entry (spawn (keep t[]) (done) (done))))\n",
             "refuse: out of scope"),
            ("await-scope",
             "(muro-beam-image 1 (boundary 1) (entry (await 0 (done))))\n",
             "refuse: out of scope"),
            ("g0-send",
             "(muro-beam-image 1 (boundary 1) (entry (seq gze (recv (0 0) (send 0 0 (done))))))\n",
             "refuse: erased variable used computationally"),
            ("done-extra",
             "(muro-beam-image 1 (boundary 1) (entry (done x)))\n",
             "refuse: junk"),
            ("proc-trunc",
             "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (done))))",
             "refuse: truncated"),
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
