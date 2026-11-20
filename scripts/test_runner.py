#!/usr/bin/env python3
# End-to-end tests for the muro-beam binary.
#
# The binary loads a .mbi file and runs drive. These checks cover
# format 1, format 2 with gref, a refusal, a truncated file, junk,
# and fuel 0. The kept nat is the one the pid-0 harness prints.
# The event words are the book trace constructors.

import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "muro-beam")
IMG = os.path.join(ROOT, "examples", "images")

# name, expected kept-nat suffix. Closures keep nothing.
VALUES = {
    "affine": "v-",
    "app": "v0",
    "drop": "v-",
    "iv": "v-",
    "match": "v0",
    "once": "v-",
    "reuse": "v-",
    "suc": "v2",
    "twice": "v-",
    "plus": "v5",
    "half": "v2",
    "iseven": "v1",
}

LINE = re.compile(
    r"^(halted|deadlock|stuck \d+|fuel) \[(.*)\] h\d+l\d+p\d+ v(\d+|-)\n$"
)
EVENT = re.compile(
    r"tr-(alloc|spend|send|recv|spawn|step|collect|down)( |\(|$)"
)

# once (suc 0). drive keeps v1 and stops stuck.
ONCE_APP = (
    "(muro-beam-image 1 (boundary 1) (entry (seq "
    "(gapp (glam (1 0) (gvar 0)) (gsu gze)) (done))))\n"
)

# Format 2, no defs section. Empty list, entry is zero.
V2_EMPTY = "(muro-beam-image 2 (boundary 1) (entry (seq gze (done))))\n"

WRAP = "(muro-beam-image 1 (boundary 1) (entry (seq {body} (done))))\n"

REFUSE = [
    ("bad-version", WRAP.format(body="gze").replace("image 1 ", "image 3 ", 1), "bad version"),
    ("bad-gref", WRAP.format(body="(gref 0)"), "bad gref"),
    (
        "bad-gref-index",
        "(muro-beam-image 2 (boundary 1) (defs (glam ((iv 0 1) 0) (gref 3))) "
        "(entry (seq gze (done))))\n",
        "bad gref",
    ),
    (
        "forward-gref",
        "(muro-beam-image 2 (boundary 1) (defs "
        "(glam ((iv 0 1) 0) (gref 1)) gze) "
        "(entry (seq gze (done))))\n",
        "bad gref",
    ),
    (
        "out-def",
        "(muro-beam-image 2 (boundary 1) (defs (glam (1 0) "
        "(glam (w 0) (gref 0)))) (entry (seq gze (done))))\n",
        "outside the boundary",
    ),
    (
        "empty-defs",
        "(muro-beam-image 2 (boundary 1) (defs) (entry (seq gze (done))))\n",
        "junk",
    ),
    (
        "bad-boundary",
        WRAP.format(body="gze").replace("(boundary 1)", "(boundary 2)", 1),
        "bad boundary version",
    ),
    ("out-of-scope", WRAP.format(body="(gvar 0)"), "out of scope"),
    ("pi", None, "type grade 0 does not allow 1 uses"),
    ("truncated", WRAP.format(body="gze").rstrip("\n"), "truncated"),
    ("unclosed", "(muro-beam-image 1 (boundary 1) (entry (seq gze (done)))", "truncated"),
    ("newline-open", "(muro-beam-image 1 (boundary 1) (entry (seq gze (done)))\n", "junk"),
    ("junk", "not-an-image\n", "junk"),
    ("junk-tail", WRAP.format(body="gze") + "x", "junk"),
    ("leading-zero", WRAP.format(body="(glam (1 0) (gvar 01))"), "junk"),
    (
        "cex",
        "(muro-beam-image 1 (boundary 1) (entry (seq (glam (1 0) "
        "(gapp (glam (w 0) (gapp (gvar 0) (gvar 0))) "
        "(glam ((iv 0 1) 0) (gvar 1)))) (done))))\n",
        "outside the boundary",
    ),
]


def fail(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def run(args):
    proc = subprocess.run(
        [BIN, *args], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    return proc.returncode, proc.stdout.decode("utf-8"), proc.stderr.decode("utf-8")


def write_tmp(text):
    fh = tempfile.NamedTemporaryFile("w", suffix=".mbi", delete=False)
    fh.write(text)
    fh.close()
    return fh.name


def events_ok(body):
    if body == "":
        return True
    for piece in body.split(", "):
        if EVENT.match(piece) is None:
            return False
    return True


def check_line(name, out, value):
    m = LINE.match(out)
    if m is None:
        fail(name + ": bad line " + repr(out))
    if m.group(1) != "stuck 0":
        fail(name + ": outcome " + m.group(1))
    if not events_ok(m.group(2)):
        fail(name + ": events " + m.group(2))
    if m.group(3) != value[1:]:
        # value is "v5" or "v-". The group is "5" or "-".
        got = "v" + m.group(3)
        fail(name + ": value " + got + " want " + value)
    if "tr-step 0" not in m.group(2):
        fail(name + ": no tr-step")
    print("ok " + name + " " + m.group(1) + " " + value)


def main():
    if not os.path.isfile(BIN):
        fail("missing " + BIN + " (run make muro-beam)")
    for name, value in VALUES.items():
        path = os.path.join(IMG, name + ".mbi")
        code, out, err = run([path, "--fuel", "1000"])
        if code != 0 or err != "":
            fail(name + ": exit " + str(code) + " stderr " + repr(err) + " out " + repr(out))
        check_line(name, out, value)
    code, out, err = run([os.path.join(IMG, "suc.mbi")])
    if code != 0 or not out.endswith(" v2\n"):
        fail("default fuel: " + repr((code, out, err)))
    print("ok default-fuel")
    path = write_tmp(ONCE_APP)
    code, out, err = run([path, "--fuel", "1000"])
    if code != 0 or err != "":
        fail("once-app: " + repr((code, out, err)))
    check_line("once-app", out, "v1")
    path = write_tmp(V2_EMPTY)
    code, out, err = run([path, "--fuel", "1000"])
    if code != 0 or err != "":
        fail("v2-empty: " + repr((code, out, err)))
    check_line("v2-empty", out, "v0")
    # Fuel 0 does not step. lowerP is an empty heap and one process.
    path = os.path.join(IMG, "suc.mbi")
    for args in ([path, "--fuel", "0"], ["--fuel", "0", path]):
        code, out, err = run(args)
        if code != 3:
            fail("fuel0 exit " + str(code) + " " + repr(out) + " " + repr(err))
        if out != "fuel [] h0l0p1 v-\n":
            fail("fuel0 line " + repr(out))
        if err != "muro-beam: out of fuel\n":
            fail("fuel0 stderr " + repr(err))
    print("ok fuel0")
    code, out, err = run([os.path.join(IMG, "plus.mbi"), "--fuel", "1"])
    if code != 3 or not out.startswith("fuel ") or err != "muro-beam: out of fuel\n":
        fail("fuel1: " + repr((code, out, err)))
    print("ok fuel1")
    for name, text, reason in REFUSE:
        if name == "pi":
            path = os.path.join(IMG, "pi.mbi")
        else:
            path = write_tmp(text)
        code, out, err = run([path])
        if code != 2 or out != "" or err != "muro-beam: " + reason + "\n":
            fail(name + ": " + repr((code, out, err)))
        print("ok " + name)
    code, out, err = run(["/no/such/image.mbi"])
    if code != 1 or out != "" or "cannot read" not in err:
        fail("missing: " + repr((code, out, err)))
    print("ok missing")
    code, out, err = run([])
    if code != 1 or out != "" or "usage:" not in err:
        fail("usage: " + repr((code, out, err)))
    print("ok usage")
    code, out, err = run(["--help"])
    if code != 0 or "exit 0" not in out or err != "":
        fail("help: " + repr((code, out, err)))
    print("ok help")
    code, out, err = run([os.path.join(IMG, "suc.mbi"), "--fuel", "no"])
    if code != 1 or "bad fuel" not in err:
        fail("bad fuel: " + repr((code, out, err)))
    print("ok bad-fuel")
    code, out, err = run([os.path.join(IMG, "suc.mbi"), "--fuel", "1", "--fuel", "2"])
    if code != 1 or "twice" not in err:
        fail("twice: " + repr((code, out, err)))
    print("ok fuel-twice")
    print("runner ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
