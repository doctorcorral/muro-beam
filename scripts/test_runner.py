#!/usr/bin/env python3
# End-to-end tests for the muro-beam binary.
#
# The binary loads a .mbi file and runs drive. These checks cover
# format 1, format 2 with gref, a refusal, a truncated file, junk,
# fuel 0, invalid UTF-8, a file over the 1 MiB cap, and a bare
# --fuel. The kept nat is the one the pid-0 harness prints.
# Format 3 (B4a) adds the console at pid 1: the console lines come
# before the summary line.
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
    # B1d data images. Drove.val is nat-only, so a con keeps v-.
    # The stuck ones still stop stuck 0 after at least one tr-step.
    "con0": "v-",
    "con1": "v-",
    "con2": "v-",
    "case0": "v0",
    "case1": "v0",
    "case2-last": "v1",
    "case2-first": "v0",
    "case-first": "v1",
    "case-w": "v0",
    "case-miss": "v-",
    "case-arity": "v-",
    "gmatch-con": "v-",
    "case-g1": "v-",
}

LINE = re.compile(
    r"^(halted|deadlock|stuck \d+|fuel) \[(.*)\] h\d+l\d+p\d+ v(\d+|-)\n$"
)
EVENT = re.compile(
    r"tr-(alloc|spend|send|recv|spawn|step|collect|down)( |\(|$)"
)

# once (suc 0). The continuation is done, so the value stays on
# saved over seg. drive keeps v1 and stops stuck.
ONCE_APP = (
    "(muro-beam-image 1 (boundary 1) (entry (seq "
    "(gapp (glam (1 0) (gvar 0)) (gsu gze)) (done))))\n"
)

# Format 2, no defs section. Empty list, entry is zero.
V2_EMPTY = "(muro-beam-image 2 (boundary 1) (entry (seq gze (done))))\n"

WRAP = "(muro-beam-image 1 (boundary 1) (entry (seq {body} (done))))\n"

# B4a console images (format 3). The binary prints the console
# lines, then the showDrove line. MuroBeam.IoPins pins the same text
# with refl, so make agda already checks these strings.
def steps(n):
    return "tr-step 0, " * n


IO = {
    # send 1 0 of an ω seq slot: one console line, then halted.
    "out-one": "2\nhalted [" + steps(5) + "tr-send 0 1 ref(2,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h3l3p2 v2",
    # Two sends. Lines are delivery order.
    "out-two": "0\n1\nhalted [" + steps(4) + "tr-send 0 1 ref(0,pt(inf),pt(inf),omega-kept) Kcopy, tr-send 0 1 ref(2,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h3l3p2 v0",
    # Format 3 with a defs section: plus 2 3 to the console.
    "out-plus": "5\nhalted [" + steps(66) + "tr-send 0 1 ref(16,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect(0 1 2 3 4 9 10 11 12 13 14)] h17l6p2 v5",
    # The console is pid 1, so the first child is pid 2.
    "out-child": "1\nhalted [" + steps(3) + "tr-spawn 0 2, tr-send 2 1 ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect(2)] h3l2p3 v1",
    # The child sends to pid 0, which forwards to the console.
    "out-relay": "3\nhalted [" + steps(7) + "tr-spawn 0 2, tr-send 2 0 ref(3,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 ref(3,pt(inf),pt(inf),omega-kept), tr-send 0 1 ref(3,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect(4)] h5l4p3 v3",
    # A constructor prints as con <tag>.
    "out-con": "con 1\nhalted [" + steps(3) + "tr-send 0 1 ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h2l2p2 v-",
    # A closure prints as closure.
    "out-clo": "closure\nhalted [tr-step 0, tr-send 0 1 ref(0,pt(inf),pt(inf),omega-kept) Kcopy, tr-collect()] h1l1p2 v-",
    # Format 3 pure entry: no output line, console is p2.
    "out-none": "stuck 0 [tr-step 0, tr-step 0, tr-step 0] h2l2p2 v1",
    # Format 1: no pid 1, emit1 is blocked, stuck 0, no output line.
    "out-v1": "stuck 0 [tr-step 0, tr-step 0, tr-step 0] h2l2p1 v1",
    # The console is output only. A recv entry deadlocks.
    "out-recv": "deadlock [] h0l0p2 v-",
    # A spawn reply sent to the console: printed, the parent's await deadlocks.
    "out-reply": "0\ndeadlock [tr-step 0, tr-spawn 0 2, tr-send 2 1 ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) Kmove] h3l3p3 v0",
}

REFUSE = [
    ("bad-version", WRAP.format(body="gze").replace("image 1 ", "image 4 ", 1), "bad version"),
    ("bad-gref", WRAP.format(body="(gref 0)"), "bad gref"),
    ("empty-gcase", WRAP.format(body="(gcase gze)"), "empty gcase"),
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
    # A tagged form that is not a spawn parent. Parse refuses the
    # word. tagAwait-no is checkP of the hand-built term,
    # fail "tagged protocol". It is not this string.
    ("not-surface",
     "(muro-beam-image 1 (boundary 1) (entry (awaitT 0 (done))))\n",
     "not surface"),
    ("not-surface-flushT",
     "(muro-beam-image 1 (boundary 1) (entry (flushT 0 (done))))\n",
     "not surface"),
    ("not-surface-ignoreT",
     "(muro-beam-image 1 (boundary 1) (entry (ignoreT 0 (done))))\n",
     "not surface"),
    ("not-surface-ncheckT",
     "(muro-beam-image 1 (boundary 1) (entry (ncheckT 0 (done))))\n",
     "not surface"),
    ("not-surface-ndemonT",
     "(muro-beam-image 1 (boundary 1) (entry (ndemonT 0 (done))))\n",
     "not surface"),
    # A tagged spawn parent. Parse refuses the word before checkP.
    # spawnTagAwait-no is the hand-built checkP pin, not this file.
    ("tagged-spawn", None, "not surface"),
    # A tag buried under seq as the spawn parent. Parse refuses the
    # word. buriedTagAwait-no is checkP of the hand-built term,
    # fail "tagged protocol". The generic arm does not merge it.
    ("buried-awaitT", None, "not surface"),
    ("buried-ignoreT", None, "not surface"),
    ("buried-flushT", None, "not surface"),
    ("buried-ncheckT", None, "not surface"),
    ("buried-ndemonT", None, "not surface"),
    ("spawn-ignoreT",
     "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (ignoreT 0 (done)))))\n",
     "not surface"),
    ("spawn-flushT",
     "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (flushT 0 (done)))))\n",
     "not surface"),
    ("spawn-ncheckT",
     "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (ncheckT 0 (done)))))\n",
     "not surface"),
    ("spawn-ndemonT",
     "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (ndemonT 0 (done)))))\n",
     "not surface"),
    ("await-scope",
     "(muro-beam-image 1 (boundary 1) (entry (await 0 (done))))\n",
     "out of scope"),
    ("done-extra",
     "(muro-beam-image 1 (boundary 1) (entry (done x)))\n",
     "junk"),
    ("await-seq", None, "protocol is not a spawn reply"),
    ("ignore-seq", None, "protocol is not a spawn reply"),
    ("nignore-seq", None, "protocol is not a spawn reply"),
    ("skip-await", None, "protocol slot is not moved"),
    ("copy-await", None, "protocol slot is not moved"),
    ("buried-await", None, "protocol is not a spawn reply"),
    ("alias-await", None, "reply result is not fresh"),
    ("gmatch-await", None, "reply result is not fresh"),
    ("gvar-await", None, "reply result is not fresh"),
    ("gref-chain", None, "reply result is not fresh"),
    ("glam-g1", None, "glam reply under g1"),
    ("nested-seq", None, "bad gref"),
    ("comp-await", None, "protocol slot is not one computational use"),
    ("comp-ignore", None, "protocol slot is not one computational use"),
    ("comp-nignore", None, "protocol slot is not one computational use"),
    ("type-await", None, "protocol slot has a type use"),
    ("type-ignore", None, "protocol slot has a type use"),
    ("type-nignore", None, "protocol slot has a type use"),
    # g1 recv binder, ω payload from seq of gsu. checkP refuses it.
    # recvMoveAwait-no is the hand-built equation, not this file's load.
    ("recv-move", None, "protocol slot came from recv"),
    # ignore and nignore share recv-move's term shape. shift is a
    # different term and the same guard.
    # recvMoveIgnore-no, recvMoveNignore-no, recvMoveShift-no.
    ("recv-move-ignore", None, "protocol slot came from recv"),
    ("recv-move-nignore", None, "protocol slot came from recv"),
    ("recv-move-shift", None, "protocol slot came from recv"),
    # Keep that is not a protocol consumer. recvKeep-no and
    # recvKeepCopy-no are the hand-built equations, not a load of
    # these files. recv-keep-beside awaits another slot.
    # recv-keep-beside-ignore and recv-keep-beside-nignore are
    # that keep beside ignore and nignore. The pins are hand-built
    # refls, not a load of the files, and not a grade theorem.
    ("recv-keep", None, "kept slot came from recv"),
    ("recv-keep-copy", None, "kept slot came from recv"),
    ("recv-keep-beside", None, "kept slot came from recv"),
    ("recv-keep-beside-ignore", None, "kept slot came from recv"),
    ("recv-keep-beside-nignore", None, "kept slot came from recv"),
    ("defs-need-seq",
     "(muro-beam-image 2 (boundary 1) (defs gze) (entry (done)))\n",
     "defs need a seq entry"),
    ("defs-need-seq-spawn",
     "(muro-beam-image 2 (boundary 1) (defs gze) (entry (spawn t[] (done) (done))))\n",
     "defs need a seq entry"),
    # A scope-0 send is `out of scope` at parse. This send is under
    # `recv`, so the entry parses and `noDefs` refuses it.
    ("defs-need-seq-send",
     "(muro-beam-image 2 (boundary 1) (defs gze) (entry (recv (w 0) (send 0 0 (done)))))\n",
     "defs need a seq entry"),
    ("defs-need-seq-recv",
     "(muro-beam-image 2 (boundary 1) (defs gze) (entry (recv (w 0) (done))))\n",
     "defs need a seq entry"),
    ("spawn-short",
     "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done))))\n",
     "junk"),
    ("send-scope",
     "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (send 0 0 (done)) (done))))\n",
     "out of scope"),
    ("thin-scope",
     "(muro-beam-image 1 (boundary 1) (entry (spawn (keep t[]) (done) (done))))\n",
     "out of scope"),
    ("g0-send",
     "(muro-beam-image 1 (boundary 1) (entry (seq gze (recv (0 0) (send 0 0 (done))))))\n",
     "erased variable used computationally"),
    ("proc-trunc",
     "(muro-beam-image 1 (boundary 1) (entry (spawn t[] (done) (done))))",
     "truncated"),
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


def write_tmp_bytes(data):
    fh = tempfile.NamedTemporaryFile("wb", suffix=".mbi", delete=False)
    fh.write(data)
    fh.close()
    return fh.name


# Pure (seq <btm> (done)) entries stop stuck 0. The continuation is
# done, so bind1 leaves saved over seg in place. Process entries are
# checked by check_proc against the full showDrove line.
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


# Full showDrove line, including the newline the Haskell main adds.
# The event list and the heap/process fingerprint are the whole line,
# the same text MuroBeam.Show prints for conformance.
REPLY = (
    "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 "
    "ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
    "Kmove, tr-collect(0 1 2 3)] h4l0p2 v0\n"
)
PROC = {
    "spawn-done": "halted [tr-spawn 0 1, tr-collect(0)] h1l0p2 v-\n",
    "bare-done": "halted [tr-collect()] h0l0p1 v-\n",
    "send-recv": (
        "halted [tr-step 0, tr-step 0, tr-step 0, tr-step 0, tr-step 0, "
        "tr-spawn 0 1, tr-send 1 0 ref(2,pt(inf),pt(inf),omega-kept) Kcopy, "
        "tr-recv 0 ref(2,pt(inf),pt(inf),omega-kept), "
        "tr-collect(0 1 2 3)] h4l0p2 v2\n"
    ),
    "spawn-ignore": REPLY,
    "spawn-await": REPLY,
    "def-spawn": (
        "halted [tr-step 0, tr-step 0, tr-step 0, tr-spawn 0 1, "
        "tr-collect(0 1)] h2l0p2 v0\n"
    ),
    "spawn-nignore": (
        "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 "
        "ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(1 2)] h3l1p2 v0\n"
    ),
    "alias-bind": (
        "halted [tr-step 0, tr-step 0, tr-step 0, tr-spawn 0 1, tr-send 1 0 "
        "ref(1,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(0 1 2 3 4)] h5l0p2 v1\n"
    ),
    "gref-await": (
        "halted [tr-step 0, tr-step 0, tr-step 0, tr-spawn 0 1, tr-send 1 0 "
        "ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(0 1 2 3)] h4l0p2 v0\n"
    ),
    # Direct glam at scope 0. glam-g1.mbi is the same body under a g1 recv.
    # A closure is not a nat, so the kept value is v-.
    "glam-reply": (
        "halted [tr-step 0, tr-spawn 0 1, tr-send 1 0 "
        "ref(0,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(0 1 2 3)] h4l0p2 v-\n"
    ),
    # Direct gpi. The body is (gsu gze). evalTm ignores it and
    # allocates nat zero, so the line is that allocation, not the body.
    "gpi-reply": REPLY,
    # (gtyp 0) needs a variable whose type grade allows one use.
    # The child sends a closure. v0 is the gtyp allocation: a
    # received nat would be the kept value instead.
    "gtyp-reply": (
        "halted [tr-spawn 0 1, tr-step 1, tr-send 1 0 "
        "ref(1,pt(inf),pt(inf),omega-kept) Kcopy, tr-recv 0 "
        "ref(1,pt(inf),pt(inf),omega-kept), tr-step 0, tr-spawn 0 2, "
        "tr-send 2 0 ref(2,pt(fin(1)),pt(fin(1)),fin-kept(1,1,le-suc(0,0,le-zero(0)))) "
        "Kmove, tr-collect(0 1 2 3 4 5)] h6l0p3 v0\n"
    ),
}


def check_proc(name, out, want):
    if out != want:
        fail(name + ": got " + repr(out) + " want " + repr(want))
    print("ok " + name)


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
    # imgFuel is 1000, the same default this binary uses when --fuel
    # is omitted. plus stops stuck 0 and keeps v5 at that fuel.
    # The event list is long; the lock is the outcome and the nat.
    code, out, err = run([os.path.join(IMG, "plus.mbi")])
    if code != 0 or err != "":
        fail("plus-default: " + repr((code, out, err)))
    m = LINE.match(out)
    if m is None or m.group(1) != "stuck 0" or m.group(3) != "5":
        fail("plus-default line " + repr(out))
    print("ok plus-default")
    path = write_tmp(ONCE_APP)
    code, out, err = run([path, "--fuel", "1000"])
    if code != 0 or err != "":
        fail("once-app: " + repr((code, out, err)))
    check_line("once-app", out, "v1")
    for name, want in PROC.items():
        path = os.path.join(IMG, name + ".mbi")
        code, out, err = run([path, "--fuel", "1000"])
        if code != 0 or err != "":
            fail(name + ": exit " + str(code) + " stderr " + repr(err) + " out " + repr(out))
        check_proc(name, out, want)
    for name, want in IO.items():
        path = os.path.join(IMG, name + ".mbi")
        for args in ([path], [path, "--fuel", "1000"]):
            code, out, err = run(args)
            if code != 0 or err != "":
                fail(name + ": exit " + str(code) + " stderr " + repr(err) + " out " + repr(out))
            check_proc(name, out, want + "\n")
    # Fuel 0 on the console layout: no step, no output line, two
    # processes. Exit 3 as for any fuel stop.
    code, out, err = run([os.path.join(IMG, "out-one.mbi"), "--fuel", "0"])
    if code != 3 or out != "fuel [] h0l0p2 v-\n" or err != "muro-beam: out of fuel\n":
        fail("out-fuel0: " + repr((code, out, err)))
    print("ok out-fuel0")
    # Same file as the halting pin above. --alias-bind loads it, plants
    # a second reference, and bind1 refuses. Exit 0: the probe ran.
    path = os.path.join(IMG, "alias-bind.mbi")
    code, out, err = run(["--alias-bind", path])
    if code != 0 or err != "" or out != "refuse: aliased reply result\n":
        fail("alias-bind-plant: " + repr((code, out, err)))
    print("ok alias-bind-plant")
    # A load refusal under --alias-bind is exit 2, stderr like a normal
    # load. The file is a non-fresh reply body.
    path = os.path.join(IMG, "alias-await.mbi")
    code, out, err = run(["--alias-bind", path])
    if code != 2 or out != "" or err != "muro-beam: reply result is not fresh\n":
        fail("alias-bind-load: " + repr((code, out, err)))
    print("ok alias-bind-load")
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
        if text is None:
            path = os.path.join(IMG, name + ".mbi")
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
    if code != 0 or "exit 0" not in out or "aliased reply result" not in out or err != "":
        fail("help: " + repr((code, out, err)))
    print("ok help")
    code, out, err = run([os.path.join(IMG, "suc.mbi"), "--fuel", "no"])
    if code != 1 or "bad fuel" not in err:
        fail("bad fuel: " + repr((code, out, err)))
    print("ok bad-fuel")
    code, out, err = run([os.path.join(IMG, "suc.mbi"), "--fuel"])
    if code != 1 or out != "" or err != "muro-beam: --fuel needs a natural\n":
        fail("bare fuel: " + repr((code, out, err)))
    print("ok bare-fuel")
    code, out, err = run([os.path.join(IMG, "suc.mbi"), "--fuel", "1", "--fuel", "2"])
    if code != 1 or "twice" not in err:
        fail("twice: " + repr((code, out, err)))
    print("ok fuel-twice")
    path = write_tmp_bytes(b"\xff\xfe not utf-8\n")
    code, out, err = run([path])
    if code != 1 or out != "" or "cannot read" not in err or "invalid UTF-8" not in err:
        fail("utf8: " + repr((code, out, err)))
    print("ok invalid-utf8")
    # 1 MiB + 1 byte, same cap as scripts/build_runner.py.
    from build_runner import MAX_IMAGE_BYTES
    path = write_tmp_bytes(b"x" * (MAX_IMAGE_BYTES + 1))
    code, out, err = run([path])
    if code != 1 or out != "" or "cannot read" not in err or "file too large" not in err:
        fail("too-large: " + repr((code, out, err)))
    print("ok too-large")
    code, out, err = run([IMG])
    if code != 1 or out != "" or "cannot read" not in err:
        fail("directory: " + repr((code, out, err)))
    print("ok directory")
    path = write_tmp(WRAP.format(body="gze"))
    os.chmod(path, 0)
    try:
        code, out, err = run([path])
    finally:
        os.chmod(path, 0o644)
    if code != 1 or out != "" or "cannot read" not in err:
        fail("denied: " + repr((code, out, err)))
    print("ok permission")
    print("runner ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
