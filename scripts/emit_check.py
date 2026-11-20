#!/usr/bin/env python3
# Emit real .mbi files with Hex muro 0.22.13 and run them.
#
# The book pin stays 0.20.33. That archive does not write a defs
# section. Format 2 is muro 0.21.22 and later. This check installs
# 0.22.13 into a private MIX_HOME, so it does not change the default
# `mix muro` and it does not change vendor/muro. The emitter is
# outside the TCB. The comparison is the bytes, then muro-beam.

import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "muro-beam")
IMG = os.path.join(ROOT, "examples", "images")
VERSION = "0.22.13"
HOME = os.environ.get(
    "MURO_EMIT_HOME",
    os.path.join(tempfile.gettempdir(), "beam-b3-muro-0.22.13"),
)

# One exported run, no definition call. Format 1.
SUC = "def two : run Nat := suc (suc 0)\n"
# Prelude plus. Format 2. The entry is plus 2 3.
PLUS = "def main : run Nat := plus 2 3\n"


def fail(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def mix_env():
    env = os.environ.copy()
    env["MIX_HOME"] = HOME
    env.pop("MIX_ARCHIVES", None)
    return env


def ensure_muro():
    ebin = os.path.join(HOME, "archives", "muro-" + VERSION, "muro-" + VERSION, "ebin")
    if os.path.isdir(ebin):
        return
    if shutil.which("mix") is None:
        fail("mix is not on PATH")
    os.makedirs(HOME, exist_ok=True)
    env = mix_env()
    subprocess.run(["mix", "local.hex", "--force"], check=True, env=env)
    subprocess.run(
        ["mix", "archive.install", "hex", "muro", VERSION, "--force"],
        check=True,
        env=env,
    )
    if not os.path.isdir(ebin):
        fail("muro " + VERSION + " did not install into " + HOME)


def emit(name, src):
    work = tempfile.mkdtemp(prefix="mbi-")
    path = os.path.join(work, name + ".muro")
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(src)
    env = mix_env()
    proc = subprocess.run(
        ["mix", "muro.emit", path, "--backend", "mbi"],
        cwd=work,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if proc.returncode != 0:
        fail(name + " emit failed: " + proc.stderr + proc.stdout)
    out = os.path.join(work, name + ".mbi")
    if not os.path.isfile(out):
        fail(name + ": emitter wrote no file\n" + proc.stdout + proc.stderr)
    with open(out, encoding="utf-8") as fh:
        return fh.read()


def golden(name):
    with open(os.path.join(IMG, name + ".mbi"), encoding="utf-8") as fh:
        return fh.read()


def drive(text):
    fh = tempfile.NamedTemporaryFile("w", suffix=".mbi", delete=False)
    fh.write(text)
    fh.close()
    proc = subprocess.run(
        [BIN, fh.name, "--fuel", "1000"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        fail("muro-beam " + repr(proc.returncode) + " " + proc.stderr.decode())
    return proc.stdout.decode("utf-8")


def check(name, src, value):
    got = emit(name, src)
    want = golden(name)
    if got != want:
        fail(name + " bytes: got " + repr(got) + " want " + repr(want))
    print("ok emit " + name)
    left = drive(got)
    right = drive(want)
    if left != right:
        fail(name + " run: emitted " + repr(left) + " golden " + repr(right))
    if not left.endswith(" " + value + "\n"):
        fail(name + " value: " + repr(left))
    print("ok run " + name + " " + value)


def main():
    if not os.path.isfile(BIN):
        fail("missing " + BIN + " (run make muro-beam)")
    ensure_muro()
    check("suc", SUC, "v2")
    check("plus", PLUS, "v5")
    print("emit-check ok (muro " + VERSION + ", book pin unchanged)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
