# Fail the build on a hole, a postulate, a termination pragma,
# or an Agda module whose OPTIONS line is not --safe.
# Comments are ignored. A name that ends in ? is not a hole.

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1] / "agda"
BANNED = re.compile(r"\bpostulate\b|TERMINATING|NON_TERMINATING|\{\!")
HOLE = re.compile(r"(?<![A-Za-z0-9_'])\?(?![A-Za-z0-9_'])")


def strip_comments(text: str) -> str:
    out = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("{-", i):
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("{-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-}", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main() -> int:
    bad = []
    files = sorted(ROOT.rglob("*.agda"))
    if not files:
        bad.append(f"{ROOT}: no Agda files")
    for path in files:
        raw = path.read_text()
        opt_lines = [ln for ln in raw.splitlines() if "OPTIONS" in ln]
        if not opt_lines or any("--safe" not in ln for ln in opt_lines):
            bad.append(f"{path}: OPTIONS line without --safe")
        body = strip_comments(raw)
        for match in BANNED.finditer(body):
            bad.append(f"{path}: {match.group(0)}")
        if HOLE.search(body):
            bad.append(f"{path}: hole ?")
    if bad:
        print("\n".join(bad))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
