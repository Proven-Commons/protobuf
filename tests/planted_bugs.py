#!/usr/bin/env python3
"""Plant each bug below in a copy of the code, and check the tests catch it.

A planted bug is a small change to the code, of a kind a person could
make by mistake: to the code under proof, or to the request handling in
Main.lean. For each one, this script copies the project into a temporary
directory, makes the change there, builds the command-line tool, and
runs the differential tests on a given number of inputs. The tests catch
the bug when they report failures. A change that alters an answer of
the code under proof also breaks the proofs, since that code no longer
meets its statements; Main.lean is outside the proofs. This script checks the
tests on their own, so it builds only the tool, not the proofs.

The project itself is never changed. The script writes the results to
tests/PLANTED-BUGS.md, and exits with 1 if a bug is not caught and its
entry gives no reason. Some bugs no test here can catch: an equivalent
change gives the same answer on every input, and some changes show only
on an input too large to send. Such an entry says why the tests miss it.

Usage: python3 tests/planted_bugs.py [--count N]
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = "protowire"  # the lake target of the command-line tool
COUNT = 20_000

# (name, file, text to replace, replacement, why the tests cannot catch it or None)
BUGS = [
    ("Field number 0 read", "Protobuf/Wire.lean",
     "if 2 ^ 32 ≤ t ∨ t / 8 = 0 then none",
     "if 2 ^ 32 ≤ t then none", None),
    ("Tags of 2^32 or more read", "Protobuf/Wire.lean",
     "if 2 ^ 32 ≤ t ∨ t / 8 = 0 then none",
     "if t / 8 = 0 then none", None),
    ("A tag of exactly 2^32 read", "Protobuf/Wire.lean",
     "if 2 ^ 32 ≤ t ∨ t / 8 = 0 then none",
     "if 2 ^ 32 < t ∨ t / 8 = 0 then none", None),
    ("Six-byte tags read", "Protobuf/Wire.lean",
     "  match Varint.decodeAux 5 bs with",
     "  match Varint.decodeAux 6 bs with", None),
    ("Eleven-byte varints read", "Protobuf/Varint.lean",
     "  match decodeAux 10 bs with",
     "  match decodeAux 11 bs with", None),
    ("Bits past the 64th kept", "Protobuf/Varint.lean",
     "| some (v, rest) => some (v % 2 ^ 64, rest)",
     "| some (v, rest) => some (v, rest)", None),
    ("No LEN length limit", "Protobuf/Wire.lean",
     "if 2 ^ 31 - 16 ≤ len ∨ (rest.take len).length < len then none",
     "if (rest.take len).length < len then none",
     "it shows only when a length of 2^31 - 16 or more is followed by that many bytes, "
     "an input of about 2 GiB; a shorter input with such a length is refused for running "
     "out of input either way. `Protobuf.Spec.decode_iff` covers the limit."),
    ("A group start tag read as an empty LEN field", "Protobuf/Wire.lean",
     "      | _ => none",
     "      | 3 => some (⟨n, .len []⟩, rest)\n      | _ => none", None),
    ("isValid takes field number 2^29", "Protobuf/Wire.lean",
     "1 ≤ f.number && f.number < 2 ^ 29 &&",
     "1 ≤ f.number && f.number ≤ 2 ^ 29 &&", None),
    ("CR kept at the end of a CR LF request", "Main.lean",
     "    String.ofList (if cs.getLast? = some '\\r' then cs.dropLast else cs)",
     "    String.ofList cs", None),
]


def failures(out):
    m = re.search(r"(\d+) failures?", out)
    return int(m.group(1)) if m else None


def run(count):
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "project"
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns(".git"))
        for name, rel, old, new, missed in BUGS:
            path = work / rel
            original = (ROOT / rel).read_text()
            if original.count(old) != 1:
                sys.exit(f"{name}: the text to replace is not in {rel} exactly once")
            path.write_text(original.replace(old, new))
            build = subprocess.run(["lake", "build", EXE], cwd=work, capture_output=True, text=True)
            if build.returncode != 0:
                path.write_text(original)
                sys.exit(f"{name}: the tool does not build with this change\n{build.stdout[-2000:]}")
            test = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count)],
                                  cwd=work, capture_output=True, text=True)
            path.write_text(original)
            n = failures(test.stdout + test.stderr)
            if n is None:
                sys.exit(f"{name}: the tests gave no failure count\n{(test.stdout + test.stderr)[-2000:]}")
            rows.append((name, rel, old, new, missed, n))
            print(f"{name}: {n} failures", flush=True)
    return rows


def write(rows, count):
    lines = [
        "# Planted bugs",
        "",
        "Written by `python3 tests/planted_bugs.py`. Each row is one small change to the",
        f"code, made in a copy. The tests ran on {count:,} inputs from their recorded seed",
        "against the changed tool. A bug is caught when they report failures.",
        "",
        "| Bug | File | Failures |",
        "|-----|------|----------|",
    ]
    for name, rel, _, _, missed, n in rows:
        cell = str(n) if n else ("0, not caught by the tests: " + missed if missed
                                 else "0, NOT CAUGHT")
        lines.append(f"| {name} | `{rel}` | {cell} |")
    lines += ["", "## The changes", ""]
    for name, rel, old, new, _, _ in rows:
        lines += [f"**{name}** in `{rel}`:", "", "```", "- " + old.replace("\n", "\n- "),
                  "+ " + new.replace("\n", "\n+ "), "```", ""]
    (ROOT / "tests" / "PLANTED-BUGS.md").write_text("\n".join(lines))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--count", type=int, default=COUNT)
    args = ap.parse_args()
    rows = run(args.count)
    write(rows, args.count)
    missed = [r[0] for r in rows if not r[5] and not r[4]]
    caught = sum(1 for r in rows if r[5])
    print(f"{caught} of {len(rows)} planted bugs caught; results in tests/PLANTED-BUGS.md")
    if missed:
        sys.exit("not caught: " + ", ".join(missed))


if __name__ == "__main__":
    main()
