#!/usr/bin/env python3
"""Differential tests: the Lean wire format codec against the reference
Protobuf parsers.

There are two oracles, both from Google's Protobuf releases:

- upb, the parser behind Python's `protobuf` package. A message is read
  as `google.protobuf.Empty`, so every field lands in its unknown field
  set, which gives the field numbers, wire types and raw values.
- The C++ parser behind `protoc --decode_raw`, run in-process through
  `grpcio-tools`. It gives whether the bytes parse, and the top-level
  field numbers and numeric values.

The encoder is compared with `google.protobuf.internal.encoder`.

Where the two parsers disagree, the Lean decoder must take the stricter
reading and refuse the input. They differ in two known ways: upb reads
field number 0, which the C++ parser refuses, and the C++ parser reads a
five-byte tag of 2^32 or more by dropping the high bits, which upb
refuses. Groups (wire types 3 and 4) are outside this library, so a
message that both parsers read but that holds a group must be refused.
The record counts each case.

Inputs come from a recorded seed:

- random field lists, weighted toward boundary field numbers and
  values, encoded and decoded;
- mutations of those encodings: a byte changed, dropped, added or
  flipped, the message cut short or extended, a varint rewritten longer
  than it needs to be (up to and past ten bytes), a tag with field
  number 0, a group, wire type 6 or 7, or a tag of 2^32 or more;
- random short byte strings;
- field lists the encoder must refuse;
- malformed requests, which the tool must answer with `error`.

Every seventh request ends in CR LF. For every input the Lean answer
must equal the oracle's, and the two parsers must disagree only in the
known ways.

    python3 tests/run_tests.py [--seed N] [--count N]

It needs `protobuf` and `grpcio-tools` at the versions below, with
protobuf on its upb backend. When they are missing it creates a virtual environment in `.lake/oracle-venv`,
installs them there, and runs itself again with it; where Python cannot
make one, it installs them into `.lake/oracle-packages` instead. It builds the
executable, writes tests/TEST-RESULTS.md, and exits non-zero if any
input disagrees.
"""

import argparse
import itertools
import os
import platform
import random
import re
import struct
import subprocess
import sys
import tempfile
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "protowire"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
VENV = ROOT / ".lake" / "oracle-venv"
PKGS = ROOT / ".lake" / "oracle-packages"
PINS = ["protobuf==7.36.2", "grpcio-tools==1.84.1"]
TIMEOUT = 1800
BUILD_TIMEOUT = 3600


def ensure_oracles():
    """Import the oracles. When this Python lacks them, install the pinned
    versions into a virtual environment and run again with it; where a
    virtual environment cannot be made, install them into a folder
    instead and import them from there."""
    if oracles_ready():
        return
    if os.environ.get("PROTOWIRE_ORACLE_VENV"):
        sys.exit("the pinned oracle packages, with the upb backend, are not usable even in "
                 ".lake/oracle-venv")
    python = VENV / "bin" / "python"
    made = python.exists() or subprocess.run(
        [sys.executable, "-m", "venv", str(VENV)], capture_output=True).returncode == 0
    if made and not os.environ.get("PROTOWIRE_NO_VENV"):
        subprocess.run([str(python), "-m", "pip", "install", "--quiet", *PINS], check=True)
        env = dict(os.environ, PROTOWIRE_ORACLE_VENV="1")
        env.pop("PROTOCOL_BUFFERS_PYTHON_IMPLEMENTATION", None)
        os.execve(str(python), [str(python), *sys.argv], env)
    subprocess.run([sys.executable, "-m", "pip", "install", "--quiet", "--break-system-packages",
                    "--target", str(PKGS), *PINS], check=True)
    sys.path.insert(0, str(PKGS))
    os.environ.pop("PROTOCOL_BUFFERS_PYTHON_IMPLEMENTATION", None)
    for name in [m for m in sys.modules if m.startswith(("google", "grpc_tools"))]:
        del sys.modules[name]
    if not oracles_ready():
        sys.exit("the pinned oracle packages, with the upb backend, are not usable")


def oracles_ready():
    """Whether the pinned oracle versions import, with protobuf on upb."""
    from importlib.metadata import PackageNotFoundError, version
    try:
        import grpc_tools  # noqa: F401
        from google.protobuf.internal import api_implementation
        versions = [f"{p.split('==')[0]}=={version(p.split('==')[0])}" for p in PINS]
    except (ImportError, PackageNotFoundError):
        return False
    return versions == PINS and api_implementation.Type() == "upb"


# The oracles.

def upb_decode(data):
    """upb's reading: a list of (number, kind, value), or None."""
    from google.protobuf import empty_pb2
    from google.protobuf.message import DecodeError
    from google.protobuf.unknown_fields import UnknownFieldSet
    try:
        msg = empty_pb2.Empty.FromString(data)
    except DecodeError:
        return None
    fields = []
    for f in UnknownFieldSet(msg):
        kind = {0: "varint", 1: "i64", 2: "len", 3: "group", 5: "i32"}[f.wire_type]
        value = f.data.hex() if kind == "len" else (None if kind == "group" else f.data)
        fields.append((f.field_number, kind, value))
    return fields


def cpp_decode_raw(data):
    """The C++ parser's reading through `protoc --decode_raw`: the text it
    prints, or None when it refuses the input."""
    from grpc_tools import _protoc_compiler
    with tempfile.TemporaryFile() as fin, tempfile.TemporaryFile() as fout, \
            tempfile.TemporaryFile() as ferr:
        fin.write(data)
        fin.flush()
        fin.seek(0)
        saved = [os.dup(0), os.dup(1), os.dup(2)]
        try:
            os.dup2(fin.fileno(), 0)
            os.dup2(fout.fileno(), 1)
            os.dup2(ferr.fileno(), 2)
            code = _protoc_compiler.run_main([b"protoc", b"--decode_raw"])
        finally:
            for fd, s in zip((0, 1, 2), saved):
                os.dup2(s, fd)
                os.close(s)
        fout.seek(0)
        return fout.read().decode("utf-8", "backslashreplace") if code == 0 else None


TOP_VALUE = re.compile(r"(\d+): (.*)")
OPEN_LINE = re.compile(r" *\d+ \{")


def cpp_top_level(text):
    """The top-level (number, value text) pairs of `--decode_raw` output."""
    out, depth = [], 0
    for line in text.splitlines():
        # A nested message opens with a line `N {` and closes with a
        # line `}`; braces inside a quoted string are not structure.
        opens = OPEN_LINE.fullmatch(line) is not None
        if depth == 0:
            m = TOP_VALUE.fullmatch(line)
            if opens:
                out.append((int(line.split(" ")[0]), "{"))
            elif m:
                out.append((int(m.group(1)), m.group(2)))
        if opens:
            depth += 1
        elif line.strip() == "}":
            depth -= 1
    return out


def cpp_agrees(fields, text):
    """Whether the C++ reading has the same field numbers, in order, and
    the same numeric values."""
    top = cpp_top_level(text)
    if [n for n, _ in top] != [n for n, _, _ in fields]:
        return False
    for (n, kind, value), (_, shown) in zip(fields, top):
        if kind == "varint" and shown != str(value):
            return False
        if kind == "i32" and shown != f"0x{value:08x}":
            return False
        if kind == "i64" and shown != f"0x{value:016x}":
            return False
    return True


def oracle_encode(fields):
    from google.protobuf.internal import encoder
    out = b""
    for n, kind, value in fields:
        wt = {"varint": 0, "i64": 1, "len": 2, "i32": 5}[kind]
        out += encoder.TagBytes(n, wt)
        if kind == "varint":
            out += encoder._VarintBytes(value)
        elif kind == "i64":
            out += struct.pack("<Q", value)
        elif kind == "i32":
            out += struct.pack("<I", value)
        else:
            data = bytes.fromhex(value)
            out += encoder._VarintBytes(len(data)) + data
    return out


def show(fields):
    return "\t".join(["OK"] + [f"{n}:{k}:{v}" for n, k, v in fields])


# Four bytes with the high bit set, then a last byte with bits above the
# 32nd: a five-byte varint of 2^32 or more.
BIG_TAG = re.compile(rb"[\x80-\xff]{4}[\x10-\x7f]")


def expected_decode(data, tally):
    """The answer the Lean decoder must give, and why, by the rule in the
    module comment."""
    u = upb_decode(data)
    c = cpp_decode_raw(data)
    if u is None and c is None:
        return "REJECT", "both refuse"
    if u is None or c is None:
        if c is None:
            reason = ("field number 0, which upb reads and C++ refuses"
                      if any(n == 0 for n, _, _ in u) else "other inputs upb reads and C++ refuses")
        else:
            reason = ("a five-byte tag of 2^32 or more, which C++ reads and upb refuses"
                      if BIG_TAG.search(data) else "other inputs C++ reads and upb refuses")
        tally[reason] = tally.get(reason, 0) + 1
        return "REJECT", reason
    if any(k == "group" for _, k, _ in u):
        tally["a group, which both read"] = tally.get("a group, which both read", 0) + 1
        return "REJECT", "group"
    if not cpp_agrees(u, c):
        tally["C++ and upb read different fields"] = \
            tally.get("C++ and upb read different fields", 0) + 1
        return "REJECT", "references differ"
    return show(u), "both read"


# Generators.

def varint(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def long_varint(n, size):
    """`n` as a varint of exactly `size` bytes, padded with zero groups."""
    groups = []
    for _ in range(size):
        groups.append(n & 0x7F)
        n >>= 7
    return bytes([g | 0x80 for g in groups[:-1]] + [groups[-1]])


def random_number(rng):
    r = rng.random()
    if r < 0.6:
        return rng.randint(1, 15)
    if r < 0.8:
        return rng.choice([1, 15, 16, 2047, 2048, 262143, 262144, 2 ** 29 - 1, 19000, 19999])
    return rng.randint(1, 2 ** 29 - 1)


def random_u(rng, bits):
    r = rng.random()
    if r < 0.3:
        return rng.randint(0, 300)
    if r < 0.6:
        k = rng.randint(1, bits)
        return rng.choice([2 ** k - 1, 2 ** (k - 1), 2 ** k - 2]) % 2 ** bits
    return rng.getrandbits(bits)


def random_field(rng):
    kind = rng.choice(["varint", "varint", "len", "len", "i64", "i32"])
    n = random_number(rng)
    if kind == "varint":
        return (n, kind, random_u(rng, 64))
    if kind == "i64":
        return (n, kind, random_u(rng, 64))
    if kind == "i32":
        return (n, kind, random_u(rng, 32))
    size = rng.choice([0, 1, 3, 7, rng.randint(0, 40), rng.randint(0, 40), rng.randint(120, 300)])
    return (n, kind, bytes(rng.getrandbits(8) for _ in range(size)).hex())


def random_fields(rng):
    return [random_field(rng) for _ in range(rng.choice([0, 1, 1, 2, 3, 5, 8]))]


def mutate(rng, data):
    b = bytearray(data)
    op = rng.randrange(11)
    if op == 0 and b:
        b[rng.randrange(len(b))] = rng.getrandbits(8)
    elif op == 1 and b:
        del b[rng.randrange(len(b))]
    elif op == 2:
        b.insert(rng.randint(0, len(b)), rng.getrandbits(8))
    elif op == 3 and b:
        b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
    elif op == 4 and b:
        b = b[: rng.randrange(len(b))]
    elif op == 5:
        b += bytes(rng.getrandbits(8) for _ in range(rng.randint(1, 4)))
    elif op == 6:
        # A record whose tag is longer than it needs to be, up to and
        # past five bytes, in front.
        n, wt = random_number(rng), rng.choice([0, 0, 2, 5])
        payload = {0: varint(rng.randint(0, 300)), 2: b"\x01a", 5: b"\x00" * 4}[wt]
        size = rng.randint(len(varint(n * 8 + wt)), 7)
        b = bytearray(long_varint(n * 8 + wt, size) + payload) + b
    elif op == 7:
        # A varint value longer than it needs to be, up to and past ten bytes.
        size = rng.randint(1, 12)
        v = rng.getrandbits(min(64, 7 * size))
        b += varint(random_number(rng) * 8) + long_varint(v, size)
        if rng.random() < 0.3:
            b[-1] = rng.choice([0x01, 0x02, 0x7F, 0x80])
    elif op == 8:
        # Field number 0, a group, or wire type 6 or 7.
        wt = rng.choice([0, 3, 4, 6, 7])
        n = 0 if wt == 0 else random_number(rng)
        rec = varint(n * 8 + wt) + (varint(1) if wt == 0 else b"")
        if wt == 3 and rng.random() < 0.7:
            rec += varint(random_number(rng) * 8) + varint(5) + varint(n * 8 + 4)
        b = bytearray(rec) + b
    elif op == 9:
        # A five-byte tag of 2^32 or more, often exactly 2^32 plus a wire
        # type: field number 2^29, one past the largest.
        t = rng.choice([2 ** 32 + rng.choice([0, 1, 2, 5]), rng.randint(2 ** 32, 2 ** 35 - 1)])
        b = bytearray(long_varint(t, 5) + varint(1)) + b
    else:
        # A length varint longer than it needs to be, or past the end.
        data_ = bytes(rng.getrandbits(8) for _ in range(rng.randint(0, 5)))
        size = rng.randint(1, 7)
        claimed = len(data_) + rng.choice([0, 0, 1, -1 if data_ else 0, 2 ** 31])
        b += varint(random_number(rng) * 8 + 2) + long_varint(claimed, max(size, len(varint(claimed)))) + data_
    return bytes(b)


def invalid_fields(rng):
    fields = random_fields(rng) or [random_field(rng)]
    i = rng.randrange(len(fields))
    n, kind, value = fields[i]
    which = rng.randrange(4)
    if which == 0:
        n = 0
    elif which == 1:
        n = rng.choice([2 ** 29, 2 ** 29 + 1, 2 ** 29 + rng.randint(0, 1000), 2 ** 32])
    elif kind == "varint" or kind == "i64":
        value = rng.choice([2 ** 64, 2 ** 64 + 1, 2 ** 64 + rng.randint(0, 2 ** 20)])
    elif kind == "i32":
        value = rng.choice([2 ** 32, 2 ** 32 + 1, 2 ** 32 + rng.randint(0, 2 ** 20)])
    else:
        n = 0
    fields[i] = (n, kind, value)
    return fields


MALFORMED = [
    ("frob 00", "unknown operation"),
    ("DECODE 00", "operations are lower case"),
    ("decode", "no argument"),
    ("decode 0", "an odd number of hex digits"),
    ("decode 0g", "not a hex digit"),
    ("decode 0A", "hex digits are lower case"),
    ("decode 00 00", "two arguments"),
    ("encode", "no argument"),
    ("encode 1:varint", "a field item without a value"),
    ("encode 1:float:1", "an unknown kind"),
    ("encode 1:varint:-1", "a negative number"),
    ("encode 1:varint:1,", "an empty item"),
    ("encode 1:len:0", "odd hex in a len value"),
    ("encode x:varint:1", "a field number that is not a number"),
    (" decode 00", "a leading space"),
    ("", "an empty line"),
    ("decode 0896\r01", "a CR inside the request"),
    ("encode 1:varint:" + "1" * 31, "a number of more than 30 digits"),
]

AT_EOF = [("decode 089601", "OK\t1:varint:150"), ("encode 1:varint:150", "089601"),
          ("decode 089601\r\n", "OK\t1:varint:150")]


def fields_text(fields):
    return ",".join(f"{n}:{k}:{v}" for n, k, v in fields) if fields else "-"


def cases(seed, count, tally):
    """(label, request, expected answer, mutated) for each input."""
    rng = random.Random(seed)
    made = 0
    for req, _ in MALFORMED:
        if made < count:
            yield ("error", req, "error", False)
            made += 1
    while made < count:
        r = rng.random()
        if r < 0.3:
            fields = random_fields(rng)
            data = oracle_encode(fields)
            yield ("encode", f"encode {fields_text(fields)}", data.hex(), False)
            want, _ = expected_decode(data, tally)
            yield ("decode valid", f"decode {data.hex()}", want, False)
            made += 2
        elif r < 0.8:
            base = oracle_encode(random_fields(rng))
            data = mutate(rng, base)
            while data == base:
                data = mutate(rng, base)
            want, _ = expected_decode(data, tally)
            yield ("decode mutated", f"decode {data.hex()}", want, True)
            made += 1
        elif r < 0.92:
            data = bytes(rng.getrandbits(8) for _ in range(rng.randint(0, 12)))
            want, _ = expected_decode(data, tally)
            yield ("decode random", f"decode {data.hex()}", want, False)
            made += 1
        else:
            yield ("encode invalid", f"encode {fields_text(invalid_fields(rng))}", "INVALID", False)
            made += 1


def run_tool(data, timeout=TIMEOUT):
    """The tool's answer lines for `data`, and a note on how the run
    failed, or None."""
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (data.count("\n") + 1)
    try:
        proc = subprocess.Popen([str(EXE), "serve"], stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as e:
        return [], f"could not run {EXE.relative_to(ROOT)}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out, limit)),
               threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines, problem


def oracle():
    from importlib.metadata import version
    from google.protobuf.internal import api_implementation
    return (f"Python {platform.python_version()}, protobuf {version('protobuf')} "
            f"({api_implementation.Type()}), "
            f"grpcio-tools {version('grpcio-tools')} (protoc --decode_raw, C++)")


def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261025)
    ap.add_argument("--count", type=count, default=200_000)
    args = ap.parse_args()
    ensure_oracles()

    try:
        build = subprocess.run(["lake", "build", "protowire"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        built, log = build.returncode == 0, build.stdout + build.stderr
    except (OSError, subprocess.TimeoutExpired) as e:
        built, log = False, str(e)
    if not built:
        write(["# Test results", "", f"- Oracle: {oracle()}", f"- Seed: {args.seed}",
               "- Inputs: 0", "- Failures: 1 (`lake build protowire` failed)", ""])
        sys.exit("lake build protowire failed:\n" + log)

    tally = {}
    items = list(cases(args.seed, args.count, tally))
    # Every seventh request ends in CR LF, which the tool must take as LF.
    out, problem = run_tool("".join(req + ("\r\n" if i % 7 == 6 else "\n")
                                    for i, (_, req, _, _) in enumerate(items)))
    failures = [("(whole run)", "a clean run", problem)] if problem else []
    for item, got in itertools.zip_longest(items, out):
        if item is None:
            failures.append(("(no request)", "nothing", got))
        elif got != item[2]:
            failures.append((item[1], item[2], "(no answer)" if got is None else got))
    # The two parsers may disagree only in the ways the module comment
    # names; any other disagreement means an oracle changed.
    for reason, n in tally.items():
        if reason.startswith("other") or reason.startswith("C++ and upb read different"):
            failures.append((f"{n} inputs", "only the known disagreements", reason))

    eof_right = 0
    for req, want in AT_EOF:
        got, problem = run_tool(req, timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    by_label = {}
    for label, _, _, _ in items:
        by_label[label] = by_label.get(label, 0) + 1
    decodes = [want for label, req, want, _ in items if label.startswith("decode")]
    accepted = sum(1 for w in decodes if w.startswith("OK"))
    mutated = sum(1 for item in items if item[3])
    malformed = [got for item, got in zip(items, out) if item[0] == "error"]

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Oracle: {oracle()}",
        f"- Lean: {lean_version()}",
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        f"- Mutated: {mutated} of the inputs are mutated encodings",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Messages decoded: {len(decodes)}, of which {accepted} read by both reference "
        f"parsers alike and {len(decodes) - accepted} refused",
        "- Refused although a reference parser reads them: " +
        (", ".join(f"{k} {v}" for k, v in sorted(tally.items())) or "none"),
        f"- Malformed requests answered `error`: {malformed.count('error')} of "
        f"{by_label.get('error', 0)}",
        f"- Requests ending in CR LF: every seventh, {len(items) // 7}",
        f"- Last lines sent alone, with no LF or with CR LF, answered right: {eof_right} of "
        f"{len(AT_EOF)}",
        f"- Failures: {len(failures)}",
        "",
    ]
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- `{req[:160]!r}`: expected `{want[:120]!r}`, got `{got[:120]!r}`"
                  for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    agree = sum(1 for item, got in zip(items, out) if got == item[2])
    print(f"{agree}/{len(items)} inputs agree, {len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
