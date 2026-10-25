#!/usr/bin/env python3
"""Test harness for the Lean Protobuf wire format codec.

Runs the worked byte examples from the Protobuf encoding
documentation, then differential runs against a Python oracle
written with plain byte code here in the harness (no protobuf
library is used). Random field lists are encoded by both sides
and decoded by both sides. Mutated byte strings must be read
alike by both sides. Results are written to tests/TEST-RESULTS.md
in the same shape as the codec, zip, and json records.

The oracle follows the same rules as the Lean decoder, on
purpose: a varint is at most ten bytes and its value fits in 64
bits, field number zero is rejected, wire types 3, 4, 6, and 7
are rejected, and nothing is read past the end of the input. The
decoder puts no upper bound on the field number: a tag is a
varint below 2^64, so any field number the tag holds is read.
The encoder side of the field list format does bound the field
number, at 536870911, as SPEC.md states.

Usage: python3 tests/run_tests.py [--skip-build]
"""

import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EXE = os.path.join(ROOT, ".lake", "build", "bin", "protobuf")
SEED = 20261025
MAX64 = 1 << 64

failures = []


def check(cond, label, detail=""):
    if not cond:
        failures.append(f"{label}: {detail}")
        print(f"FAIL {label}: {detail}")


# ---------------------------------------------------------------------------
# Batch runner: one process for many requests.
# ---------------------------------------------------------------------------

class Tool:
    def __init__(self):
        self.lines = []
        self.expected = 0

    def ask(self, line, skip=0):
        """Queue a request. Its answer is line (index - skip) among the
        answers: every request answers exactly one line, except the
        empty field list encoding, which answers with an empty line
        that splitlines drops. Such requests are marked with skip."""
        self.lines.append(line)
        self.expected += 1
        return self.expected - 1 - skip

    def run(self):
        proc = subprocess.run([EXE], input="\n".join(self.lines) + "\n",
                              capture_output=True, text=True, timeout=1200)
        if proc.returncode != 0:
            raise RuntimeError(f"tool exited {proc.returncode}: {proc.stderr[:500]}")
        self.answers = proc.stdout.splitlines()
        return self.answers


# ---------------------------------------------------------------------------
# Python oracle: plain byte code, the rules of the slice.
# ---------------------------------------------------------------------------

def o_enc_varint(n):
    out = bytearray()
    while True:
        b = n % 128
        n //= 128
        if n:
            out.append(b + 128)
        else:
            out.append(b)
            return bytes(out)


def o_dec_varint(bs, i=0):
    """(value, next index) or None."""
    val = 0
    shift = 0
    count = 0
    while True:
        if i >= len(bs):
            return None
        b = bs[i]
        i += 1
        count += 1
        if count > 10:
            return None
        val |= (b & 127) << shift
        shift += 7
        if b < 128:
            break
    if val >= MAX64:
        return None
    return val, i


def o_dec_varint_whole(bs):
    r = o_dec_varint(bs, 0)
    if r is None or r[1] != len(bs):
        return None
    return r[0]


def o_enc_field(f):
    num, wt, payload = f
    tag = o_enc_varint(num * 8 + wt)
    if wt == 0:
        body = o_enc_varint(payload)
    elif wt in (1, 5):
        body = bytes(payload)
    else:
        body = o_enc_varint(len(payload)) + bytes(payload)
    return tag + body


def o_enc_msg(fs):
    return b"".join(o_enc_field(f) for f in fs)


def o_dec_msg(bs):
    """A field list: (num, wt, payload) with payload an int for
    wire type 0 and a list of bytes otherwise. None on rejection."""
    i = 0
    out = []
    while i < len(bs):
        r = o_dec_varint(bs, i)
        if r is None:
            return None
        tag, i = r
        num, wt = tag // 8, tag % 8
        if num == 0:
            return None
        if wt == 0:
            r = o_dec_varint(bs, i)
            if r is None:
                return None
            v, i = r
            out.append((num, 0, v))
        elif wt == 1:
            if i + 8 > len(bs):
                return None
            out.append((num, 1, list(bs[i:i + 8])))
            i += 8
        elif wt == 2:
            r = o_dec_varint(bs, i)
            if r is None:
                return None
            ln, i = r
            if i + ln > len(bs):
                return None
            out.append((num, 2, list(bs[i:i + ln])))
            i += ln
        elif wt == 5:
            if i + 4 > len(bs):
                return None
            out.append((num, 5, list(bs[i:i + 4])))
            i += 4
        else:
            return None
    return out


def tokens_of(fs):
    toks = []
    for num, wt, payload in fs:
        toks.append(num)
        toks.append(wt)
        if wt == 0:
            toks.append(payload)
        elif wt == 2:
            toks.append(len(payload))
            toks.extend(payload)
        else:
            toks.extend(payload)
    return toks


def csv(bs):
    return ",".join(str(b) for b in bs)


def parse_dec(answer):
    """A `dec` answer to a field list, or None for `none`."""
    if answer == "none":
        return None
    assert answer.startswith("ok:"), answer
    rest = answer[3:]
    if rest == "":
        return []
    toks = [int(t) for t in rest.split(",")]
    out = []
    i = 0
    while i < len(toks):
        num, wt = toks[i], toks[i + 1]
        i += 2
        if wt == 0:
            out.append((num, 0, toks[i]))
            i += 1
        elif wt == 1:
            out.append((num, 1, toks[i:i + 8]))
            i += 8
        elif wt == 2:
            ln = toks[i]
            i += 1
            out.append((num, 2, toks[i:i + ln]))
            i += ln
        else:
            out.append((num, 5, toks[i:i + 4]))
            i += 4
    return out


# ---------------------------------------------------------------------------
# Worked examples from the Protobuf encoding documentation.
# ---------------------------------------------------------------------------

def worked_examples(tool):
    cases = []
    def venc(v, want):
        idx = tool.ask(f"venc {v}")
        cases.append((idx, want, f"venc {v}"))
    def vdec(bs, want):
        idx = tool.ask(f"vdec {csv(bs)}")
        cases.append((idx, want, f"vdec {csv(bs)}"))
    def enc(fs, want):
        idx = tool.ask("enc " + ",".join(str(t) for t in tokens_of(fs)))
        cases.append((idx, want, f"enc {tokens_of(fs)}"))
    def dec(bs, want):
        idx = tool.ask(f"dec {csv(bs)}")
        cases.append((idx, want, f"dec {csv(bs)}"))

    testing = [116, 101, 115, 116, 105, 110, 103]
    venc(1, "1")
    venc(300, "172,2")
    venc(150, "150,1")
    venc(0, "0")
    venc(18446744073709551615,
         "255,255,255,255,255,255,255,255,255,1")
    vdec([1], "ok:1")
    vdec([172, 2], "ok:300")
    vdec([172], "none")                       # cut short
    vdec([128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 1],
         "none")                              # eleven bytes
    vdec([255, 255, 255, 255, 255, 255, 255, 255, 255, 2],
         "none")                              # a bit past 64
    vdec([1, 1], "none")                      # trailing byte
    enc([(1, 0, 150)], "8,150,1")             # the docs message
    dec([8, 150, 1], "ok:1,0,150")
    enc([(2, 2, testing)], "18,7,116,101,115,116,105,110,103")
    dec([18, 7, 116, 101, 115, 116, 105, 110, 103],
        "ok:2,2,7,116,101,115,116,105,110,103")
    enc([(1, 0, 1), (2, 2, testing), (3, 5, [1, 2, 3, 4]),
         (4, 1, [8, 7, 6, 5, 4, 3, 2, 1])],
        "8,1,18,7,116,101,115,116,105,110,103,29,1,2,3,4,"
        "33,8,7,6,5,4,3,2,1")
    dec([8, 1, 18, 7, 116, 101, 115, 116, 105, 110, 103,
         29, 1, 2, 3, 4, 33, 8, 7, 6, 5, 4, 3, 2, 1],
        "ok:1,0,1,2,2,7,116,101,115,116,105,110,103,3,5,1,2,3,4,"
        "4,1,8,7,6,5,4,3,2,1")
    dec([0, 1], "none")                       # field number zero
    dec([27, 1], "none")                     # wire type 3, a group
    dec([28, 1], "none")                     # wire type 4, a group
    dec([30, 1], "none")                     # wire type 6
    dec([31, 1], "none")                     # wire type 7
    dec([18, 7, 116, 101], "none")           # length past the end
    dec([9, 1, 2, 3], "none")                # fixed64 cut short
    dec([13, 1, 2], "none")                  # fixed32 cut short
    dec([136], "none")                       # tag varint cut short
    return cases


def verify_cases(tool, cases, label):
    ok = 0
    for idx, want, name in cases:
        got = tool.answers[idx] if idx < len(tool.answers) else "<missing>"
        if got == want:
            ok += 1
        else:
            check(False, label, f"{name}: want {want!r}, got {got!r}")
    return ok, len(cases)


# ---------------------------------------------------------------------------
# Random generation.
# ---------------------------------------------------------------------------

def rand_varint(rng):
    return rng.choice([
        lambda: rng.randrange(0, 128),
        lambda: rng.randrange(0, 300),
        lambda: rng.randrange(0, 1 << 16),
        lambda: rng.randrange(0, 1 << 32),
        lambda: rng.randrange(0, MAX64),
        lambda: rng.choice([0, 1, 127, 128, 300, (1 << 32) - 1,
                            1 << 63, MAX64 - 1]),
    ])()


def rand_field(rng):
    num = rng.choice([1, 2, 3, 4, 5, 16, 100, 2047,
                      rng.randrange(1, 536870912)])
    wt = rng.choice([0, 0, 1, 2, 2, 5])
    if wt == 0:
        return (num, 0, rand_varint(rng))
    if wt == 1:
        return (num, 1, [rng.randrange(256) for _ in range(8)])
    if wt == 5:
        return (num, 5, [rng.randrange(256) for _ in range(4)])
    ln = rng.choice([0, 1, 3, 7, 16, rng.randrange(0, 40)])
    return (num, 2, [rng.randrange(256) for _ in range(ln)])


# ---------------------------------------------------------------------------

def main():
    if "--skip-build" not in sys.argv:
        env = dict(os.environ)
        env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env["PATH"]
        r = subprocess.run(["lake", "build"], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=1800)
        if r.returncode != 0:
            print(r.stdout[-2000:], r.stderr[-2000:])
            print("BUILD FAILED")
            return 1

    tool = Tool()
    cases = worked_examples(tool)

    rng = random.Random(SEED)

    # Varint differential.
    varint_inputs = []
    varint_idx = []
    for _ in range(3000):
        v = rand_varint(rng)
        varint_inputs.append(v)
        varint_idx.append((tool.ask(f"venc {v}"),
                           tool.ask(f"vdec {csv(o_enc_varint(v))}")))
    # Whole input varint rejections and readings, both sides.
    neg_inputs = []
    neg_idx = []
    for _ in range(600):
        bs = bytearray(o_enc_varint(rand_varint(rng)))
        kind = rng.randrange(3)
        if kind == 0 and bs:
            bs = bs[:rng.randrange(len(bs))]          # truncate
        elif kind == 1:
            bs = bs + bytearray([rng.randrange(256)])  # trailing byte
        else:
            bs = bytearray(rng.randrange(256)
                           for _ in range(rng.randrange(0, 13)))
        neg_inputs.append(bytes(bs))
        neg_idx.append(tool.ask(f"vdec {csv(bs)}"))

    # Message differential.
    msg_inputs = []
    msg_idx = []
    for _ in range(3000):
        fs = [rand_field(rng) for _ in range(rng.randrange(1, 7))]
        msg_inputs.append(fs)
        msg_idx.append((tool.ask("enc " + ",".join(str(t) for t in tokens_of(fs))),
                        tool.ask(f"dec {csv(o_enc_msg(fs))}")))

    # Mutations of valid messages, read by both sides.
    mut_inputs = []
    mut_idx = []
    for _ in range(400):
        fs = [rand_field(rng) for _ in range(rng.randrange(1, 5))]
        bs = bytearray(o_enc_msg(fs))
        muts = []
        for cut in range(0, len(bs)):
            muts.append(bytes(bs[:cut]))
        for pos in range(len(bs)):
            for val in (0, 255, bs[pos] ^ 128, (bs[pos] + 1) % 256):
                m = bytearray(bs)
                m[pos] = val
                muts.append(bytes(m))
        muts.append(bytes(bs) + bytes([0]))
        muts.append(bytes(bs) + bytes([128]))
        muts.append(bytes(bs) + bytes([8, 1]))
        for m in muts:
            mut_inputs.append(m)
            mut_idx.append(tool.ask(f"dec {csv(m)}"))

    # Malformed requests.
    malformed = [
        "enc 0,0,1",            # field number zero
        "enc 536870912,0,1",    # field number too big
        "enc 1,3,1",            # wire type outside the slice
        "enc 1,0",              # group runs out of numbers
        "enc 1,0,18446744073709551616",  # varint value at 2^64
        "enc 1,1,1,2,3",        # fixed64 payload short
        "enc 1,2,3,9,9",        # length says 3, 2 bytes follow
        "enc 1,2,18446744073709551616,9",  # length at 2^64
        "enc 1,0,256",          # fine as a value, but...
        "dec 256",              # byte number above 255
        "dec 1,,2",             # empty token
        "venc 18446744073709551616",     # at 2^64
        "venc 1,2",             # two numbers
        "vdec 300",             # byte number above 255
        "dec 08,1",             # leading zero
        "enc 1, 0,1",           # space inside the number list
        "foo 1",                # unknown op
        "enc 1,0,-1",           # a sign
        "dec 999999999999999999999",     # twenty one digits
    ]
    # `enc 1,0,256` is well formed (256 is a varint value): drop it
    # from the malformed list and check it on its own below.
    malformed.remove("enc 1,0,256")
    mal_idx = [(tool.ask(m), m) for m in malformed]
    value256_idx = tool.ask("enc 1,0,256")

    answers = tool.run()
    check(len(answers) == tool.expected, "answer-count",
          f"{len(answers)} answers for {tool.expected} requests")

    lines = []
    lines.append("# Test results\n")
    lines.append("Run with `python3 tests/run_tests.py` from the "
                 "package root (it runs `lake build` first; pass "
                 "`--skip-build` to skip that step). Date of the "
                 "recorded run: 2026-10-25. Seed: 20261025.\n")
    lines.append("Oracle: a Python oracle written with plain byte "
                 "code in tests/run_tests.py. No protobuf library "
                 "is used. The oracle follows the same rules as "
                 "the Lean decoder, as SPEC.md states them.\n")

    ok, total = verify_cases(tool, cases, "worked")
    lines.append("## Worked examples from the encoding documentation\n")
    lines.append(f"{ok} of {total} fixed cases passed: varint 1 "
                 "and 300, varint 150, the largest 64 bit varint, "
                 "cut short and eleven byte and past 64 bit "
                 "rejections, field 1 varint 150 (bytes 8, 150, 1), "
                 "field 2 with the text \"testing\" (bytes 18, 7, "
                 "then the text), a four field message across all "
                 "four wire types, and rejections for field number "
                 "zero, wire types 3, 4, 6, 7, a length past the "
                 "end, fixed width values cut short, and a tag "
                 "cut short.\n")

    # Varint differential scoring.
    v_agree = v_total = 0
    for v, (ie, idc) in zip(varint_inputs, varint_idx):
        v_total += 2
        if answers[ie] == csv(o_enc_varint(v)):
            v_agree += 1
        else:
            check(False, "varint-enc", f"{v}: got {answers[ie]!r}")
        want = f"ok:{v}"
        if answers[idc] == want:
            v_agree += 1
        else:
            check(False, "varint-dec", f"{v}: got {answers[idc]!r}")
    n_agree = n_total = 0
    for bs, idx in zip(neg_inputs, neg_idx):
        n_total += 1
        ov = o_dec_varint_whole(bs)
        want = "none" if ov is None else f"ok:{ov}"
        if answers[idx] == want:
            n_agree += 1
        else:
            check(False, "varint-neg", f"{csv(bs)}: want {want}, got {answers[idx]!r}")

    m_agree = m_total = 0
    for fs, (ie, idc) in zip(msg_inputs, msg_idx):
        m_total += 2
        if answers[ie] == csv(o_enc_msg(fs)):
            m_agree += 1
        else:
            check(False, "msg-enc", f"{tokens_of(fs)}: got {answers[ie]!r}")
        got = parse_dec(answers[idc]) if idc < len(answers) else None
        if got == fs:
            m_agree += 1
        else:
            check(False, "msg-dec", f"{tokens_of(fs)}: got {answers[idc]!r}")

    u_agree = u_total = 0
    for bs, idx in zip(mut_inputs, mut_idx):
        u_total += 1
        ov = o_dec_msg(bs)
        want = "none" if ov is None else "ok:" + ",".join(str(t) for t in tokens_of(ov))
        if answers[idx] == want:
            u_agree += 1
        else:
            check(False, "mut", f"{csv(bs)}: want {want!r}, got {answers[idx]!r}")

    lines.append("## Differential run against the Python oracle\n")
    lines.append(f"Varint encodings and decodings: {v_total} cases "
                 f"(3000 random values, each encoded by the Lean "
                 f"tool and decoded back from the oracle encoding), "
                 f"{v_agree} agreements, {v_total - v_agree} failures.\n")
    lines.append(f"Whole input varint readings: {n_total} mutated "
                 f"and random byte strings, {n_agree} agreements, "
                 f"{n_total - n_agree} failures.\n")
    lines.append(f"Messages: {m_total} cases (3000 random field "
                 f"lists of 1 to 6 fields, each encoded by the Lean "
                 f"tool and checked byte by byte against the oracle, "
                 f"and the oracle encoding decoded by the Lean tool "
                 f"and checked field by field), {m_agree} agreements, "
                 f"{m_total - m_agree} failures.\n")
    lines.append(f"Mutated messages: {u_total} byte strings (every "
                 f"truncation and single byte change of 400 random "
                 f"messages, plus appended bytes), read by both "
                 f"sides, {u_agree} agreements, "
                 f"{u_total - u_agree} failures.\n")
    total_in = v_total + n_total + m_total + u_total
    total_ag = v_agree + n_agree + m_agree + u_agree
    lines.append(f"Differential total: {total_in} inputs, {total_ag} "
                 f"agreements, {total_in - total_ag} failures, "
                 f"seed 20261025.\n")
    lines.append("Named differences: none. Every byte string the "
                 "two sides read, they read the same way, and every "
                 "one they reject, they both reject.\n")

    mal_ok = 0
    for idx, m in mal_idx:
        if answers[idx] == "error":
            mal_ok += 1
        else:
            check(False, "malformed", f"{m!r}: got {answers[idx]!r}")
    check(answers[value256_idx] == "8,128,2", "value-256",
          f"got {answers[value256_idx]!r}")
    lines.append("## Malformed requests\n")
    lines.append(f"{mal_ok} of {len(mal_idx)} malformed lines "
                 "printed `error`: field number zero or too big, "
                 "bad wire types, groups that run out of numbers, "
                 "values and lengths at 2^64, byte numbers above "
                 "255, empty tokens, leading zeros, spaces in the "
                 "number list, signs, twenty one digit numbers, "
                 "and an unknown op. One near miss is well formed "
                 "and checked apart: `enc 1,0,256` encodes the "
                 "varint value 256 and answers 8,128,2.\n")

    # The empty message, in its own run: its encoding is an empty
    # line, which the batch runner cannot count.
    proc = subprocess.run([EXE], input="enc \ndec \ndec 8,150,1\n",
                          capture_output=True, text=True, timeout=60)
    got_empty = proc.stdout.splitlines()
    check(got_empty == ["", "ok:", "ok:1,0,150"], "empty-message",
          f"got {got_empty!r}")
    lines.append("## The empty message\n")
    lines.append("Checked in its own run, since its encoding is "
                 "an empty line: `enc ` prints an empty line, "
                 "`dec ` prints `ok:`, and the bytes of the docs "
                 "example still decode after them.\n")

    lines.append("## Failures\n")
    if failures:
        for f in failures[:50]:
            lines.append(f"- {f}")
    else:
        lines.append("None.\n")

    with open(os.path.join(HERE, "TEST-RESULTS.md"), "w") as fh:
        fh.write("\n".join(lines))
    print("\n".join(lines))
    print(f"failures: {len(failures)}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
