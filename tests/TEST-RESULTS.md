# Test results

Run with `python3 tests/run_tests.py` from the package root (it runs `lake build` first; pass `--skip-build` to skip that step). Date of the recorded run: 2026-10-25. Seed: 20261025.

Oracle: a Python oracle written with plain byte code in tests/run_tests.py. No protobuf library is used. The oracle follows the same rules as the Lean decoder, as SPEC.md states them.

## Worked examples from the encoding documentation

26 of 26 fixed cases passed: varint 1 and 300, varint 150, the largest 64 bit varint, cut short and eleven byte and past 64 bit rejections, field 1 varint 150 (bytes 8, 150, 1), field 2 with the text "testing" (bytes 18, 7, then the text), a four field message across all four wire types, and rejections for field number zero, wire types 3, 4, 6, 7, a length past the end, fixed width values cut short, and a tag cut short.

## Differential run against the Python oracle

Varint encodings and decodings: 6000 cases (3000 random values, each encoded by the Lean tool and decoded back from the oracle encoding), 6000 agreements, 0 failures.

Whole input varint readings: 600 mutated and random byte strings, 600 agreements, 0 failures.

Messages: 6000 cases (3000 random field lists of 1 to 6 fields, each encoded by the Lean tool and checked byte by byte against the oracle, and the oracle encoding decoded by the Lean tool and checked field by field), 6000 agreements, 0 failures.

Mutated messages: 39840 byte strings (every truncation and single byte change of 400 random messages, plus appended bytes), read by both sides, 39840 agreements, 0 failures.

Differential total: 52440 inputs, 52440 agreements, 0 failures, seed 20261025.

Named differences: none. Every byte string the two sides read, they read the same way, and every one they reject, they both reject.

## Malformed requests

18 of 18 malformed lines printed `error`: field number zero or too big, bad wire types, groups that run out of numbers, values and lengths at 2^64, byte numbers above 255, empty tokens, leading zeros, spaces in the number list, signs, twenty one digit numbers, and an unknown op. One near miss is well formed and checked apart: `enc 1,0,256` encodes the varint value 256 and answers 8,128,2.

## The empty message

Checked in its own run, since its encoding is an empty line: `enc ` prints an empty line, `dec ` prints `ok:`, and the bytes of the docs example still decode after them.

## Failures

None.
