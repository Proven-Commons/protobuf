# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17, protobuf 7.36.2 (upb), grpcio-tools 1.84.1 (protoc --decode_raw, C++)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 200000
- Mutated: 77017 of the inputs are mutated encodings
- By kind: decode mutated 77017, decode random 18395, decode valid 46084, encode 46084, encode invalid 12402, error 18
- Messages decoded: 141496, of which 73280 read by both reference parsers alike and 68216 refused
- Refused although a reference parser reads them: a five-byte tag of 2^32 or more, which C++ reads and upb refuses 650, a group, which both read 981, field number 0, which upb reads and C++ refuses 1688
- Malformed requests answered `error`: 18 of 18
- Requests ending in CR LF: every seventh, 28571
- Last lines sent alone, with no LF or with CR LF, answered right: 3 of 3
- Failures: 0
