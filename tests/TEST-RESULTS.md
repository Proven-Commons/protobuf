# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17, protobuf 7.36.2 (upb), grpcio-tools 1.84.1 (protoc --decode_raw, C++)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 200000
- Mutated: 77137 of the inputs are mutated encodings
- By kind: decode mutated 77137, decode random 18392, decode valid 46010, encode 46010, encode invalid 12436, error 15
- Messages decoded: 141539, of which 73247 read by both reference parsers alike and 68292 refused
- Refused although a reference parser reads them: a five-byte tag of 2^32 or more, which C++ reads and upb refuses 1253, a group, which both read 1022, field number 0, which upb reads and C++ refuses 1700
- Malformed requests answered `error`: 15 of 15
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
