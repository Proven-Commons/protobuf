# protobuf: the Protobuf wire format, proved

This library reads and writes the Protobuf wire format in Lean: varints, field tags, and messages as lists of raw fields. Machine-checked proofs show three things:

- the decoder accepts exactly the byte strings the encoding guide's rules allow, and refuses everything else, including input cut short;
- the encoder writes what the guide describes;
- decoding what the encoder wrote gives the fields back.

It is tested against Google's own parsers, upb and C++; `tests/TEST-RESULTS.md` has the record.

It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean:

- `Protobuf.decode` reads a whole message as a list of fields, or fails.
- `Protobuf.encode` writes a list of fields.
- `Field.isValid` says whether a field can be written.
- `Varint.encode` and `Varint.decode` work on single varints.

`SPEC.md` says what each one does.

## What is proved

The statements are in `Spec.lean`. The definitions they use, written from the encoding guide, are in `Spec/Defs.lean`, and the types are in `Protobuf/Types.lean`. The proofs are in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| The encoder writes the shortest varint. | `Spec.varint_encode_eq` |
| The varint decoder reads exactly one varint of up to ten bytes from the front of its input, leaves the rest untouched, and refuses everything else. That includes input that ends inside the varint, and an eleventh byte. | `Spec.varint_decode_iff` |
| Decoding a varint the encoder wrote gives the number back. | `Spec.varint_decode_encode` |
| `isValid` decides exactly which fields can be written: field numbers 1 to 2^29 - 1, and values that fit their wire type. | `Spec.isValid_iff` |
| The encoder writes each field as the guide describes: the tag, then the payload, every varint in its shortest form. | `Spec.encode_eq` |
| `decode` returns a field list exactly when the bytes split into records, one per field, in order. So it reads every well-formed message and returns the fields as written. It refuses everything else: a record cut short, a length past the end, field number 0, a group, an unknown wire type, and an oversized tag or length. | `Spec.decode_iff` |
| Decoding what the encoder wrote gives the fields back. | `Spec.decode_encode` |
| Every field the decoder returns can be written again. | `Spec.decode_valid` |
| The guide's worked examples, and the edge and refusal cases listed in `SPEC.md`. | `Spec.guide_vectors`, `Spec.edge_vectors`, `Spec.reject_vectors` |

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- Reading requests and printing answers in `Main.lean`: the hex and decimal parsing and printing, and the request format. The differential tests cover them, with malformed requests.
- Groups (wire types 3 and 4) are refused, although both reference parsers read them. They are deprecated in the encoding guide and left for a later slice.
- Where the two reference parsers disagree, this decoder takes the stricter reading:
  - it refuses field number 0, which upb reads;
  - it refuses a tag of 2^32 or more, which the C++ parser reads by dropping the high bits.
- What fields mean. Schemas, `.proto` files, field types such as signed or zigzag integers, floats, strings, nested messages and packed repeated fields all sit above the wire format. A `LEN` field's bytes are returned as they are.
- Limits on message size and nesting that a program may want. The decoder reads any input in memory. A `LEN` field must be shorter than 2^31 bytes, as in the reference parsers.
- Speed. The code works on lists of bytes, which suits proofs, not bulk data.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about (by `implemented_by` and `extern`), such as the arithmetic on natural numbers and the fixed-width byte type.
- The operating system and hardware it runs on.
- Python's `protobuf` and `grpcio-tools` packages, as the oracle in the differential tests. The record names their versions.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), and Python 3.11 or later with `venv`, and network access for the oracle packages.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script installs the pinned oracle packages into `.lake/oracle-venv` when they are missing. It then compares the tool with upb and with the C++ parser on inputs from a recorded seed, and rewrites `tests/TEST-RESULTS.md`.

## Layout

- `Protobuf/Types.lean`: the field and value types. It is part of the specification.
- `Protobuf/Varint.lean`, `Protobuf/Wire.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the encoding guide, with checks against its worked bytes.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
