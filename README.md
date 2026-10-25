# protobuf

A Lean Protobuf wire format codec: varints, field tags, and
messages of raw fields, with the round trips proved.

The package works at the level of bytes only. A message is a
list of fields; each field holds a field number and a raw value:
a varint number, eight bytes, a length delimited byte string,
or four bytes. There are no `.proto` schemas and no field
meanings here: what a field means lives in a schema, and a
schema sits outside this slice. A packed repeated field is
simply a length delimited byte string at this level.

Files:

- `Protobuf/Wire.lean` holds the value and field types, the
  varint encoder and decoder, the field and message encoder and
  decoder, and the well formedness rules the proofs use.
- `Proofs/RoundTrip.lean` proves the round trips.
- `Proofs/Examples.lean` proves the worked examples from the
  Protobuf encoding documentation.
- `Protobuf/Verify.lean` prints the axioms the claims rest on.
- `Main.lean` is a command line front end over the codec.
- `SPEC.md` is the specification in prose.
- `tests/run_tests.py` runs the worked examples and a
  differential run against a Python oracle, and writes
  `tests/TEST-RESULTS.md`.

## Using the codec

Build once:

```sh
lake build
```

The tool reads one request per line. A request is an operation,
one space, and a list of decimal numbers parted by commas. The
operations are `venc` and `vdec` for one varint, and `enc` and
`dec` for a message. A field list is read as groups: field
number, wire type, then the payload (one number for wire type
0, eight byte numbers for type 1, a length and that many byte
numbers for type 2, four byte numbers for type 5). The full
format rules are in `SPEC.md`.

```console
$ printf 'venc 300\nenc 1,0,150\nenc 2,2,7,116,101,115,116,105,110,103\ndec 8,150,1\n' | .lake/build/bin/protobuf
172,2
8,150,1
18,7,116,101,115,116,105,110,103
ok:1,0,150
```

The first line is 300 as a varint. The second is the docs
message: field 1 holding the varint 150. The third is field 2
holding the text "testing". The fourth decodes the second
line's bytes back to their field list.

`dec` prints `none` for well formed bytes this slice rejects
(a group tag, a length past the end, a field cut short), and
any malformed request line prints `error`.

## Tests

```sh
python3 tests/run_tests.py
```

The harness checks the worked examples byte by byte (the same
examples are also proved in `Proofs/Examples.lean`), then runs
a differential comparison against a Python oracle written with
plain byte code in the harness: random field lists are encoded
by both sides and decoded by both sides, mutated byte strings
must be read alike, and varints are run both ways on their own.
Run of 2026-10-25: 26 fixed cases passed, 52440 differential
inputs, 52440 agreements, 0 failures, seed 20261025. The full
record is in `tests/TEST-RESULTS.md`.

## What is proved

With the build passing and no `sorry` anywhere:

- **Varint round trip** (`Protobuf.Proofs.decodeVarint_encode`):
  for any natural number below 2^64, decoding its encoding
  gives the number back with no leftover. The appended form
  (`decodeVarint_encode_append`) shows that bytes after the
  encoding are left alone.
- **Message round trip** (`Protobuf.Proofs.decodeMessage_encode`,
  by way of `parseField_encode`): decoding the encoding of a
  well formed field list gives the same list back. Well formed
  means field numbers from 1 to 536870911, varint values and
  lengths below 2^64, and fixed width values of the right byte
  count.
- **Worked examples** (`Protobuf.Examples`): the byte examples
  from the Protobuf encoding documentation, proved, including
  the largest 64 bit varint and the rejections for a bit past
  64 and for eleven byte varints.

## What is not proved

- Which byte strings are accepted is covered by tests, not
  proof. The proofs cover the round trips.
- There is no decode then encode claim for arbitrary bytes: a
  varint written long reads fine but writes back short, and a
  field number above 536870911 can be read off the wire but is
  outside the field list format, so it cannot be written back.
- No schemas or meanings: no `.proto` files, no field types, no
  signed or zigzag readings, no packed field contents.
- Groups are rejected, not read. Wire types 3, 4, 6, and 7 all
  reject the message.
- Soundness of the readings rests on the code matching
  `SPEC.md`; the differential run is the check for that.

## What you must trust

- The Lean kernel and the way `#print axioms` reports proof
  dependencies.
- That `SPEC.md` states the wire rules you care about. The code
  is written to it and the oracle mirrors it, so a rule stated
  wrong in the same way in both would not be caught by the
  differential run. The worked examples, taken from the
  Protobuf documentation itself, are the outside anchor.
- The Python oracle in the harness is a reading check only; the
  proofs do not depend on it.

## How to re-check

```sh
lake build                            # the package and the proofs
grep -rn sorry Protobuf Proofs Main.lean   # only the sorryAx comment in Verify.lean
lake env lean Protobuf/Verify.lean    # axioms: only the standard ones
python3 tests/run_tests.py            # the worked examples and the differential run
```

`Verify.lean` is not part of the build; run it by hand as
above. Each claim should list only standard axioms (the
recorded run shows propext and Quot.sound, a subset of the
usual three). A line naming `sorryAx` would mean a proof rests
on an admitted gap.
