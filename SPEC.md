# Specification: protobuf

This library implements the Protobuf wire format: varints, field tags, and messages as lists of raw fields. It is the layer under every `.proto` schema. It reads and writes the bytes without knowing what the fields mean. A reviewer who did not write this specification approves it. The approval also covers `Protobuf/Spec.lean`, `Protobuf/Spec/Defs.lean`, `Protobuf/Types.lean`, and the other files `bar.toml` lists.

The source is the Protobuf encoding guide, <https://protobuf.dev/programming-guides/encoding/>. Where the guide leaves a choice, the source is the behaviour of Google's two parsers: upb, which Python's `protobuf` package uses, and the C++ parser behind `protoc --decode_raw`.

Bytes are `List UInt8`. The command-line tool converts them at the edges.

## Varints

A varint carries an unsigned number seven bits to a byte, least significant group first. The high bit of each byte is set when another byte follows.

- `Varint.encode` writes the shortest varint for a number below 2^64, from one to ten bytes.
- `Varint.decode` reads one varint from the front of its input and returns its value and the rest of the input.
  - It reads up to ten bytes.
  - It fails when the input ends inside the varint, or when the tenth byte still has its high bit set.
  - Any bits above the 64th are dropped, as both reference parsers drop them.
  - A varint need not be in its shortest form: `80 00` reads as 0, as in both reference parsers.

## Fields

A message is a sequence of records. Each record is a tag, then a payload. The tag is a varint of `field_number * 8 + wire_type`.

| Wire type | Name | Payload | Value here |
|-----------|------|---------|------------|
| 0 | `VARINT` | a varint | `.varint v`, below 2^64 |
| 1 | `I64` | eight bytes | `.i64 v`, the bytes little-endian |
| 2 | `LEN` | a varint length, then that many bytes | `.len bytes` |
| 5 | `I32` | four bytes | `.i32 v`, the bytes little-endian |

The decoder refuses everything else:

- a tag longer than five bytes, or of 2^32 or more;
- field number 0;
- wire types 3 and 4, which are groups;
- wire types 6 and 7, which do not exist;
- a length longer than five bytes, of 2^31 - 16 or more, or running past the end of the input;
- any record cut short.

Groups are deprecated in the guide and outside this first slice.

The two reference parsers differ in three places, and this library takes the stricter reading in each:

- upb reads field number 0, which the C++ parser refuses. The encoding guide does not forbid field number 0, but the language guide's field numbers start at 1.
- The C++ parser reads a five-byte tag of 2^32 or more by dropping its high bits, which upb refuses.
- upb reads a `LEN` length up to 2^31 - 1, while the C++ parser refuses one of 2^31 - 16 or more. The encoding guide says a message must be smaller than 2 GiB.

`Field.isValid` says which fields the encoder can write:

- a field number from 1 to 2^29 - 1;
- a `VARINT` or `I64` value below 2^64;
- an `I32` value below 2^32;
- `LEN` bytes shorter than 2^31 - 16.

`encode` and `Varint.encode` are specified only for valid fields and for numbers below 2^64. For anything else they write bytes that do not read back as what was given, so a program checks `Field.isValid` first, as the command-line tool does.

## Messages

`encode` writes each field in turn: the shortest varint for its tag, then its payload, with any varint in its shortest form.

`decode` reads records until the input ends and returns the fields in order. A field number may repeat, and the order is kept. The empty input is the empty message. If any record is malformed, the whole input is refused. `decode` never returns part of a message. Each length check looks at no more of the input than the field needs, so decoding takes time in proportion to the input's length.

## The command-line tool

`protowire serve`, in `Main.lean`, answers requests from the differential tests, one per line. Its header comment gives the protocol. Every answer comes from `decode`, `encode` and `Field.isValid`.

## What must always hold

Each property is a theorem in `Protobuf/Spec.lean`, under the name given. The definitions the statements use are in `Protobuf/Spec/Defs.lean`. They are written from the encoding guide and checked against its worked bytes.

| Property | Theorem |
|----------|---------|
| For numbers below 2^64, the encoder writes the shortest varint. | `Protobuf.Spec.varint_encode_eq` |
| The varint decoder reads exactly one varint of up to ten bytes from the front of its input, keeps the rest untouched, and refuses everything else. | `Protobuf.Spec.varint_decode_iff` |
| For numbers below 2^64, decoding a varint the encoder wrote gives the number back. | `Protobuf.Spec.varint_decode_encode` |
| `isValid` decides exactly which fields can be written. | `Protobuf.Spec.isValid_iff` |
| For valid fields, the encoder writes each field as the guide describes. | `Protobuf.Spec.encode_eq` |
| `decode` returns a field list exactly when the bytes split into records, one per field, in order, by the rules above. | `Protobuf.Spec.decode_iff` |
| For valid fields, decoding what the encoder wrote gives the fields back. | `Protobuf.Spec.decode_encode` |
| Every field the decoder returns can be written again. | `Protobuf.Spec.decode_valid` |
| The guide's worked bytes: 1, 150 and -2 as varints, and its messages `Test1` to `Test4`. | `Protobuf.Spec.guide_vectors` |
| 2^64 - 1 is ten bytes, fixed-width values are little-endian, varints need not be in shortest form, ten-byte varints drop bits past the 64th, the largest field number reads, and so does the empty message. | `Protobuf.Spec.edge_vectors` |
| The decoder refuses each kind of malformed input listed above, except a length of 2^31 - 16 or more, which needs a 2 GiB input; `Protobuf.Spec.decode_iff` covers it. | `Protobuf.Spec.reject_vectors` |

Together, these fix every output.

- `decode` is fixed for every input.
- `encode` and `Varint.encode` are fixed for every valid input.
- A decoder that accepted nothing would meet `Protobuf.Spec.decode_valid`, but it would fail `Protobuf.Spec.decode_iff` and `Protobuf.Spec.decode_encode`.
- `encode` is not fixed for fields that are not valid.
- A decoder that accepted too much would fail `Protobuf.Spec.decode_iff`.

## Oracle

Google's Protobuf parsers, compared on every input:

- upb, through Python's `protobuf` package, reading each message as `google.protobuf.Empty` so that every field is kept as an unknown field;
- the C++ parser behind `protoc --decode_raw`, run in-process through `grpcio-tools`.

The encoder is compared with `google.protobuf.internal.encoder`.
