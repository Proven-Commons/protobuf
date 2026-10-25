# Protobuf wire format codec: specification

This is the specification of the first slice for the `protobuf`
package: the Protobuf wire format at the level of bytes, in Lean,
with the round trips proved.

What the slice is: a varint codec, field tags, and messages made
of fields with raw values, for the four wire types the format
uses today (0, 1, 2, 5). What it is not: anything about `.proto`
schema files, message meanings, or the types a schema assigns to
a field. A field here is a number and raw bytes or a raw number,
and nothing more.

## Varints

A varint encodes a natural number in base 128: seven bits at a
time, low group first, with the high bit of each byte set on
every byte but the last. The encoder writes the short form: no
leading zero groups, and the number 0 is the single byte 0.

The decoder reads one varint from the front of a byte list and
returns the value and the bytes after it. It rejects:

- a varint cut short by the end of the input (a byte with its
  high bit set and nothing after it),
- a varint longer than ten bytes,
- a varint whose value does not fit in 64 bits. Ten bytes carry
  seventy bit places; a ten byte varint whose last byte is 2 or
  more sets a bit past 64 and is rejected. The largest varint
  read is 18446744073709551615, ten bytes ending in the byte 1.

Longer than needed encodings are read, up to those limits: a
value written with leading zero groups (the byte pairs 128, 0
for the number 0, say) decodes to the same value. Only the
encoder is held to the short form.

## Tags and wire types

Every field starts with a tag: a varint holding the field number
times eight plus the wire type. Field number zero is rejected.
The wire types:

| Type | Meaning | Value held here |
| --- | --- | --- |
| 0 | varint | a natural number below 2^64 |
| 1 | 64 bit | eight bytes, in wire order |
| 2 | length delimited | a length varint, then that many bytes |
| 5 | 32 bit | four bytes, in wire order |

Wire types 3 and 4 are group start and end markers. The format
has set them aside, and this slice rejects them. Wire types 6
and 7 are not wire types at all, and are rejected too.

The decoder puts no upper bound on the field number beyond what
the tag varint itself allows: a tag is a varint below 2^64, so
any field number the tag holds is read. The field list format
of the command line (below) binds a field number to the range
the Protobuf format allows for schemas, 1 to 536870911, because
that is the range the round trip claim covers. A number read off
the wire above that range is reported as read; the command line
will not write it back. That gap is stated again under "not
claimed".

## Messages

A message is a list of fields, written in list order, one field
after another with nothing between them. The decoder reads
fields until the input ends. It returns an error in place of
reading past the end of its input:

- a length that runs past the bytes left,
- a 64 bit or 32 bit value cut short,
- a tag or a value varint cut short,
- a field with number zero, or a wire type of 3, 4, 6, or 7,
  anywhere in the message. One bad field rejects the whole
  message; there is no partial reading.

Fixed width values are held as their wire bytes, low byte
first, and written back as they were read. Length delimited
values are held as byte strings; a packed repeated field is one
of those, and its contents are not looked inside at this level.

## The command line format

One request per line: an operation, one space, and a number
list. The empty line is passed over. A line of any other shape
prints `error`. A number in the list is plain decimal: no sign,
no leading zeros (0 itself is written `0`), at most twenty
digits, numbers parted by commas with no spaces.

- `venc` takes one number, below 2^64, and prints its varint
  bytes as a comma parted number list.
- `vdec` takes byte numbers (each at most 255) and prints `ok:`
  and the value when the bytes are exactly one varint this
  slice reads, and `none` when they are not.
- `enc` takes a field list (below) and prints the message bytes
  as a comma parted number list.
- `dec` takes byte numbers and prints `ok:` and the field list
  when the bytes are a message this slice reads, and `none`
  when they are not.

`none` and `error` mean different things: `none` is a well
formed request whose bytes are rejected; `error` is a request
that breaks the line rules or the field list rules.

The field list format reads the numbers as groups, one group
per field, in field order. A group is: the field number, the
wire type, then the payload.

- Wire type 0: one number, the varint value, below 2^64.
- Wire type 1: eight byte numbers.
- Wire type 2: a length number, below 2^64, then that many byte
  numbers.
- Wire type 5: four byte numbers.

The empty field list is the empty number list, so `enc ` with an
empty list prints an empty line (the empty message), and `dec `
of no bytes prints `ok:` with nothing after it. Field numbers
run from 1 to 536870911. A group that breaks any rule (a field
number of 0 or above the range, a wire type outside 0, 1, 2, 5,
a byte number above 255, a value or length at or above 2^64, or
numbers that run out in the middle of a group) makes the whole
request malformed, and the answer is `error`.

## The claims

A field is *well formed* when its number is between 1 and
536870911 and its value is in shape: a varint value below 2^64,
a 64 bit value of eight bytes, a 32 bit value of four bytes, or
a length delimited value whose length is below 2^64. A message
is well formed when all of its fields are.

Over well formed input, the following are proved (in
`Proofs/RoundTrip.lean`, names in the `Protobuf.Proofs`
namespace):

1. **Varint round trip** (`decodeVarint_encode`, with the
   appended form `decodeVarint_encode_append`): for `n` below
   2^64, decoding the encoding of `n` gives `n` back, with no
   leftover, and bytes after the encoding are left alone.
2. **Message round trip** (`decodeMessage_encode`, by way of
   `parseField_encode`): decoding the encoding of a well formed
   field list gives the same field list back.
3. **Worked examples** (`Proofs/Examples.lean`): the byte
   examples from the Protobuf encoding documentation (varint 1,
   varint 300, varint 150, field 1 holding varint 150, field 2
   holding the text "testing"), the largest 64 bit varint, and
   the rejections at this level (a bit past 64, eleven bytes,
   field number zero, a group tag, a length past the end), each
   proved.

The printed spec file of the verified bar (a `Spec.lean` whose
statements a checker compares against these) is a reviewer step
that has not been taken yet, so the statements above are the
claims as proved in `Proofs`, in prose form here.

## Not claimed

- No round trip for arbitrary byte strings. A message read off
  the wire and written back need not give the same bytes: a
  varint may have been written long, and a field number above
  536870911, which the decoder reads, cannot be written by the
  command line format at all.
- No claim about which byte strings are accepted, beyond the
  tests. The accept and reject rules above are what the code
  does; the proofs cover the round trips, and the differential
  tests cover the readings.
- Nothing about schemas or meanings: no `.proto` files, no field
  names or types, no signed or zigzag readings of a varint, no
  packed field contents, no maps, no unknown field policy.
- Groups are rejected, not read.
- No streaming: a message is read from a whole byte list in
  memory, and nothing here writes to disk.
