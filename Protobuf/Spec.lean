/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Protobuf/Proofs.lean`, under
  the same names; `lake comparator` checks that each one proves exactly
  the statement written here. The `sorry`s below are expected in this
  file only.

  The definitions the statements use, written from the Protobuf encoding
  guide, are in `Protobuf/Spec/Defs.lean`, and the types in `Protobuf/Types.lean`.
  Both are part of the specification too.
-/

import Protobuf
import Protobuf.Spec.Defs

open Protobuf

/-! ## Varints -/

/-- The encoder writes the shortest varint. -/
theorem Protobuf.Spec.varint_encode_eq (n : Nat) (h : n < 2 ^ 64) : Varint.encode n = Protobuf.Spec.varint n := sorry

/-- The decoder reads exactly one varint from the front of its input:
    up to ten bytes, the last without its high bit, and returns its
    value and the rest of the input untouched. Anything else, including
    input that ends inside the varint and an eleventh byte, is
    refused. -/
theorem Protobuf.Spec.varint_decode_iff (bs : List UInt8) (v : Nat) (rest : List UInt8) :
    Varint.decode bs = some (v, rest) ↔ ∃ pre, bs = pre ++ rest ∧ Protobuf.Spec.IsVarint pre v := sorry

/-- Round trip: decoding what the encoder wrote gives the number back,
    and leaves what follows untouched. -/
theorem Protobuf.Spec.varint_decode_encode (n : Nat) (rest : List UInt8) (h : n < 2 ^ 64) :
    Varint.decode (Varint.encode n ++ rest) = some (n, rest) := sorry

/-! ## Messages -/

/-- `isValid` decides exactly which fields can be written. -/
theorem Protobuf.Spec.isValid_iff (f : Field) : f.isValid = true ↔ Protobuf.Spec.ValidField f := sorry

/-- The encoder writes each field as the encoding guide describes, with
    every varint in its shortest form. -/
theorem Protobuf.Spec.encode_eq (fs : List Field) (h : ∀ f ∈ fs, Protobuf.Spec.ValidField f) :
    Protobuf.encode fs = Protobuf.Spec.encode fs := sorry

/-- `decode` returns `fs` exactly when the bytes split into records, one
    per field of `fs`, in order, by the rules of `Protobuf.Spec.FieldBytes`. So it
    reads every message made of `VARINT`, `I64`, `LEN` and `I32` records
    with field numbers from 1 to 2^29 - 1, refuses everything else (a
    record cut short, a length past the end, field number 0, a group, an
    unknown wire type, an oversized tag or length), and returns the
    fields as written. -/
theorem Protobuf.Spec.decode_iff (bs : List UInt8) (fs : List Field) :
    decode bs = some fs ↔ Protobuf.Spec.Message bs fs := sorry

/-- Round trip: decoding what the encoder wrote gives the fields back. -/
theorem Protobuf.Spec.decode_encode (fs : List Field) (h : ∀ f ∈ fs, Protobuf.Spec.ValidField f) :
    decode (Protobuf.encode fs) = some fs := sorry

/-- Every field the decoder returns can be written again. -/
theorem Protobuf.Spec.decode_valid (bs : List UInt8) (fs : List Field) (h : decode bs = some fs) :
    ∀ f ∈ fs, Protobuf.Spec.ValidField f := sorry

/-! ## Test vectors -/

/-- The encoding guide's worked bytes: 1 and 150 as varints, -2 as a
    ten-byte varint (2^64 - 2 unsigned), and the messages `Test1` with
    field 1 set to 150, `Test2` with field 2 set to "testing", `Test3`
    holding the first message in field 3, and `Test4` with field 4 set
    to "hello" and field 5 packed with 1, 2 and 3. -/
theorem Protobuf.Spec.guide_vectors :
    Varint.encode 1 = [0x01] ∧
    Varint.encode 150 = [0x96, 0x01] ∧
    Varint.encode (2 ^ 64 - 2) = [0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01] ∧
    decode [0x08, 0x96, 0x01] = some [⟨1, .varint 150⟩] ∧
    decode [0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67] =
      some [⟨2, .len [0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]⟩] ∧
    decode [0x1a, 0x03, 0x08, 0x96, 0x01] = some [⟨3, .len [0x08, 0x96, 0x01]⟩] ∧
    decode [0x22, 0x05, 0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x2a, 0x03, 0x01, 0x02, 0x03] =
      some [⟨4, .len [0x68, 0x65, 0x6c, 0x6c, 0x6f]⟩, ⟨5, .len [0x01, 0x02, 0x03]⟩] ∧
    Protobuf.encode [⟨1, .varint 150⟩, ⟨2, .len [0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]⟩] =
      [0x08, 0x96, 0x01, 0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67] := sorry

/-- Cases the guide does not work through: the largest 64-bit value is
    ten bytes; fixed-width values are little-endian; the reference
    parsers' readings of unusual varints, not in shortest form, and ten
    bytes with bits past the 64th; the largest field number; and the
    empty message. -/
theorem Protobuf.Spec.edge_vectors :
    Varint.encode (2 ^ 64 - 1) = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01] ∧
    decode [0x0d, 0x01, 0x02, 0x03, 0x04] = some [⟨1, .i32 0x04030201⟩] ∧
    decode [0x09, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08] =
      some [⟨1, .i64 0x0807060504030201⟩] ∧
    decode [0x08, 0x80, 0x00] = some [⟨1, .varint 0⟩] ∧
    decode [0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f] =
      some [⟨1, .varint (2 ^ 64 - 1)⟩] ∧
    decode [0xf8, 0xff, 0xff, 0xff, 0x0f, 0x01] = some [⟨2 ^ 29 - 1, .varint 1⟩] ∧
    decode [] = some [] := sorry

/-- Input the decoder refuses: a varint cut short, an eleventh varint
    byte, field number 0, a length past the end, fixed-width values cut
    short, a group start and a group end, wire types 6 and 7, a tag of
    2^32 or more (from exactly 2^32, which would be field number 2^29),
    and a tag or length longer than five bytes. -/
theorem Protobuf.Spec.reject_vectors :
    decode [0x08] = none ∧
    decode [0x08, 0x80] = none ∧
    decode [0x08, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00] = none ∧
    decode [0x00, 0x00] = none ∧
    decode [0x0a, 0x04, 0x61, 0x62] = none ∧
    decode [0x0d, 0x01, 0x02, 0x03] = none ∧
    decode [0x09, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07] = none ∧
    decode [0x0b, 0x0c] = none ∧
    decode [0x0c] = none ∧
    decode [0x0e, 0x00] = none ∧
    decode [0x0f, 0x00] = none ∧
    decode [0xf8, 0xff, 0xff, 0xff, 0x1f, 0x01] = none ∧
    decode [0x80, 0x80, 0x80, 0x80, 0x10, 0x01] = none ∧
    decode [0x88, 0x80, 0x80, 0x80, 0x80, 0x00, 0x01] = none ∧
    decode [0x0a, 0x81, 0x80, 0x80, 0x80, 0x80, 0x00, 0x61] = none := sorry
