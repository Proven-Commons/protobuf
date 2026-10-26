/-
  The definitions the specification uses, written from the Protobuf
  encoding guide (https://protobuf.dev/programming-guides/encoding/)
  independently of the code in `Protobuf/`. Part of the approved
  specification, with `Spec.lean` and `Protobuf/Types.lean`.

  Both the challenge file and the proofs import this file, so each
  statement means the same thing on both sides. The `example`s check the
  definitions against the guide's worked bytes.
-/

import Protobuf

open Protobuf

/-! ## Varints

"Each byte in the varint has a continuation bit that indicates if the
byte that follows it is part of the varint. This is the most significant
bit (MSB) of the byte. The lower 7 bits of each byte are used to store
the two's complement representation of the number in groups of 7 bits,
least significant group first." Varints carry unsigned 64-bit values in
one to ten bytes. -/

/-- The number the low seven bits of each byte make, least significant
    group first. -/
def Spec.groupsValue (bs : List UInt8) : Nat :=
  ((List.range bs.length).map fun i => (bs.getD i 0).toNat % 128 * 128 ^ i).sum

/-- The shape of a varint of at most `k` bytes: at least one byte, every
    byte but the last with its high bit set, the last without it. -/
def Spec.VarintShape (k : Nat) (bs : List UInt8) : Prop :=
  bs ≠ [] ∧ bs.length ≤ k ∧
    (∀ b ∈ bs.dropLast, 128 ≤ b.toNat) ∧ (∀ b ∈ bs.getLast?, b.toNat < 128)

/-- `bs` is a varint for `v`. The reference parsers read up to ten
    bytes and drop any bits above the 64th, so a value is its groups
    modulo 2^64. A varint need not be in its shortest form: the
    reference parsers read `80 00` as 0. -/
def Spec.IsVarint (bs : List UInt8) (v : Nat) : Prop :=
  Spec.VarintShape 10 bs ∧ v = Spec.groupsValue bs % 2 ^ 64

/-- The shortest varint for `n`, as an encoder writes it: seven bits at
    a time, least significant first, with the high bit set on every
    byte but the last. `fuel` bounds the number of bytes; `n + 1` is
    always enough. -/
def Spec.varintAux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n =>
    if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: Spec.varintAux fuel (n / 128)

def Spec.varint (n : Nat) : List UInt8 := Spec.varintAux (n + 1) n

-- The guide's examples: 1 is `01`, and 150 is `96 01`.
example : Spec.varint 1 = [0x01] := by decide
example : Spec.varint 150 = [0x96, 0x01] := by decide
example : Spec.groupsValue [0x96, 0x01] = 150 := by decide
example : Spec.VarintShape 10 [0x96, 0x01] := by unfold Spec.VarintShape; decide

/-! ## Fixed-width values

"Non-varint numeric types are simple. `double` and `fixed64` have wire
type `I64`, which tells the parser to expect a fixed eight-byte lump of
data. ... Similarly `float` and `fixed32` have wire type `I32`, which
tells it to expect four bytes instead." The bytes are little-endian. -/

/-- The bytes read as a number, least significant first. -/
def Spec.leValue (bs : List UInt8) : Nat :=
  ((List.range bs.length).map fun i => (bs.getD i 0).toNat * 256 ^ i).sum

/-- `n` in `k` bytes, least significant first. -/
def Spec.leBytes (k n : Nat) : List UInt8 :=
  (List.range k).map fun i => (n / 256 ^ i % 256).toUInt8

example : Spec.leValue [0x01, 0x02, 0x03, 0x04] = 0x04030201 := by decide
example : Spec.leBytes 4 0x04030201 = [0x01, 0x02, 0x03, 0x04] := by decide

/-! ## Fields and messages

"A protocol buffer message is a series of key-value pairs." Each record
is a tag, then its payload. "The 'tag' of a record is encoded as a
varint formed from the field number and the wire type via the formula
`(field_number << 3) | wire_type`." The wire types are 0 `VARINT`,
1 `I64`, 2 `LEN`, 3 `SGROUP`, 4 `EGROUP` and 5 `I32`. "The `LEN` wire
type has a dynamic length, specified by a varint immediately after the
tag, which is followed by the payload as usual."

The language guide gives field numbers from 1 to 2^29 - 1, and the
encoding guide says "Protos must be smaller than 2 GiB when serialized".
Both reference parsers read a tag or a length as a varint of at most
five bytes. Where they disagree, this specification takes the stricter
reading: upb reads field number 0 and the C++ parser refuses it; the C++
parser reads a tag of 2^32 or more by dropping its high bits and upb
refuses it; upb reads a length up to 2^31 - 1 and the C++ parser refuses
one of 2^31 - 16 or more. Groups, wire types 3 and 4, are deprecated and
outside this library; wire types 6 and 7 do not exist. -/

/-- A field the encoder can write: a field number from 1 to 2^29 - 1,
    and a value that fits its wire type, with bytes the C++ parser
    reads. -/
def Spec.ValidField (f : Field) : Prop :=
  1 ≤ f.number ∧ f.number < 2 ^ 29 ∧
  match f.value with
  | .varint v => v < 2 ^ 64
  | .i64 v => v < 2 ^ 64
  | .len d => d.length < 2 ^ 31 - 16
  | .i32 v => v < 2 ^ 32

/-- `tag` then `payload` are the bytes of field `f`. -/
def Spec.FieldBytes (tag payload : List UInt8) (f : Field) : Prop :=
  Spec.VarintShape 5 tag ∧ Spec.groupsValue tag < 2 ^ 32 ∧
  f.number = Spec.groupsValue tag / 8 ∧ 1 ≤ f.number ∧
  match Spec.groupsValue tag % 8, f.value with
  | 0, .varint v => Spec.IsVarint payload v
  | 1, .i64 v => payload.length = 8 ∧ v = Spec.leValue payload
  | 2, .len d =>
    ∃ pre, payload = pre ++ d ∧ Spec.VarintShape 5 pre ∧ Spec.groupsValue pre = d.length ∧
      d.length < 2 ^ 31 - 16
  | 5, .i32 v => payload.length = 4 ∧ v = Spec.leValue payload
  | _, _ => False

/-- `bs` is a message whose fields, in order, are `fs`: the bytes split
    into records, one per field. -/
inductive Spec.Message : List UInt8 → List Field → Prop where
  | nil : Spec.Message [] []
  | cons {tag payload rest : List UInt8} {f : Field} {fs : List Field} :
      Spec.FieldBytes tag payload f → Spec.Message rest fs →
      Spec.Message (tag ++ payload ++ rest) (f :: fs)

/-- The bytes an encoder writes for a field: the shortest varint for
    the tag, then the payload, with any varint in its shortest form. -/
def Spec.fieldBytes (f : Field) : List UInt8 :=
  match f.value with
  | .varint v => Spec.varint (f.number * 8 + 0) ++ Spec.varint v
  | .i64 v => Spec.varint (f.number * 8 + 1) ++ Spec.leBytes 8 v
  | .len d => Spec.varint (f.number * 8 + 2) ++ Spec.varint d.length ++ d
  | .i32 v => Spec.varint (f.number * 8 + 5) ++ Spec.leBytes 4 v

/-- The bytes an encoder writes for a message: its fields in order. -/
def Spec.encode (fs : List Field) : List UInt8 :=
  (fs.map Spec.fieldBytes).flatten

-- The guide's examples: field 1 set to 150 is `08 96 01`, field 2 set
-- to "testing" is `12 07 74 65 73 74 69 6e 67`, and field 3 holding the
-- first message is `1a 03 08 96 01`.
example : Spec.encode [⟨1, .varint 150⟩] = [0x08, 0x96, 0x01] := by decide
example : Spec.encode [⟨2, .len [0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]⟩] =
    [0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67] := by decide
example : Spec.encode [⟨3, .len [0x08, 0x96, 0x01]⟩] = [0x1a, 0x03, 0x08, 0x96, 0x01] := by decide
example : Spec.FieldBytes [0x08] [0x96, 0x01] ⟨1, .varint 150⟩ := by
  refine ⟨by unfold Spec.VarintShape; decide, by decide, by decide, by decide, ?_⟩
  show Spec.IsVarint [0x96, 0x01] 150
  exact ⟨by unfold Spec.VarintShape; decide, by decide⟩
