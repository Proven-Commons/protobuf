/-
  The Protobuf wire format, at the level of bytes: varints, field
  tags, and the four wire types this slice carries.

  A message is a list of fields. Each field holds a field number
  and a raw value: a varint number, eight bytes, a length delimited
  byte string, or four bytes. No meaning is attached to a field
  here. Meanings live in `.proto` schema files, which sit outside
  this slice.

  Rules the decoder follows:

  - A varint is at most ten bytes. A varint cut short by the end of
    the input is rejected, a varint that runs past ten bytes is
    rejected, and a varint whose value does not fit in 64 bits is
    rejected.
  - A field tag is a varint that holds the field number times
    eight, plus the wire type. A field number of zero is rejected.
  - Wire types 0, 1, 2, and 5 are read. Wire types 3 and 4 are
    group markers, which the format has set aside, and 6 and 7 are
    not wire types at all. All four are rejected.
  - A length delimited value whose length runs past the bytes left
    is rejected, and so is a fixed width value cut short. The
    decoder returns an error in place of reading past the end of
    its input.

  The encoding of a value never depends on a schema, so a packed
  repeated field is simply a length delimited byte string at this
  level, like any other.
-/

namespace Protobuf

/-- A raw field value, as the wire carries it. A `fixed64` value
    holds its eight bytes in wire order, low byte first, and a
    `fixed32` value holds its four bytes the same way. -/
inductive Value where
  | varint (n : Nat)
  | fixed64 (bs : List UInt8)
  | bytes (bs : List UInt8)
  | fixed32 (bs : List UInt8)
  deriving DecidableEq, Repr

/-- One field: a field number and a raw value. -/
structure Field where
  num : Nat
  value : Value
  deriving DecidableEq, Repr

/-- The wire type number of a value: 0 for a varint, 1 for 64 bit,
    2 for length delimited, 5 for 32 bit. -/
def wireType : Value → Nat
  | .varint _ => 0
  | .fixed64 _ => 1
  | .bytes _ => 2
  | .fixed32 _ => 5

/-! ## Varints -/

/-- Encode a natural number as a base 128 varint: seven bits at a
    time, low group first, with the high bit of each byte set on
    every byte but the last. The encoding is the short one: no
    leading zero groups. -/
def encodeVarint (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8]
  else (n % 128 + 128).toUInt8 :: encodeVarint (n / 128)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The unfolding rule for `encodeVarint`. -/
theorem encodeVarint_def (n : Nat) :
    encodeVarint n =
      if n < 128 then [n.toUInt8]
      else (n % 128 + 128).toUInt8 :: encodeVarint (n / 128) := by
  rw [encodeVarint]

/-- Read a varint from the front of a byte list, with at most
    `fuel` bytes. Returns the value and the bytes after it. A list
    that ends while a byte still asks for one more gives `none`,
    and so does a list whose varint needs more than `fuel` bytes. -/
def decodeVarintGo : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: rest =>
    if b < 128 then some (b.toNat, rest)
    else (decodeVarintGo fuel rest).map fun (v, r) => (b.toNat - 128 + 128 * v, r)

/-- The unfolding rule for `decodeVarintGo` on a list with a head
    byte. -/
theorem decodeVarintGo_cons (fuel : Nat) (b : UInt8) (rest : List UInt8) :
    decodeVarintGo (fuel + 1) (b :: rest) =
      if b < 128 then some (b.toNat, rest)
      else (decodeVarintGo fuel rest).map fun (v, r) => (b.toNat - 128 + 128 * v, r) := by
  rw [decodeVarintGo]

/-- Read one varint from the front of a byte list: at most ten
    bytes, and a value that fits in 64 bits. Returns the value and
    the bytes after it, or `none` when the bytes hold no such
    varint at the front. -/
def decodeVarint (bs : List UInt8) : Option (Nat × List UInt8) :=
  (decodeVarintGo 10 bs).bind fun (v, rest) =>
    if v < 18446744073709551616 then some (v, rest) else none

/-! ## Fields and messages -/

/-- Encode one field value, without its tag. A length delimited
    value writes its length as a varint, then its bytes. -/
def encodeValue : Value → List UInt8
  | .varint n => encodeVarint n
  | .fixed64 bs => bs
  | .bytes bs => encodeVarint bs.length ++ bs
  | .fixed32 bs => bs

/-- Encode one field: its tag as a varint, then its value. The tag
    holds the field number times eight, plus the wire type. -/
def encodeField (f : Field) : List UInt8 :=
  encodeVarint (f.num * 8 + wireType f.value) ++ encodeValue f.value

/-- Encode a message: the fields in list order, one after the
    other, with nothing between them. -/
def encodeMessage (fs : List Field) : List UInt8 :=
  fs.flatMap encodeField

/-- Read one field from the front of a byte list. Returns the field
    and the bytes after it, or `none` when the front of the list
    holds no field this slice reads. -/
def parseField (bs : List UInt8) : Option (Field × List UInt8) :=
  match decodeVarint bs with
  | none => none
  | some (tag, rest1) =>
    let num := tag / 8
    let wt := tag % 8
    if num = 0 then none
    else if wt = 0 then
      (decodeVarint rest1).map fun (v, r) => (⟨num, .varint v⟩, r)
    else if wt = 1 then
      if 8 ≤ rest1.length then
        some (⟨num, .fixed64 (rest1.take 8)⟩, rest1.drop 8)
      else none
    else if wt = 2 then
      match decodeVarint rest1 with
      | none => none
      | some (len, rest2) =>
        if len ≤ rest2.length then
          some (⟨num, .bytes (rest2.take len)⟩, rest2.drop len)
        else none
    else if wt = 5 then
      if 4 ≤ rest1.length then
        some (⟨num, .fixed32 (rest1.take 4)⟩, rest1.drop 4)
      else none
    else none

/-- Read fields until the byte list ends. The fuel count bounds
    the fields read: each field takes at least one byte, so the
    length of the input is always fuel enough. A byte list that
    ends in the middle of a field gives `none`. -/
def parseFields : Nat → List UInt8 → Option (List Field)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs =>
    match parseField bs with
    | some (f, rest) => (parseFields fuel rest).map (f :: ·)
    | none => none

/-- The unfolding rule for `parseFields` on an empty byte list. -/
theorem parseFields_nil (fuel : Nat) : parseFields fuel [] = some [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => rfl

/-- Read a whole message: fields until the input ends, with
    nothing left over. -/
def decodeMessage (bs : List UInt8) : Option (List Field) :=
  parseFields bs.length bs

/-! ## Well formed fields

  The round trip claims in `Proofs` hold for well formed fields.
  A varint value fits in 64 bits, a fixed width value holds the
  right count of bytes, and a field number sits in the range the
  Protobuf format allows, from 1 to 536870911. A length delimited
  value asks only that its length fits in 64 bits, which any list
  a program can hold does in practice, but the proof needs the
  bound stated. -/

/-- A value in the shape the encoder and the round trip proofs
    rely on. -/
inductive WFValue : Value → Prop
  | varint {n : Nat} (h : n < 18446744073709551616) : WFValue (.varint n)
  | fixed64 {bs : List UInt8} (h : bs.length = 8) : WFValue (.fixed64 bs)
  | bytes {bs : List UInt8} (h : bs.length < 18446744073709551616) : WFValue (.bytes bs)
  | fixed32 {bs : List UInt8} (h : bs.length = 4) : WFValue (.fixed32 bs)

/-- A field with a number in range and a well formed value. -/
def WFField (f : Field) : Prop :=
  0 < f.num ∧ f.num < 536870912 ∧ WFValue f.value

/-- A message whose fields are all well formed. -/
def WFMessage (fs : List Field) : Prop :=
  ∀ f ∈ fs, WFField f

end Protobuf
