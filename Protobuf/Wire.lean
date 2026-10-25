/-
  Fields and messages on the wire.
-/

import Protobuf.Types
import Protobuf.Varint

namespace Protobuf

/-! ## Encoding -/

/-- The low `k` bytes of `n`, least significant first. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: leBytes k (n / 256)

def Value.wireType : Value → Nat
  | .varint _ => 0
  | .i64 _ => 1
  | .len _ => 2
  | .i32 _ => 5

def Value.encode : Value → List UInt8
  | .varint v => Varint.encode v
  | .i64 v => leBytes 8 v
  | .len d => Varint.encode d.length ++ d
  | .i32 v => leBytes 4 v

/-- The tag, a varint of the field number and the wire type, then the
    value. -/
def Field.encode (f : Field) : List UInt8 :=
  Varint.encode (f.number * 8 + f.value.wireType) ++ f.value.encode

/-- A message: its fields, one after another, in order. -/
def encode (fs : List Field) : List UInt8 :=
  fs.flatMap Field.encode

/-- Whether the field can be written: a field number from 1 to
    2^29 - 1, values that fit their wire type, and bytes shorter than
    2^31. -/
def Field.isValid (f : Field) : Bool :=
  1 ≤ f.number && f.number < 2 ^ 29 &&
  match f.value with
  | .varint v => v < 2 ^ 64
  | .i64 v => v < 2 ^ 64
  | .len d => d.length < 2 ^ 31
  | .i32 v => v < 2 ^ 32

/-! ## Decoding -/

/-- Bytes read as a number, least significant first. -/
def leValue (bs : List UInt8) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- Reads one field from the front of the input: the field, and the
    bytes after it. -/
def decodeField (bs : List UInt8) : Option (Field × List UInt8) :=
  match Varint.decodeAux 5 bs with
  | none => none
  | some (t, rest) =>
    if 2 ^ 32 ≤ t ∨ t / 8 = 0 then none
    else
      let n := t / 8
      match t % 8 with
      | 0 =>
        match Varint.decode rest with
        | some (v, rest) => some (⟨n, .varint v⟩, rest)
        | none => none
      | 1 => if rest.length < 8 then none else some (⟨n, .i64 (leValue (rest.take 8))⟩, rest.drop 8)
      | 2 =>
        match Varint.decodeAux 5 rest with
        | some (len, rest) =>
          if 2 ^ 31 ≤ len ∨ rest.length < len then none
          else some (⟨n, .len (rest.take len)⟩, rest.drop len)
        | none => none
      | 5 => if rest.length < 4 then none else some (⟨n, .i32 (leValue (rest.take 4))⟩, rest.drop 4)
      | _ => none

/-- Reads fields until the input ends. Each field takes at least one
    byte, so `fuel` equal to the input's length is enough. -/
def decodeAux : Nat → List UInt8 → Option (List Field)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b :: bs =>
    match decodeField (b :: bs) with
    | some (f, rest) =>
      match decodeAux fuel rest with
      | some fs => some (f :: fs)
      | none => none
    | none => none

/-- Reads a whole message. Fails on anything that is not a sequence of
    well-formed fields, including input that ends inside a field. -/
def decode (bs : List UInt8) : Option (List Field) :=
  decodeAux bs.length bs

end Protobuf
