/-
  Varints: unsigned numbers seven bits to a byte, least significant
  group first, with the high bit of each byte set when another byte
  follows.
-/

namespace Protobuf.Varint

/-- At most `fuel` bytes of the varint for `n`. -/
def encodeAux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n =>
    if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: encodeAux fuel (n / 128)

/-- The shortest varint for `n`. Ten bytes hold any value below 2^64. -/
def encode (n : Nat) : List UInt8 := encodeAux 10 n

/-- Reads a varint of at most `k` bytes from the front of the input: the
    number its groups make, and the bytes after it. Fails when the input
    ends first, or when byte `k` still has its high bit set. -/
def decodeAux : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else
      match decodeAux k bs with
      | some (v, rest) => some (b.toNat - 128 + 128 * v, rest)
      | none => none

/-- Reads a varint of up to ten bytes. Bits above the 64th are dropped,
    as the reference parsers drop them. -/
def decode (bs : List UInt8) : Option (Nat × List UInt8) :=
  match decodeAux 10 bs with
  | some (v, rest) => some (v % 2 ^ 64, rest)
  | none => none

end Protobuf.Varint
