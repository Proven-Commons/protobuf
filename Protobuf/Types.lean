/-
  What a message is on the wire: a list of fields, each a field number
  and a raw value of one of four wire types. Part of the approved
  specification, with `Protobuf/Spec.lean` and `Protobuf/Spec/Defs.lean`, since every
  statement is about these types.

  Which values are in range is `Protobuf.Spec.ValidField`, in `Protobuf/Spec/Defs.lean`.
-/

namespace Protobuf

/-- A field's value as the wire carries it, before any schema gives it
    a meaning. Groups (wire types 3 and 4) are outside this library. -/
inductive Value where
  /-- Wire type 0, `VARINT`: an unsigned value below 2^64. -/
  | varint (v : Nat)
  /-- Wire type 1, `I64`: eight bytes, read as an unsigned value. -/
  | i64 (v : Nat)
  /-- Wire type 2, `LEN`: a length, then that many bytes. -/
  | len (bytes : List UInt8)
  /-- Wire type 5, `I32`: four bytes, read as an unsigned value. -/
  | i32 (v : Nat)
  deriving DecidableEq, Repr

/-- One field of a message: its field number and its value. A message
    may repeat a field number; the order of fields is kept. -/
structure Field where
  number : Nat
  value : Value
  deriving DecidableEq, Repr

end Protobuf
