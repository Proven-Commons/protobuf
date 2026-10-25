/-
  The statements of `Spec.lean`, under the same names, from the lemmas
  in the other files of `Proofs/`. The test vectors are checked by
  evaluation.
-/

import Protobuf
import Spec.Defs
import Proofs.Varint
import Proofs.Message

open Protobuf
open Protobuf.Proofs

theorem Spec.varint_encode_eq (n : Nat) (h : n < 2 ^ 64) : Varint.encode n = Spec.varint n :=
  Protobuf.Proofs.Varint.encode_eq n h

theorem Spec.varint_decode_iff (bs : List UInt8) (v : Nat) (rest : List UInt8) :
    Varint.decode bs = some (v, rest) ↔ ∃ pre, bs = pre ++ rest ∧ Spec.IsVarint pre v :=
  Protobuf.Proofs.Varint.decode_iff bs v rest

theorem Spec.varint_decode_encode (n : Nat) (rest : List UInt8) (h : n < 2 ^ 64) :
    Varint.decode (Varint.encode n ++ rest) = some (n, rest) :=
  Protobuf.Proofs.Varint.decode_encode n rest h

theorem Spec.isValid_iff (f : Field) : f.isValid = true ↔ Spec.ValidField f :=
  Protobuf.Proofs.Message.isValid_iff f

theorem Spec.encode_eq (fs : List Field) (h : ∀ f ∈ fs, Spec.ValidField f) :
    Protobuf.encode fs = Spec.encode fs :=
  Protobuf.Proofs.Message.encode_eq fs h

theorem Spec.decode_iff (bs : List UInt8) (fs : List Field) :
    decode bs = some fs ↔ Spec.Message bs fs :=
  Protobuf.Proofs.Message.decode_iff bs fs

theorem Spec.decode_encode (fs : List Field) (h : ∀ f ∈ fs, Spec.ValidField f) :
    decode (Protobuf.encode fs) = some fs :=
  Protobuf.Proofs.Message.decode_encode fs h

theorem Spec.decode_valid (bs : List UInt8) (fs : List Field) (h : decode bs = some fs) :
    ∀ f ∈ fs, Spec.ValidField f :=
  Protobuf.Proofs.Message.decode_valid bs fs h

theorem Spec.guide_vectors :
    Varint.encode 1 = [0x01] ∧
    Varint.encode 150 = [0x96, 0x01] ∧
    Varint.encode (2 ^ 64 - 1) = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01] ∧
    decode [0x08, 0x96, 0x01] = some [⟨1, .varint 150⟩] ∧
    decode [0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67] =
      some [⟨2, .len [0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]⟩] ∧
    decode [0x1a, 0x03, 0x08, 0x96, 0x01] = some [⟨3, .len [0x08, 0x96, 0x01]⟩] ∧
    decode [0x22, 0x06, 0x03, 0x8e, 0x02, 0x9e, 0xa7, 0x05] =
      some [⟨4, .len [0x03, 0x8e, 0x02, 0x9e, 0xa7, 0x05]⟩] ∧
    Protobuf.encode [⟨1, .varint 150⟩, ⟨2, .len [0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67]⟩] =
      [0x08, 0x96, 0x01, 0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67] := by
  decide

theorem Spec.edge_vectors :
    decode [0x0d, 0x01, 0x02, 0x03, 0x04] = some [⟨1, .i32 0x04030201⟩] ∧
    decode [0x09, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08] =
      some [⟨1, .i64 0x0807060504030201⟩] ∧
    decode [0x08, 0x80, 0x00] = some [⟨1, .varint 0⟩] ∧
    decode [0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f] =
      some [⟨1, .varint (2 ^ 64 - 1)⟩] ∧
    decode [0xf8, 0xff, 0xff, 0xff, 0x0f, 0x01] = some [⟨2 ^ 29 - 1, .varint 1⟩] ∧
    decode [] = some [] := by
  decide

theorem Spec.reject_vectors :
    decode [0x08] = none ∧
    decode [0x08, 0x80] = none ∧
    decode [0x08, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00] = none ∧
    decode [0x00, 0x00] = none ∧
    decode [0x0a, 0x04, 0x61, 0x62] = none ∧
    decode [0x0d, 0x01, 0x02, 0x03] = none ∧
    decode [0x09, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07] = none ∧
    decode [0x0b, 0x0c] = none ∧
    decode [0x0e, 0x00] = none ∧
    decode [0x0f, 0x00] = none ∧
    decode [0xf8, 0xff, 0xff, 0xff, 0x1f, 0x01] = none ∧
    decode [0x88, 0x80, 0x80, 0x80, 0x80, 0x00, 0x01] = none ∧
    decode [0x0a, 0x81, 0x80, 0x80, 0x80, 0x80, 0x00, 0x61] = none := by
  decide
