/-
  The round trip proofs: decoding an encoding gives back what was
  encoded, first for one varint, then for one field, then for a
  whole message of well formed fields.

  The statements proved here are `decodeVarint_encode` and
  `decodeMessage_encode`. A matching statement in a spec file
  still has to be added by a reviewer, so this file builds on its
  own, in the same shape as the codec and json proofs.

  Helper lemmas live in `Protobuf.Proofs`.
-/

import Protobuf

namespace Protobuf.Proofs

open Protobuf

/-- An encoding of a varint always has at least one byte. -/
theorem encodeVarint_length_pos (n : Nat) : 0 < (encodeVarint n).length := by
  rw [encodeVarint_def]
  split <;> simp

/-- A number below `128 ^ (k + 1)` encodes in at most `k + 1`
    bytes. -/
theorem encodeVarint_length_le (k n : Nat) (hn : n < 128 ^ (k + 1)) :
    (encodeVarint n).length ≤ k + 1 := by
  induction k generalizing n with
  | zero =>
    have h : n < 128 := by simpa using hn
    rw [encodeVarint_def, if_pos h]
    simp
  | succ k ih =>
    rw [encodeVarint_def]
    by_cases h : n < 128
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp only [List.length_cons]
      have hpow : 128 ^ (k + 1 + 1) = 128 ^ (k + 1) * 128 := by rw [Nat.pow_succ]
      rw [hpow] at hn
      have hdiv : n / 128 < 128 ^ (k + 1) := by omega
      have hle := ih (n / 128) hdiv
      omega

/-- The varint reader, run with fuel at least the length of an
    encoding, reads that encoding whole and leaves the rest of the
    list alone. Induction on the fuel: each step eats one byte of
    the encoding and one unit of fuel. -/
theorem go_encode (fuel n : Nat) (rest : List UInt8)
    (h : (encodeVarint n).length ≤ fuel) :
    decodeVarintGo fuel (encodeVarint n ++ rest) = some (n, rest) := by
  induction fuel generalizing n rest with
  | zero =>
    have hpos := encodeVarint_length_pos n
    omega
  | succ fuel ih =>
    by_cases hn : n < 128
    · have henc : encodeVarint n = [n.toUInt8] := by
        rw [encodeVarint_def, if_pos hn]
      have h1 : (n.toUInt8).toNat = n :=
        UInt8.toNat_ofNat_of_lt (show n < 256 by omega)
      have hb : n.toUInt8 < 128 := by
        rw [UInt8.lt_iff_toNat_lt, h1]
        show n < 128
        exact hn
      rw [henc]
      show decodeVarintGo (fuel + 1) (n.toUInt8 :: rest) = some (n, rest)
      rw [decodeVarintGo_cons, if_pos hb, h1]
    · have henc : encodeVarint n =
          (n % 128 + 128).toUInt8 :: encodeVarint (n / 128) := by
        rw [encodeVarint_def, if_neg hn]
      have hlen : (encodeVarint (n / 128)).length ≤ fuel := by
        rw [henc] at h
        simp only [List.length_cons] at h
        omega
      have hc : ((n % 128 + 128).toUInt8).toNat = n % 128 + 128 :=
        UInt8.toNat_ofNat_of_lt
          (show n % 128 + 128 < 256 by
            have := Nat.mod_lt n (show 0 < 128 by decide); omega)
      have hnb : ¬ (n % 128 + 128).toUInt8 < 128 := by
        rw [UInt8.lt_iff_toNat_lt, hc]
        show ¬ (n % 128 + 128 < 128)
        have hmod := Nat.mod_lt n (show 0 < 128 by decide)
        omega
      rw [henc]
      show decodeVarintGo (fuel + 1)
          ((n % 128 + 128).toUInt8 :: (encodeVarint (n / 128) ++ rest)) =
        some (n, rest)
      rw [decodeVarintGo_cons, if_neg hnb, ih (n / 128) rest hlen, hc]
      simp [Nat.mod_add_div]

/-- Decoding an encoded varint, with more bytes after it, gives
    the number back and leaves the other bytes alone. -/
theorem decodeVarint_encode_append {n : Nat} (hn : n < 18446744073709551616)
    (rest : List UInt8) :
    decodeVarint (encodeVarint n ++ rest) = some (n, rest) := by
  have h70 : (128 : Nat) ^ (9 + 1) = 1180591620717411303424 := by decide
  have hlen : (encodeVarint n).length ≤ 10 := by
    have h1 : n < 128 ^ (9 + 1) := by omega
    exact encodeVarint_length_le 9 n h1
  unfold decodeVarint
  rw [go_encode 10 n rest hlen]
  simp [hn]

/-- Decoding an encoded varint gives the number back. -/
theorem decodeVarint_encode {n : Nat} (hn : n < 18446744073709551616) :
    decodeVarint (encodeVarint n) = some (n, []) := by
  have h := decodeVarint_encode_append hn ([] : List UInt8)
  simpa using h

/-- A wire type number is below eight, so a tag's low three bits
    hold the wire type and the rest holds the field number. -/
theorem wireType_lt (v : Value) : wireType v < 8 := by
  cases v <;> simp [wireType]

/-- Reading the encoding of a well formed field, with more bytes
    after it, gives the field back and leaves the other bytes
    alone. The tag decodes first: its value splits into the field
    number and the wire type, the number is not zero, and each
    value case then follows the varint and take and drop rules. -/
theorem parseField_encode {f : Field} (hf : WFField f) (rest : List UInt8) :
    parseField (encodeField f ++ rest) = some (f, rest) := by
  obtain ⟨num, value⟩ := f
  obtain ⟨hnum0, hnum29, hv⟩ := hf
  have hnum0' : 0 < num := hnum0
  have hnum29' : num < 536870912 := hnum29
  have hwt : wireType value < 8 := wireType_lt value
  have htag : num * 8 + wireType value < 18446744073709551616 := by omega
  have hdiv : (num * 8 + wireType value) / 8 = num := by omega
  have hmod : (num * 8 + wireType value) % 8 = wireType value := by omega
  have happ : encodeField ⟨num, value⟩ ++ rest =
      encodeVarint (num * 8 + wireType value) ++ (encodeValue value ++ rest) := by
    simp only [encodeField, List.append_assoc]
  have hdec := decodeVarint_encode_append htag (encodeValue value ++ rest)
  have hne : ¬ num = 0 := by omega
  cases value with
  | varint n =>
    cases hv with
    | varint hv64 =>
      rw [happ]
      unfold parseField
      rw [hdec]
      dsimp only
      have hwv : wireType (.varint n) = 0 := rfl
      rw [hdiv, hmod, if_neg hne, if_pos hwv]
      have hEv : encodeValue (.varint n) = encodeVarint n := rfl
      rw [hEv, decodeVarint_encode_append hv64 rest]
      rfl
  | fixed64 bs =>
    cases hv with
    | fixed64 hlen =>
      rw [happ]
      unfold parseField
      rw [hdec]
      dsimp only
      have hwv : wireType (.fixed64 bs) = 1 := rfl
      rw [hdiv, hmod, if_neg hne, if_neg (by omega : ¬ wireType (.fixed64 bs) = 0),
        if_pos hwv]
      have hEv : encodeValue (.fixed64 bs) = bs := rfl
      rw [hEv, if_pos (by simp [List.length_append, hlen] : 8 ≤ (bs ++ rest).length),
        List.take_left' hlen, List.drop_left' hlen]
  | bytes bs =>
    cases hv with
    | bytes hvlen =>
      rw [happ]
      unfold parseField
      rw [hdec]
      dsimp only
      have hwv : wireType (.bytes bs) = 2 := rfl
      rw [hdiv, hmod, if_neg hne, if_neg (by omega : ¬ wireType (.bytes bs) = 0),
        if_neg (by omega : ¬ wireType (.bytes bs) = 1), if_pos hwv]
      have hEv : encodeValue (.bytes bs) = encodeVarint bs.length ++ bs := rfl
      rw [hEv, List.append_assoc, decodeVarint_encode_append hvlen (bs ++ rest)]
      dsimp only
      rw [if_pos (by simp [List.length_append] : bs.length ≤ (bs ++ rest).length),
        List.take_left, List.drop_left]
  | fixed32 bs =>
    cases hv with
    | fixed32 hlen =>
      rw [happ]
      unfold parseField
      rw [hdec]
      dsimp only
      have hwv : wireType (.fixed32 bs) = 5 := rfl
      rw [hdiv, hmod, if_neg hne, if_neg (by omega : ¬ wireType (.fixed32 bs) = 0),
        if_neg (by omega : ¬ wireType (.fixed32 bs) = 1),
        if_neg (by omega : ¬ wireType (.fixed32 bs) = 2), if_pos hwv]
      have hEv : encodeValue (.fixed32 bs) = bs := rfl
      rw [hEv, if_pos (by simp [List.length_append, hlen] : 4 ≤ (bs ++ rest).length),
        List.take_left' hlen, List.drop_left' hlen]

/-- A field always encodes to at least one byte: its tag. -/
theorem encodeField_length_pos (f : Field) : 0 < (encodeField f).length := by
  have h := encodeVarint_length_pos (f.num * 8 + wireType f.value)
  simp only [encodeField, List.length_append]
  omega

/-- A message encoding is at least as long as its field count. -/
theorem encodeMessage_length : ∀ (fs : List Field),
    fs.length ≤ (encodeMessage fs).length := by
  intro fs
  induction fs with
  | nil => simp [encodeMessage]
  | cons f fs ih =>
    have h1 := encodeField_length_pos f
    have h2 : encodeMessage (f :: fs) = encodeField f ++ encodeMessage fs := rfl
    rw [h2, List.length_append, List.length_cons]
    omega

/-- One step of the field reader: on a byte list with a head byte,
    the reader reads one field and goes on with the rest. -/
theorem parseFields_step (fuel : Nat) (bs : List UInt8) (h : bs ≠ []) :
    parseFields (fuel + 1) bs =
      match parseField bs with
      | some (f, rest) => (parseFields fuel rest).map (f :: ·)
      | none => none := by
  cases bs with
  | nil => exact absurd rfl h
  | cons b rest => rfl

/-- Reading the encoding of a well formed message, with fuel at
    least the field count, gives the message back. Induction on
    the field list: the head field reads by `parseField_encode`,
    and the tail is shorter than the bytes it came from, so the
    fuel lasts. -/
theorem parseFields_encode : ∀ (fs : List Field), WFMessage fs →
    ∀ (fuel : Nat), fs.length ≤ fuel →
    parseFields fuel (encodeMessage fs) = some fs := by
  intro fs
  induction fs with
  | nil =>
    intro _ fuel _
    exact parseFields_nil fuel
  | cons f fs ih =>
    intro hwf fuel hf
    have hf' : WFField f := hwf f (by simp)
    have hfs : WFMessage fs := fun x hx => hwf x (List.mem_cons_of_mem f hx)
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hne : encodeMessage (f :: fs) ≠ [] := by
        have hlen := encodeMessage_length (f :: fs)
        simp only [List.length_cons] at hlen
        exact List.ne_nil_of_length_pos (by omega)
      have hcons : encodeMessage (f :: fs) = encodeField f ++ encodeMessage fs := rfl
      rw [parseFields_step fuel _ hne, hcons, parseField_encode hf' (encodeMessage fs)]
      dsimp only
      rw [ih hfs fuel (by simp at hf; omega)]
      rfl

/-- Decoding the encoding of a well formed message gives the
    message back. -/
theorem decodeMessage_encode {fs : List Field} (h : WFMessage fs) :
    decodeMessage (encodeMessage fs) = some fs :=
  parseFields_encode fs h _ (encodeMessage_length fs)

end Protobuf.Proofs
