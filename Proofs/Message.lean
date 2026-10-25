/-
  Fields and messages against the spec: `Field.isValid` decides
  `Spec.ValidField`, the encoder writes `Spec.encode`, `decodeField`
  reads exactly one record (`Spec.FieldBytes`) from the front of its
  input, `decode` reads exactly a `Spec.Message`, decoding what the
  encoder wrote gives the fields back, and every field the decoder
  returns is valid.
-/

import Protobuf
import Spec.Defs
import Proofs.Varint
import Proofs.Fixed

namespace Protobuf.Proofs.Message

open Protobuf

/-! ## Validity -/

theorem isValid_iff (f : Field) : f.isValid = true ↔ Spec.ValidField f := by
  obtain ⟨n, v⟩ := f
  cases v <;> simp [Field.isValid, Spec.ValidField, and_assoc]

/-! ## The encoder -/

theorem field_encode_eq (f : Field) (h : Spec.ValidField f) : f.encode = Spec.fieldBytes f := by
  obtain ⟨n, v⟩ := f
  obtain ⟨h1, h2, h3⟩ := h
  have h2 : n < 2 ^ 29 := h2
  have hn : ∀ w, w < 8 → n * 8 + w < 2 ^ 64 := by intro w hw; omega
  cases v with
  | varint v =>
    have h3 : v < 2 ^ 64 := h3
    show Varint.encode (n * 8 + 0) ++ Varint.encode v = Spec.varint (n * 8 + 0) ++ Spec.varint v
    rw [Proofs.Varint.encode_eq _ (hn 0 (by decide)), Proofs.Varint.encode_eq _ h3]
  | i64 v =>
    show Varint.encode (n * 8 + 1) ++ leBytes 8 v = Spec.varint (n * 8 + 1) ++ Spec.leBytes 8 v
    rw [Proofs.Varint.encode_eq _ (hn 1 (by decide)), Proofs.Fixed.leBytes_eq]
  | len d =>
    have h3 : d.length < 2 ^ 31 - 16 := h3
    show Varint.encode (n * 8 + 2) ++ (Varint.encode d.length ++ d) =
      Spec.varint (n * 8 + 2) ++ Spec.varint d.length ++ d
    rw [Proofs.Varint.encode_eq _ (hn 2 (by decide)), Proofs.Varint.encode_eq _ (by omega),
      List.append_assoc]
  | i32 v =>
    show Varint.encode (n * 8 + 5) ++ leBytes 4 v = Spec.varint (n * 8 + 5) ++ Spec.leBytes 4 v
    rw [Proofs.Varint.encode_eq _ (hn 5 (by decide)), Proofs.Fixed.leBytes_eq]

theorem encode_cons (f : Field) (fs : List Field) : encode (f :: fs) = f.encode ++ encode fs := by
  simp [encode]

theorem spec_encode_cons (f : Field) (fs : List Field) :
    Spec.encode (f :: fs) = Spec.fieldBytes f ++ Spec.encode fs := by
  simp [Spec.encode]

theorem encode_eq (fs : List Field) (h : ∀ f ∈ fs, Spec.ValidField f) : encode fs = Spec.encode fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [encode_cons, spec_encode_cons, field_encode_eq f (h f (by simp)),
      ih (fun g hg => h g (by simp [hg]))]

/-! ## One record -/

/-- The length checks in `decodeField` look at no more than `k` bytes. -/
theorem take_short (l : List UInt8) (k : Nat) : ((l.take k).length < k) = (l.length < k) := by
  simp only [List.length_take]
  apply propext
  omega

theorem decodeField_iff (bs : List UInt8) (f : Field) (rest : List UInt8) :
    decodeField bs = some (f, rest) ↔
      ∃ tag payload, bs = tag ++ payload ++ rest ∧ Spec.FieldBytes tag payload f := by
  constructor
  · intro h
    unfold decodeField at h
    simp only [take_short] at h
    cases ht : Varint.decodeAux 5 bs with
    | none => rw [ht] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨t, r⟩ := p
      obtain ⟨tag, hbs, hshape, hg⟩ := (Proofs.Varint.decodeAux_iff 5 bs t r).mp ht
      rw [ht] at h
      simp only at h
      by_cases hc : 2 ^ 32 ≤ t ∨ t / 8 = 0
      · simp only [hc, ↓reduceIte] at h
        exact absurd h (by simp)
      · simp only [hc, ↓reduceIte] at h
        have ht32 : t < 2 ^ 32 := by omega
        have hn : 1 ≤ t / 8 := by omega
        subst hbs
        subst hg
        split at h
        · rename_i hw
          split at h
          · rename_i v r' hv
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨pre, hr, hiv⟩ := (Proofs.Varint.decode_iff r v r').mp hv
            refine ⟨tag, pre, by rw [hr, List.append_assoc], hshape, ht32, rfl, hn, ?_⟩
            rw [hw]
            exact hiv
          · exact absurd h (by simp)
        · rename_i hw
          by_cases hl : r.length < 8
          · simp only [hl, ↓reduceIte] at h
            exact absurd h (by simp)
          · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨tag, r.take 8, by rw [List.append_assoc, List.take_append_drop], hshape, ht32,
              rfl, hn, ?_⟩
            rw [hw]
            exact ⟨by simp; omega, Proofs.Fixed.leValue_eq _⟩
        · rename_i hw
          split at h
          · rename_i len r2 hv
            obtain ⟨pre, hr, hps, hpv⟩ := (Proofs.Varint.decodeAux_iff 5 r len r2).mp hv
            by_cases hl : 2 ^ 31 - 16 ≤ len ∨ r2.length < len
            · simp only [hl, ↓reduceIte] at h
              exact absurd h (by simp)
            · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hlen : (r2.take len).length = len := by simp; omega
              refine ⟨tag, pre ++ r2.take len, ?_, hshape, ht32, rfl, hn, ?_⟩
              · rw [hr, List.append_assoc, List.append_assoc, List.take_append_drop]
              · rw [hw]
                exact ⟨pre, rfl, hps, by rw [hlen, hpv], by rw [hlen]; omega⟩
          · exact absurd h (by simp)
        · rename_i hw
          by_cases hl : r.length < 4
          · simp only [hl, ↓reduceIte] at h
            exact absurd h (by simp)
          · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨tag, r.take 4, by rw [List.append_assoc, List.take_append_drop], hshape, ht32,
              rfl, hn, ?_⟩
            rw [hw]
            exact ⟨by simp; omega, Proofs.Fixed.leValue_eq _⟩
        · exact absurd h (by simp)
  · rintro ⟨tag, payload, rfl, hshape, ht32, hnum, hn, hm⟩
    obtain ⟨num, val⟩ := f
    have hd : Varint.decodeAux 5 (tag ++ payload ++ rest) =
        some (Spec.groupsValue tag, payload ++ rest) :=
      (Proofs.Varint.decodeAux_iff 5 _ _ _).mpr ⟨tag, List.append_assoc _ _ _, hshape, rfl⟩
    have hc : ¬(2 ^ 32 ≤ Spec.groupsValue tag ∨ Spec.groupsValue tag / 8 = 0) := by
      simp only at hnum hn
      omega
    have hnum' : num = Spec.groupsValue tag / 8 := hnum
    unfold decodeField
    simp only [take_short]
    rw [hd]
    simp only [hc, ↓reduceIte]
    simp only at hm
    split at hm
    · rename_i v hw
      rw [hw]
      simp only
      rw [(Proofs.Varint.decode_iff _ v rest).mpr ⟨payload, rfl, hm⟩, hnum']
    · rename_i v hw
      obtain ⟨hl, rfl⟩ := hm
      have hl' : ¬(payload ++ rest).length < 8 := by simp; omega
      rw [hw]
      simp only [hl', ↓reduceIte]
      rw [List.take_left' hl, List.drop_left' hl, Proofs.Fixed.leValue_eq, hnum']
    · rename_i d hw
      obtain ⟨pre, rfl, hps, hpv, hdl⟩ := hm
      have hd2 : Varint.decodeAux 5 (pre ++ d ++ rest) = some (d.length, d ++ rest) :=
        (Proofs.Varint.decodeAux_iff 5 _ _ _).mpr ⟨pre, List.append_assoc _ _ _, hps, hpv.symm⟩
      have hl' : ¬(2 ^ 31 - 16 ≤ d.length ∨ (d ++ rest).length < d.length) := by simp; omega
      rw [hw]
      simp only
      rw [hd2]
      simp only [hl', ↓reduceIte]
      rw [List.take_left' rfl, List.drop_left' rfl, hnum']
    · rename_i v hw
      obtain ⟨hl, rfl⟩ := hm
      have hl' : ¬(payload ++ rest).length < 4 := by simp; omega
      rw [hw]
      simp only [hl', ↓reduceIte]
      rw [List.take_left' hl, List.drop_left' hl, Proofs.Fixed.leValue_eq, hnum']
    · exact hm.elim

/-! ## Messages -/

/-- Whatever `decodeAux` returns, with any fuel, is a message. -/
theorem decodeAux_sound (fuel : Nat) :
    ∀ bs fs, decodeAux fuel bs = some fs → Spec.Message bs fs := by
  induction fuel with
  | zero =>
    intro bs fs h
    cases bs with
    | nil =>
      simp only [decodeAux, Option.some.injEq] at h
      subst h
      exact .nil
    | cons b bs => simp [decodeAux] at h
  | succ fuel ih =>
    intro bs fs h
    cases bs with
    | nil =>
      simp only [decodeAux, Option.some.injEq] at h
      subst h
      exact .nil
    | cons b bs =>
      simp only [decodeAux] at h
      split at h
      · rename_i f rest hf
        split at h
        · rename_i fs' hfs
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨tag, payload, hbs, hfb⟩ := (decodeField_iff _ f rest).mp hf
          rw [hbs]
          exact .cons hfb (ih rest fs' hfs)
        · exact absurd h (by simp)
      · exact absurd h (by simp)

/-- A message is read whole by `decodeAux` with fuel at least its length:
    each record takes at least one byte, since its tag does. -/
theorem decodeAux_complete {bs : List UInt8} {fs : List Field} (h : Spec.Message bs fs) :
    ∀ fuel, bs.length ≤ fuel → decodeAux fuel bs = some fs := by
  induction h with
  | nil => intro fuel _; cases fuel <;> rfl
  | @cons tag payload rest f fs hfb _ ih =>
    intro fuel hlen
    obtain ⟨c, tag', rfl⟩ : ∃ c tag', tag = c :: tag' := by
      cases tag with
      | nil => exact absurd rfl hfb.1.1
      | cons c tag' => exact ⟨c, tag', rfl⟩
    simp only [List.cons_append, List.length_cons, List.length_append] at hlen ⊢
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hd : decodeField (c :: (tag' ++ payload ++ rest)) = some (f, rest) :=
      (decodeField_iff _ f rest).mpr ⟨c :: tag', payload, rfl, hfb⟩
    simp only [decodeAux, hd]
    rw [ih fuel' (by omega)]

theorem decode_iff (bs : List UInt8) (fs : List Field) : decode bs = some fs ↔ Spec.Message bs fs :=
  ⟨decodeAux_sound bs.length bs fs, fun h => decodeAux_complete h bs.length (Nat.le_refl _)⟩

/-! ## Decoded fields are valid -/

theorem fieldBytes_valid {tag payload : List UInt8} {f : Field} (h : Spec.FieldBytes tag payload f) :
    Spec.ValidField f := by
  obtain ⟨num, val⟩ := f
  obtain ⟨_, ht, hnum, hn, hm⟩ := h
  simp only at hnum hn hm
  refine ⟨hn, show num < 2 ^ 29 by omega, ?_⟩
  simp only
  split at hm
  · obtain ⟨_, rfl⟩ := hm
    exact Nat.mod_lt _ (by decide)
  · obtain ⟨hl, rfl⟩ := hm
    have := Proofs.Fixed.leValue_lt payload
    rw [hl] at this
    exact this
  · obtain ⟨_, _, _, _, hdl⟩ := hm
    exact hdl
  · obtain ⟨hl, rfl⟩ := hm
    have := Proofs.Fixed.leValue_lt payload
    rw [hl] at this
    exact this
  · exact hm.elim

theorem message_valid {bs : List UInt8} {fs : List Field} (h : Spec.Message bs fs) :
    ∀ f ∈ fs, Spec.ValidField f := by
  induction h with
  | nil => simp
  | cons hfb _ ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact fieldBytes_valid hfb
    · exact ih g hg

theorem decode_valid (bs : List UInt8) (fs : List Field) (h : decode bs = some fs) :
    ∀ f ∈ fs, Spec.ValidField f :=
  message_valid ((decode_iff bs fs).mp h)

/-! ## Round trip -/

/-- The shortest varint of a valid tag has at most five bytes. -/
theorem tag_bytes (n w : Nat) (hn : n < 2 ^ 29) (hw : w < 8) :
    Spec.VarintShape 5 (Spec.varint (n * 8 + w)) ∧ Spec.groupsValue (Spec.varint (n * 8 + w)) = n * 8 + w := by
  have hs := Proofs.Varint.varint_shape (n * 8 + w)
  have h5 : (2 : Nat) ^ 32 ≤ 128 ^ 5 := by decide
  exact ⟨Proofs.Varint.shape_mono hs.1 (Proofs.Varint.varint_length _ 5 (by decide) (by omega)), hs.2⟩

/-- The bytes the encoder writes for a valid field are one record. -/
theorem fieldBytes_split (f : Field) (h : Spec.ValidField f) :
    ∃ tag payload, Spec.fieldBytes f = tag ++ payload ∧ Spec.FieldBytes tag payload f := by
  obtain ⟨n, val⟩ := f
  obtain ⟨h1, h2, h3⟩ := h
  have h1 : 1 ≤ n := h1
  have h2 : n < 2 ^ 29 := h2
  cases val with
  | varint v =>
    have h3 : v < 2 ^ 64 := h3
    obtain ⟨hs, hg⟩ := tag_bytes n 0 h2 (by decide)
    refine ⟨Spec.varint (n * 8 + 0), Spec.varint v, rfl, hs, by rw [hg]; omega,
      show n = _ by rw [hg]; omega, h1, ?_⟩
    rw [hg, show (n * 8 + 0) % 8 = 0 by omega]
    have hv := Proofs.Varint.varint_shape v
    exact ⟨Proofs.Varint.shape_mono hv.1
      (Proofs.Varint.varint_length v 10 (by decide) (Nat.lt_of_lt_of_le h3 Proofs.Varint.two_pow_le)),
      by rw [hv.2, Nat.mod_eq_of_lt h3]⟩
  | i64 v =>
    have h3 : v < 2 ^ 64 := h3
    obtain ⟨hs, hg⟩ := tag_bytes n 1 h2 (by decide)
    refine ⟨Spec.varint (n * 8 + 1), Spec.leBytes 8 v, rfl, hs, by rw [hg]; omega,
      show n = _ by rw [hg]; omega, h1, ?_⟩
    rw [hg, show (n * 8 + 1) % 8 = 1 by omega]
    exact ⟨Proofs.Fixed.leBytes_length 8 v,
      (Proofs.Fixed.leValue_leBytes 8 v (by simpa using h3)).symm⟩
  | len d =>
    have h3 : d.length < 2 ^ 31 - 16 := h3
    obtain ⟨hs, hg⟩ := tag_bytes n 2 h2 (by decide)
    refine ⟨Spec.varint (n * 8 + 2), Spec.varint d.length ++ d, List.append_assoc _ _ _, hs,
      by rw [hg]; omega, show n = _ by rw [hg]; omega, h1, ?_⟩
    rw [hg, show (n * 8 + 2) % 8 = 2 by omega]
    have hv := Proofs.Varint.varint_shape d.length
    have h5 : (2 : Nat) ^ 31 ≤ 128 ^ 5 := by decide
    exact ⟨Spec.varint d.length, rfl,
      Proofs.Varint.shape_mono hv.1 (Proofs.Varint.varint_length _ 5 (by decide) (by omega)),
      hv.2, h3⟩
  | i32 v =>
    have h3 : v < 2 ^ 32 := h3
    obtain ⟨hs, hg⟩ := tag_bytes n 5 h2 (by decide)
    refine ⟨Spec.varint (n * 8 + 5), Spec.leBytes 4 v, rfl, hs, by rw [hg]; omega,
      show n = _ by rw [hg]; omega, h1, ?_⟩
    rw [hg, show (n * 8 + 5) % 8 = 5 by omega]
    exact ⟨Proofs.Fixed.leBytes_length 4 v,
      (Proofs.Fixed.leValue_leBytes 4 v (by simpa using h3)).symm⟩

theorem encode_message (fs : List Field) (h : ∀ f ∈ fs, Spec.ValidField f) :
    Spec.Message (Spec.encode fs) fs := by
  induction fs with
  | nil => exact .nil
  | cons f fs ih =>
    obtain ⟨tag, payload, he, hfb⟩ := fieldBytes_split f (h f (by simp))
    rw [spec_encode_cons, he]
    exact .cons hfb (ih fun g hg => h g (by simp [hg]))

theorem decode_encode (fs : List Field) (h : ∀ f ∈ fs, Spec.ValidField f) :
    decode (encode fs) = some fs := by
  rw [encode_eq fs h]
  exact (decode_iff _ _).mpr (encode_message fs h)

end Protobuf.Proofs.Message
