/-
  The varint encoder and decoder of `Protobuf/Varint.lean` against the
  spec: `encode` writes `Protobuf.Spec.varint`, `decodeAux k` reads exactly one
  varint of at most `k` bytes (shape `Protobuf.Spec.VarintShape k`, value
  `Protobuf.Spec.groupsValue`), `decode` reads exactly a `Protobuf.Spec.IsVarint`, and
  decoding what the encoder wrote gives the number back.
-/

import Protobuf
import Protobuf.Spec.Defs

namespace Protobuf.Proofs.Varint

open Protobuf

/-! ## Groups and shapes, one byte at a time -/

theorem sum_map_mul (c : Nat) (g : Nat → Nat) (l : List Nat) :
    (l.map fun i => c * g i).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, ih, Nat.mul_add]

theorem groupsValue_nil : Protobuf.Spec.groupsValue [] = 0 := rfl

theorem groupsValue_cons (b : UInt8) (bs : List UInt8) :
    Protobuf.Spec.groupsValue (b :: bs) = b.toNat % 128 + 128 * Protobuf.Spec.groupsValue bs := by
  unfold Protobuf.Spec.groupsValue
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
    ← sum_map_mul]
  congr 1
  · simp
  · congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_eq_add_one, List.getD_cons_succ, Nat.pow_succ]
    rw [Nat.mul_comm (128 ^ i) 128, Nat.mul_left_comm]

theorem shape_zero (bs : List UInt8) : ¬ Protobuf.Spec.VarintShape 0 bs := by
  intro ⟨h1, h2, _⟩
  exact h1 (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h2))

theorem shape_nil (k : Nat) : ¬ Protobuf.Spec.VarintShape k [] := fun h => h.1 rfl

theorem shape_cons (k : Nat) (b : UInt8) (bs : List UInt8) :
    Protobuf.Spec.VarintShape (k + 1) (b :: bs) ↔
      (b.toNat < 128 ∧ bs = []) ∨ (128 ≤ b.toNat ∧ Protobuf.Spec.VarintShape k bs) := by
  cases bs with
  | nil =>
    simp [Protobuf.Spec.VarintShape]
  | cons c cs =>
    simp [Protobuf.Spec.VarintShape, List.dropLast_cons_cons, List.getLast?_cons_cons]
    exact ⟨fun ⟨h1, ⟨h2, h3⟩, h4⟩ => ⟨h2, h1, h3, h4⟩, fun ⟨h2, h1, h3, h4⟩ => ⟨h1, ⟨h2, h3⟩, h4⟩⟩


/-! ## The decoder -/

/-- The right-hand side of `decodeAux_iff` at `k + 1`, one byte at a time. -/
theorem split_cons (k : Nat) (b : UInt8) (bs : List UInt8) (v : Nat) (rest : List UInt8) :
    (∃ pre, b :: bs = pre ++ rest ∧ Protobuf.Spec.VarintShape (k + 1) pre ∧ v = Protobuf.Spec.groupsValue pre) ↔
      (b.toNat < 128 ∧ bs = rest ∧ v = b.toNat) ∨
      (128 ≤ b.toNat ∧ ∃ v', (∃ pre, bs = pre ++ rest ∧ Protobuf.Spec.VarintShape k pre ∧
        v' = Protobuf.Spec.groupsValue pre) ∧ v = b.toNat % 128 + 128 * v') := by
  constructor
  · rintro ⟨pre, h, hs, hv⟩
    cases pre with
    | nil => exact absurd hs (shape_nil _)
    | cons c pre =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hbc, rfl⟩ := h
      rw [← hbc] at hs hv
      rcases (shape_cons k b pre).mp hs with ⟨hc, rfl⟩ | ⟨hc, hs'⟩
      · left
        refine ⟨hc, by simp, ?_⟩
        rw [hv, groupsValue_cons, groupsValue_nil]
        omega
      · right
        exact ⟨hc, _, ⟨pre, rfl, hs', rfl⟩, by rw [hv, groupsValue_cons]⟩
  · rintro (⟨hc, rfl, rfl⟩ | ⟨hc, v', ⟨pre, rfl, hs, rfl⟩, rfl⟩)
    · refine ⟨[b], rfl, (shape_cons k b []).mpr (Or.inl ⟨hc, rfl⟩), ?_⟩
      rw [groupsValue_cons, groupsValue_nil]
      omega
    · exact ⟨b :: pre, rfl, (shape_cons k b pre).mpr (Or.inr ⟨hc, hs⟩), by rw [groupsValue_cons]⟩

theorem decodeAux_iff (k : Nat) (bs : List UInt8) (v : Nat) (rest : List UInt8) :
    Varint.decodeAux k bs = some (v, rest) ↔
      ∃ pre, bs = pre ++ rest ∧ Protobuf.Spec.VarintShape k pre ∧ v = Protobuf.Spec.groupsValue pre := by
  induction k generalizing bs v with
  | zero =>
    simp only [Varint.decodeAux, reduceCtorEq, false_iff, not_exists, not_and]
    intro pre _ h
    exact absurd h (shape_zero pre)
  | succ k ih =>
    cases bs with
    | nil =>
      simp only [Varint.decodeAux, reduceCtorEq, false_iff, not_exists, not_and]
      intro pre h hs _
      have : pre = [] := (List.append_eq_nil_iff.mp h.symm).1
      subst this
      exact shape_nil _ hs
    | cons b bs =>
      have hb := UInt8.toNat_lt b
      rw [split_cons]
      simp only [← ih]
      simp only [Varint.decodeAux]
      by_cases hc : b.toNat < 128
      · have hc' : ¬ 128 ≤ b.toNat := by omega
        simp only [hc, hc', ite_true, false_and, or_false, Option.some.injEq, Prod.mk.injEq,
          true_and]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1.symm⟩, fun ⟨h1, h2⟩ => ⟨h2.symm, h1⟩⟩
      · cases h : Varint.decodeAux k bs with
        | none => simp [hc]
        | some p =>
          obtain ⟨v0, r0⟩ := p
          have hc' : 128 ≤ b.toNat := by omega
          simp only [hc, hc', ite_false, Option.some.injEq, Prod.mk.injEq, true_and, false_and,
            false_or]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨v0, ⟨rfl, h2⟩, by omega⟩
          · rintro ⟨v', ⟨rfl, h2⟩, h3⟩
            exact ⟨by omega, h2⟩


theorem decode_iff (bs : List UInt8) (v : Nat) (rest : List UInt8) :
    Varint.decode bs = some (v, rest) ↔ ∃ pre, bs = pre ++ rest ∧ Protobuf.Spec.IsVarint pre v := by
  unfold Varint.decode
  cases h : Varint.decodeAux 10 bs with
  | none =>
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro pre hbs ⟨hs, _⟩
    have h2 := (decodeAux_iff 10 bs _ rest).mpr ⟨pre, hbs, hs, rfl⟩
    rw [h] at h2
    exact absurd h2 (by simp)
  | some p =>
    obtain ⟨v0, r0⟩ := p
    obtain ⟨pre0, hbs0, hs0, hv0⟩ := (decodeAux_iff 10 bs v0 r0).mp h
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨pre0, hbs0, hs0, by rw [hv0]⟩
    · rintro ⟨pre, hbs, hs, hv⟩
      have h2 := (decodeAux_iff 10 bs _ rest).mpr ⟨pre, hbs, hs, rfl⟩
      rw [h] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      exact ⟨by rw [hv, h2.1], h2.2⟩

/-! ## The shortest varint -/

theorem toUInt8_toNat_of_lt (n : Nat) (h : n < 256) : n.toUInt8.toNat = n := by
  simp
  omega

theorem varintAux_succ (f n : Nat) :
    Protobuf.Spec.varintAux (f + 1) n =
      if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: Protobuf.Spec.varintAux f (n / 128) :=
  rfl

theorem div_lt (n f : Nat) (h : n < 128 ^ (f + 1)) : n / 128 < 128 ^ f :=
  (Nat.div_lt_iff_lt_mul (by decide)).mpr (by rw [← Nat.pow_succ]; exact h)

theorem lt_pow (n : Nat) : n < 128 ^ (n + 1) :=
  Nat.lt_of_lt_of_le (Nat.lt_pow_self (by decide)) (Nat.pow_le_pow_right (by decide) (by omega))

theorem single_shape (n : Nat) (h : n < 128) :
    Protobuf.Spec.VarintShape [n.toUInt8].length [n.toUInt8] ∧ Protobuf.Spec.groupsValue [n.toUInt8] = n := by
  have h1 : n.toUInt8.toNat = n := toUInt8_toNat_of_lt n (by omega)
  refine ⟨(shape_cons 0 _ []).mpr (Or.inl ⟨by omega, rfl⟩), ?_⟩
  rw [groupsValue_cons, groupsValue_nil, h1]
  omega

theorem cons_shape (n : Nat) (rest : List UInt8)
    (hr : Protobuf.Spec.VarintShape rest.length rest ∧ Protobuf.Spec.groupsValue rest = n / 128) :
    Protobuf.Spec.VarintShape ((n % 128 + 128).toUInt8 :: rest).length ((n % 128 + 128).toUInt8 :: rest) ∧
      Protobuf.Spec.groupsValue ((n % 128 + 128).toUInt8 :: rest) = n := by
  have h1 : (n % 128 + 128).toUInt8.toNat = n % 128 + 128 := toUInt8_toNat_of_lt _ (by omega)
  refine ⟨(shape_cons rest.length _ rest).mpr (Or.inr ⟨by omega, hr.1⟩), ?_⟩
  rw [groupsValue_cons, hr.2, h1]
  omega

theorem varintAux_shape (f : Nat) : ∀ n, n < 128 ^ (f + 1) →
    Protobuf.Spec.VarintShape (Protobuf.Spec.varintAux (f + 1) n).length (Protobuf.Spec.varintAux (f + 1) n) ∧
      Protobuf.Spec.groupsValue (Protobuf.Spec.varintAux (f + 1) n) = n := by
  induction f with
  | zero =>
    intro n hn
    have h : n < 128 := by simpa using hn
    rw [varintAux_succ]
    simp only [h, ite_true]
    exact single_shape n h
  | succ f ih =>
    intro n hn
    rw [varintAux_succ]
    by_cases h : n < 128
    · simp only [h, ite_true]
      exact single_shape n h
    · simp only [h, ite_false]
      exact cons_shape n _ (ih (n / 128) (div_lt n (f + 1) hn))

theorem varint_shape (n : Nat) :
    Protobuf.Spec.VarintShape (Protobuf.Spec.varint n).length (Protobuf.Spec.varint n) ∧ Protobuf.Spec.groupsValue (Protobuf.Spec.varint n) = n :=
  varintAux_shape n n (lt_pow n)

theorem varintAux_length (f : Nat) :
    ∀ n k, 1 ≤ k → n < 128 ^ k → (Protobuf.Spec.varintAux f n).length ≤ k := by
  induction f with
  | zero =>
    intro n k _ _
    simp [Protobuf.Spec.varintAux]
  | succ f ih =>
    intro n k hk hn
    rw [varintAux_succ]
    by_cases h : n < 128
    · simp only [h, ite_true, List.length_singleton]
      exact hk
    · simp only [h, ite_false, List.length_cons]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at hn
          omega
        · exact hj
      have := ih (n / 128) j hj (div_lt n j hn)
      omega

theorem varint_length (n k : Nat) (hk : 1 ≤ k) (h : n < 128 ^ k) : (Protobuf.Spec.varint n).length ≤ k :=
  varintAux_length (n + 1) n k hk h

theorem shape_mono {k k' : Nat} {bs : List UInt8} (h : Protobuf.Spec.VarintShape k bs) (hk : k ≤ k') :
    Protobuf.Spec.VarintShape k' bs :=
  ⟨h.1, Nat.le_trans h.2.1 hk, h.2.2⟩

theorem decodeAux_varint (n k : Nat) (rest : List UInt8) (hk : 1 ≤ k) (h : n < 128 ^ k) :
    Varint.decodeAux k (Protobuf.Spec.varint n ++ rest) = some (n, rest) := by
  have hs := varint_shape n
  exact (decodeAux_iff k _ n rest).mpr
    ⟨Protobuf.Spec.varint n, rfl, shape_mono hs.1 (varint_length n k hk h), hs.2.symm⟩

/-! ## The encoder -/

theorem encodeAux_eq (f n : Nat) : Varint.encodeAux f n = Protobuf.Spec.varintAux f n := by
  induction f generalizing n with
  | zero => rfl
  | succ f ih => simp only [Varint.encodeAux, Protobuf.Spec.varintAux, ih]

/-- More fuel than the digits need changes nothing. -/
theorem varintAux_add (f g : Nat) :
    ∀ n, n < 128 ^ (f + 1) → Protobuf.Spec.varintAux (f + g + 1) n = Protobuf.Spec.varintAux (f + 1) n := by
  induction f with
  | zero =>
    intro n hn
    have h : n < 128 := by simpa using hn
    rw [varintAux_succ, varintAux_succ]
    simp only [h, ite_true]
  | succ f ih =>
    intro n hn
    rw [varintAux_succ, varintAux_succ]
    by_cases h : n < 128
    · simp only [h, ite_true]
    · simp only [h, ite_false]
      rw [Nat.add_right_comm f 1 g, ih (n / 128) (div_lt n (f + 1) hn)]

theorem varintAux_eq_varint (f n : Nat) (hf : 1 ≤ f) (h : n < 128 ^ f) :
    Protobuf.Spec.varintAux f n = Protobuf.Spec.varint n := by
  unfold Protobuf.Spec.varint
  obtain ⟨f, rfl⟩ : ∃ j, f = j + 1 := ⟨f - 1, by omega⟩
  rcases Nat.le_total f n with hle | hle
  · have := varintAux_add f (n - f) n h
    rw [show f + (n - f) + 1 = n + 1 by omega] at this
    exact this.symm
  · have := varintAux_add n (f - n) n (lt_pow n)
    rw [show n + (f - n) + 1 = f + 1 by omega] at this
    exact this

theorem two_pow_le : 2 ^ 64 ≤ 128 ^ 10 := by decide

theorem encode_eq (n : Nat) (h : n < 2 ^ 64) : Varint.encode n = Protobuf.Spec.varint n := by
  unfold Varint.encode
  rw [encodeAux_eq]
  exact varintAux_eq_varint 10 n (by decide) (Nat.lt_of_lt_of_le h two_pow_le)

theorem decode_encode (n : Nat) (rest : List UInt8) (h : n < 2 ^ 64) :
    Varint.decode (Varint.encode n ++ rest) = some (n, rest) := by
  unfold Varint.decode
  rw [encode_eq n h, decodeAux_varint n 10 rest (by decide) (Nat.lt_of_lt_of_le h two_pow_le)]
  simp [Nat.mod_eq_of_lt h]

end Protobuf.Proofs.Varint
