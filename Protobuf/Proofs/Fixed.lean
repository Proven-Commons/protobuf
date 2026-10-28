/-
  Fixed-width values: `leValue` and `leBytes` in `Protobuf/Wire.lean`
  are `Protobuf.Spec.leValue` and `Protobuf.Spec.leBytes`, `Protobuf.Spec.leBytes k n` has `k`
  bytes, and the two are inverse: reading back `k` bytes of a number
  below 256^k gives the number, and writing the value of a list of bytes
  in as many bytes gives the list.
-/

import Protobuf
import Protobuf.Spec.Defs

namespace Protobuf.Proofs.Fixed

open Protobuf

/-! ## Cons formulas for the spec -/

theorem sum_map_mul_left (l : List Nat) (g : Nat → Nat) (c : Nat) :
    (l.map fun i => c * g i).sum = c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.sum_cons, ih, Nat.mul_add]

theorem spec_leValue_nil : Protobuf.Spec.leValue [] = 0 := rfl

theorem spec_leValue_cons (b : UInt8) (bs : List UInt8) :
    Protobuf.Spec.leValue (b :: bs) = b.toNat + 256 * Protobuf.Spec.leValue bs := by
  unfold Protobuf.Spec.leValue
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  have : ((fun i => ((b :: bs).getD i 0).toNat * 256 ^ i) ∘ Nat.succ) =
      fun i => 256 * ((bs.getD i 0).toNat * 256 ^ i) := by
    funext i
    simp [Nat.pow_succ', Nat.mul_left_comm]
  rw [this, sum_map_mul_left]
  simp

theorem spec_leBytes_zero (n : Nat) : Protobuf.Spec.leBytes 0 n = [] := rfl

theorem spec_leBytes_succ (k n : Nat) :
    Protobuf.Spec.leBytes (k + 1) n = (n % 256).toUInt8 :: Protobuf.Spec.leBytes k (n / 256) := by
  unfold Protobuf.Spec.leBytes
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    simp [Nat.pow_succ', Nat.div_div_eq_div_mul]

/-! ## The code is the spec -/

theorem leValue_cons (b : UInt8) (bs : List UInt8) :
    leValue (b :: bs) = b.toNat + 256 * leValue bs := rfl

theorem leValue_eq (bs : List UInt8) : leValue bs = Protobuf.Spec.leValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [leValue_cons, spec_leValue_cons, ih]

theorem leBytes_eq (k n : Nat) : leBytes k n = Protobuf.Spec.leBytes k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [spec_leBytes_succ, ← ih]; rfl

/-! ## Length, bounds and inverses -/

theorem leBytes_length (k n : Nat) : (Protobuf.Spec.leBytes k n).length = k := by
  simp [Protobuf.Spec.leBytes]

theorem toNat_lt (b : UInt8) : b.toNat < 256 := UInt8.toNat_lt b

theorem leValue_leBytes (k n : Nat) (h : n < 256 ^ k) : Protobuf.Spec.leValue (Protobuf.Spec.leBytes k n) = n := by
  induction k generalizing n with
  | zero =>
    simp at h
    subst h
    rfl
  | succ k ih =>
    have hd : n / 256 < 256 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_succ]
      exact h
    rw [spec_leBytes_succ, spec_leValue_cons, ih _ hd]
    have : (n % 256).toUInt8.toNat = n % 256 := by simp
    rw [this]
    exact Nat.mod_add_div n 256

theorem leValue_lt (bs : List UInt8) : Protobuf.Spec.leValue bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [spec_leValue_nil]
  | cons b bs ih =>
    rw [spec_leValue_cons, List.length_cons, Nat.pow_succ']
    have := toNat_lt b
    omega

theorem leBytes_leValue (bs : List UInt8) : Protobuf.Spec.leBytes bs.length (Protobuf.Spec.leValue bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := toNat_lt b
    rw [List.length_cons, spec_leBytes_succ, spec_leValue_cons]
    have hm : (b.toNat + 256 * Protobuf.Spec.leValue bs) % 256 = b.toNat := by omega
    have hd : (b.toNat + 256 * Protobuf.Spec.leValue bs) / 256 = Protobuf.Spec.leValue bs := by omega
    rw [hm, hd, ih]
    simp

end Protobuf.Proofs.Fixed
