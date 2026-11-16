module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Int.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-!
# Exact fixed-point rounding, including signed division and square roots

The computational operations use unbounded integers. In particular, division
normalizes a negative denominator before Euclidean division. The square root
uses the proved natural-number integer square root, with no floating proposal.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

def scale (precision : ℕ) : ℕ := 2 ^ precision

noncomputable def value (precision : ℕ) (z : ℤ) : ℝ := (z : ℝ) / (scale precision : ℝ)

def floorDiv (a b : ℤ) : ℤ := if 0 ≤ b then a / b else (-a) / (-b)
def ceilDiv (a b : ℤ) : ℤ := -floorDiv (-a) b

theorem scale_pos (precision : ℕ) : 0 < scale precision := Nat.pow_pos (by decide)
theorem scale_real_pos (precision : ℕ) : (0 : ℝ) < (scale precision : ℝ) := by exact_mod_cast scale_pos precision

theorem floorDiv_eq_floor (a b : ℤ) : floorDiv a b = ⌊(a : ℚ) / (b : ℚ)⌋ := by
  by_cases hb : 0 ≤ b
  · rw [floorDiv, ite_eq_left hb, ← Int.toNat_of_nonneg hb]
    simpa only [Int.cast_natCast] using (Rat.floor_intCast_div_natCast a b.toNat).symm
  · have hnb : 0 ≤ -b := by omega
    rw [floorDiv, ite_eq_right hb]
    have heq : (a : ℚ) / (b : ℚ) = ((-a : ℤ) : ℚ) / ((-b : ℤ) : ℚ) := by simp
    rw [heq, ← Int.toNat_of_nonneg hnb]
    simpa only [Int.cast_natCast] using (Rat.floor_intCast_div_natCast (-a) (-b).toNat).symm

theorem ceilDiv_eq_ceil (a b : ℤ) : ceilDiv a b = ⌈(a : ℚ) / (b : ℚ)⌉ := by
  rw [ceilDiv, floorDiv_eq_floor]
  simp only [Int.cast_neg, neg_div, Int.floor_neg, neg_neg]

theorem floorDiv_le_real (a b : ℤ) : (floorDiv a b : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rw [floorDiv_eq_floor]
  simpa only [Rat.cast_intCast, Rat.cast_div] using
    (Rat.cast_le (K := ℝ)).2 (Int.floor_le ((a : ℚ) / b))

theorem real_le_ceilDiv (a b : ℤ) : (a : ℝ) / (b : ℝ) ≤ (ceilDiv a b : ℝ) := by
  rw [ceilDiv_eq_ceil]
  simpa only [Rat.cast_intCast, Rat.cast_div] using
    (Rat.cast_le (K := ℝ)).2 (Int.le_ceil ((a : ℚ) / b))

theorem floorDiv_value_le (precision : ℕ) (a b : ℤ) :
    value precision (floorDiv a b) ≤ ((a : ℝ) / (b : ℝ)) / (scale precision : ℝ) :=
  div_le_div_of_nonneg_right (floorDiv_le_real a b) (scale_real_pos precision).le

theorem value_le_ceilDiv (precision : ℕ) (a b : ℤ) :
    ((a : ℝ) / (b : ℝ)) / (scale precision : ℝ) ≤ value precision (ceilDiv a b) :=
  div_le_div_of_nonneg_right (real_le_ceilDiv a b) (scale_real_pos precision).le

theorem floorDiv_scale_value_le (precision : ℕ) (a : ℤ) :
    value precision (floorDiv a (scale precision)) ≤ (a : ℝ) / (scale precision : ℝ) ^ 2 := by
  simpa only [Int.cast_natCast, div_div, pow_two] using floorDiv_value_le precision a (scale precision)

theorem value_le_ceilDiv_scale (precision : ℕ) (a : ℤ) :
    (a : ℝ) / (scale precision : ℝ) ^ 2 ≤ value precision (ceilDiv a (scale precision)) := by
  simpa only [Int.cast_natCast, div_div, pow_two] using value_le_ceilDiv precision a (scale precision)

def sqrtFloor (a : ℤ) : ℤ := a.toNat.sqrt
def sqrtCeil (a : ℤ) : ℤ := let r := sqrtFloor a; if r * r = a then r else r + 1

theorem sqrtFloor_nonneg (a : ℤ) : 0 ≤ sqrtFloor a := Int.natCast_nonneg _
theorem sqrtCeil_nonneg (a : ℤ) : 0 ≤ sqrtCeil a := by
  dsimp only [sqrtCeil]
  split_ifs <;> linarith [sqrtFloor_nonneg a]

theorem sqrtFloor_sq_le {a : ℤ} (ha : 0 ≤ a) : sqrtFloor a ^ 2 ≤ a := by
  have h := Nat.sqrt_le' a.toNat
  have h' : (a.toNat.sqrt : ℤ) ^ 2 ≤ (a.toNat : ℤ) := by exact_mod_cast h
  simpa only [sqrtFloor, Int.toNat_of_nonneg ha] using h'

theorem le_sqrtCeil_sq {a : ℤ} (ha : 0 ≤ a) : a ≤ sqrtCeil a ^ 2 := by
  dsimp only [sqrtCeil]
  split_ifs with h
  · nlinarith only [h]
  · have hnat := Nat.lt_succ_sqrt' a.toNat
    have h' : (a.toNat : ℤ) < ((a.toNat.sqrt : ℤ) + 1) ^ 2 := by exact_mod_cast hnat
    simp only [Int.toNat_of_nonneg ha] at h'
    exact h'.le

theorem sqrtFloor_value_le_sqrt {a : ℤ} (ha : 0 ≤ a) (precision : ℕ) :
    value precision (sqrtFloor (a * scale precision)) ≤ Real.sqrt (value precision a) := by
  have hS := scale_real_pos precision
  have hSi : (0 : ℤ) ≤ (scale precision : ℤ) := Int.natCast_nonneg _
  have hsq : (sqrtFloor (a * scale precision) : ℝ) ^ 2 ≤ (a : ℝ) * (scale precision : ℝ) := by
    exact_mod_cast sqrtFloor_sq_le (mul_nonneg ha hSi)
  apply Real.le_sqrt_of_sq_le
  unfold value
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hS)).2
  have heq : (a : ℝ) / (scale precision : ℝ) * (scale precision : ℝ) ^ 2 =
      (a : ℝ) * (scale precision : ℝ) := by field_simp
  rwa [heq]

theorem sqrt_le_sqrtCeil_value {a : ℤ} (ha : 0 ≤ a) (precision : ℕ) :
    Real.sqrt (value precision a) ≤ value precision (sqrtCeil (a * scale precision)) := by
  have hS := scale_real_pos precision
  have hSi : (0 : ℤ) ≤ (scale precision : ℤ) := Int.natCast_nonneg _
  have hsq : (a : ℝ) * (scale precision : ℝ) ≤ (sqrtCeil (a * scale precision) : ℝ) ^ 2 := by
    exact_mod_cast le_sqrtCeil_sq (mul_nonneg ha hSi)
  have h0 : 0 ≤ value precision (sqrtCeil (a * scale precision)) :=
    div_nonneg (by exact_mod_cast sqrtCeil_nonneg (a * scale precision)) hS.le
  apply (Real.sqrt_le_left h0).2
  unfold value
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hS)).2
  have heq : (a : ℝ) / (scale precision : ℝ) * (scale precision : ℝ) ^ 2 =
      (a : ℝ) * (scale precision : ℝ) := by field_simp
  rwa [heq]

end BlaschkeLebesgue.Certificates.FixedPoint
