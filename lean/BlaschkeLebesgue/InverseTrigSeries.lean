module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

/-! # Finite, rigorous inverse-trigonometric enclosures

Even and odd partial sums bracket the arctangent. The half-angle identity
reduces arcsine to arctangent at an argument of smaller magnitude.
-/

public noncomputable section

open Finset

namespace BlaschkeLebesgue.InverseTrig

@[expose] def atanHorner (w : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (-1) ^ k / (2 * k + 1) + w * atanHorner w (k + 1) n

theorem atanHorner_eq_sum (w : ℝ) (k n : ℕ) :
    atanHorner w k n =
      ∑ i ∈ range n, (-1 : ℝ) ^ (i + k) / (2 * (i + k) + 1) * w ^ i := by
  induction n generalizing k with
  | zero => simp [atanHorner]
  | succ n ih =>
    rw [atanHorner, ih, sum_range_succ']
    simp only [zero_add, pow_zero, mul_one, Nat.cast_zero, zero_add]
    rw [mul_sum]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [show i + (k + 1) = i + 1 + k by omega, pow_succ]
    push_cast
    ring

theorem atanHorner_sq (x : ℝ) (n : ℕ) :
    x * atanHorner (x ^ 2) 0 n =
      ∑ i ∈ range n, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / (2 * i + 1) := by
  rw [atanHorner_eq_sum, mul_sum]
  apply sum_congr rfl
  intro i hi
  simp only [add_zero, pow_succ]
  ring

theorem atanTerm_antitone {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : ℕ ↦ x ^ (2 * n + 1) / (2 * n + 1)) := by
  intro m n hmn
  apply div_le_div₀ (pow_nonneg hx _)
    (pow_le_pow_of_le_one hx hx1 (by omega)) (by positivity)
  exact_mod_cast (show 2 * m + 1 ≤ 2 * n + 1 by omega)

theorem atan_partial_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    x * atanHorner (x ^ 2) 0 (2 * n) ≤ Real.arctan x ∧
      Real.arctan x ≤ x * atanHorner (x ^ 2) 0 (2 * n + 1) := by
  have ht := (Real.hasSum_arctan (x := x)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hx1)).tendsto_sum_nat
  simp only [mul_div_assoc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at ht
  have hm := atanTerm_antitone hx hx1.le
  rw [atanHorner_sq, atanHorner_sq]
  simp only [mul_div_assoc]
  exact ⟨hm.alternating_series_le_tendsto ht n, hm.tendsto_le_alternating_series ht n⟩

theorem arcsin_eq_two_arctan {x : ℝ} (hx : -1 < x) (hx1 : x < 1) :
    Real.arcsin x = 2 * Real.arctan (x / (1 + Real.sqrt (1 - x ^ 2))) := by
  have hq : 0 < 1 - x ^ 2 := by nlinarith
  have hr : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hq
  have hr2 := Real.sq_sqrt hq.le
  have hd : 0 < 1 + Real.sqrt (1 - x ^ 2) := by positivity
  have ht0 : -1 < x / (1 + Real.sqrt (1 - x ^ 2)) :=
    (lt_div_iff₀ hd).2 (by nlinarith)
  have ht1 : x / (1 + Real.sqrt (1 - x ^ 2)) < 1 :=
    (div_lt_iff₀ hd).2 (by nlinarith)
  rw [Real.arcsin_eq_arctan ⟨hx, hx1⟩, Real.two_mul_arctan ht0 ht1]
  congr 1
  have ht2 : 1 - (x / (1 + Real.sqrt (1 - x ^ 2))) ^ 2 ≠ 0 := by nlinarith
  field_simp
  rw [show (1 + Real.sqrt (1 - x ^ 2)) ^ 2 - x ^ 2 =
    2 * Real.sqrt (1 - x ^ 2) * (1 + Real.sqrt (1 - x ^ 2)) by nlinarith]
  field_simp

end BlaschkeLebesgue.InverseTrig
