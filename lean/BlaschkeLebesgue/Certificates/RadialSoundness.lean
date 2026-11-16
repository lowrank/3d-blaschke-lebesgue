module

public import BlaschkeLebesgue.Certificates.RadialArithmetic
public import BlaschkeLebesgue.Radial

/-!
# Meaning of the exact radial arithmetic checks

The checked coefficient has a strict real pi margin. The individual squared tests
imply the corresponding real square-root inequalities. Passing these finite tests
is distinct from their geometric meaning, supplied by `CapIntegrals.lean`.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.RadialArithmetic

theorem checkRow_numeric {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) :
    coefficient p positive negative = p.expectedCoefficient ∧
      0 < coefficient p positive negative ∧
      4144109 / 10000000 < piLower * coefficient p positive negative := by
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

theorem piLower_lt_pi : (piLower : ℝ) < Real.pi := by
  have h := Real.pi_gt_d20
  norm_num [piLower] at h ⊢
  exact h

/-- The output comparison interpreted in the real numbers, using a proved bound for pi. -/
theorem checkRow_real_margin {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) :
    (4144109 / 10000000 : ℝ) < Real.pi * (coefficient p positive negative : ℝ) := by
  obtain ⟨_, hpos, hbound⟩ := checkRow_numeric h
  have hpos' : 0 < (coefficient p positive negative : ℝ) := by exact_mod_cast hpos
  calc
    _ < (piLower : ℝ) * (coefficient p positive negative : ℝ) := by
      have hreal := (Rat.cast_lt (K := ℝ)).2 hbound
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul] at hreal
      exact hreal
    _ < _ := mul_lt_mul_of_pos_right piLower_lt_pi hpos'

theorem positiveStep_squares {p : Parameters} {k : ℕ} {y x : ℚ}
    (h : positiveStep p k y x = true) :
    0 ≤ 4 * x ^ 2 - (x ^ 2 + parameterM p) ^ 2 ∧
      0 < y * stepCosine k - x ∧
      y ^ 2 * (4 * x ^ 2 - (x ^ 2 + parameterM p) ^ 2) * stepSine k ^ 2 ≤
        (x ^ 2 + parameterM p) ^ 2 * (y * stepCosine k - x) ^ 2 := by
  simp only [positiveStep, decide_eq_true_eq] at h
  tauto

/-- Every accepted positive test implies the real propagation inequality. -/
theorem positiveStep_sound {p : Parameters} {k : ℕ} {y x : ℚ}
    (hm : 0 < parameterM p) (hx : 0 < x) (hy : 0 < y) (hs : 0 ≤ stepSine k)
    (h : positiveStep p k y x = true) :
    BlaschkeLebesgue.Radial.propagation (parameterM p) x (stepCosine k) (stepSine k) ≤ y := by
  obtain ⟨hrad, hlinear, hsquared⟩ := positiveStep_squares h
  exact (BlaschkeLebesgue.Radial.propagation_test_sound
    (by exact_mod_cast hm) (by exact_mod_cast hx) (by exact_mod_cast hy)
    (by exact_mod_cast hs) (by exact_mod_cast hrad) (by exact_mod_cast hlinear)
    (by exact_mod_cast hsquared)).2

/-- Every accepted negative test implies the real negative-cap bound. -/
theorem negativeStep_sound {p : Parameters} {k : ℕ} {previous z : ℚ}
    (h : negativeStep p k previous z = true) :
    -(p.lo : ℝ) * (cosine k : ℝ) +
      Real.sqrt (1 - (p.lo : ℝ) ^ 2 * (sine k : ℝ) ^ 2) ≤ (z : ℝ) := by
  simp only [negativeStep, decide_eq_true_eq] at h
  have hsign : 0 ≤ z + p.lo * cosine k := by tauto
  have hsquare : 1 - p.lo ^ 2 * sine k ^ 2 ≤ (z + p.lo * cosine k) ^ 2 := by tauto
  exact BlaschkeLebesgue.Radial.negative_cap_test_sound
    (by exact_mod_cast hsign) (by exact_mod_cast hsquare)

def exactSum (p : Parameters) (k : ℕ) : List ℕ → ℚ
  | [] => 0
  | x :: xs => ringTerm p k x + exactSum p (k + 1) xs

/-- Rounding each ring down gives a lower bound for the entire unrounded rational sum. -/
theorem roundedSum_le (p : Parameters) (k : ℕ) (xs : List ℕ) :
    (roundedSum p k xs : ℚ) / roundingScale ≤ exactSum p k xs := by
  induction xs generalizing k with
  | nil => simp [roundedSum, exactSum]
  | cons x xs ih =>
    simp only [roundedSum, exactSum, Int.cast_add, add_div]
    exact add_le_add (roundedTerm_le p k x) (ih (k + 1))

end BlaschkeLebesgue.Certificates.RadialArithmetic
