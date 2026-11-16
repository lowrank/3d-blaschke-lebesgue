module

public import BlaschkeLebesgue.CompletionRegion

/-!
# Coupled allocation of the two opposite-edge radii

The endpoint allocation inequality is proved directly by squaring nonnegative
radicals. Both radii share the same total deficit; they are not replaced by
two independent worst-case radii.
-/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Completion

def edgeRadius (e : ℝ) : ℝ := Real.sqrt (3 / 4 + e / 4)
def separationUpper (a b : ℝ) : ℝ := Real.sqrt (1 / 2 + (a - b) / 4)
def allocationNumerator (a b x y : ℝ) : ℝ :=
  edgeRadius 0 * Real.sqrt (1 + max (x ^ 2) (y ^ 2)) +
    edgeRadius a * Real.sqrt (1 + min (x ^ 2) (y ^ 2)) - separationUpper a b
def determinantFactor (a x y : ℝ) : ℝ :=
  edgeRadius a / Real.sqrt (1 + min (x ^ 2) (y ^ 2))

theorem edgeRadius_pos {e : ℝ} (he : 0 ≤ e) : 0 < edgeRadius e := by
  apply Real.sqrt_pos.2
  linarith

theorem edgeRadius_sq {e : ℝ} (he : 0 ≤ e) : edgeRadius e ^ 2 = 3 / 4 + e / 4 :=
  Real.sq_sqrt (by linarith)

theorem edgeRadius_mono : Monotone edgeRadius := by
  intro e d hed
  exact Real.sqrt_le_sqrt (by linarith)

theorem edgeRadius_sum_lower {e₁ e₂ : ℝ} (h1 : 0 ≤ e₁) (h2 : 0 ≤ e₂) :
    edgeRadius 0 + edgeRadius (e₁ + e₂) ≤ edgeRadius e₁ + edgeRadius e₂ := by
  have h0 := edgeRadius_pos (by norm_num : (0 : ℝ) ≤ 0)
  have hr1 := edgeRadius_pos h1
  have hr2 := edgeRadius_pos h2
  have hrA := edgeRadius_pos (add_nonneg h1 h2)
  have hprod : edgeRadius 0 * edgeRadius (e₁ + e₂) ≤ edgeRadius e₁ * edgeRadius e₂ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, mul_pow, edgeRadius_sq (by norm_num : (0 : ℝ) ≤ 0),
      edgeRadius_sq (add_nonneg h1 h2), edgeRadius_sq h1, edgeRadius_sq h2]
    nlinarith [mul_nonneg h1 h2]
  have hs0 := edgeRadius_sq (by norm_num : (0 : ℝ) ≤ 0)
  have hs1 := edgeRadius_sq h1
  have hs2 := edgeRadius_sq h2
  have hsA := edgeRadius_sq (add_nonneg h1 h2)
  nlinarith

/-- The smaller factor receives the larger endpoint radius in the uniform
lower bound, regardless of how the actual two deficits are distributed. -/
theorem radius_allocation_lower {e₁ e₂ : ℝ} (h1 : 0 ≤ e₁) (h2 : 0 ≤ e₂) (x y : ℝ) :
    edgeRadius 0 * Real.sqrt (1 + max (x ^ 2) (y ^ 2)) +
      edgeRadius (e₁ + e₂) * Real.sqrt (1 + min (x ^ 2) (y ^ 2)) ≤
    edgeRadius e₁ * Real.sqrt (1 + x ^ 2) + edgeRadius e₂ * Real.sqrt (1 + y ^ 2) := by
  have hs := edgeRadius_sum_lower h1 h2
  have hr1 := edgeRadius_mono h1
  have hr2 := edgeRadius_mono h2
  rcases le_total (x ^ 2) (y ^ 2) with hxy | hyx
  · rw [max_eq_right hxy, min_eq_left hxy]
    have hf : Real.sqrt (1 + x ^ 2) ≤ Real.sqrt (1 + y ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsum := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (1 + x ^ 2))
    have hdiff := mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hr2)
    nlinarith
  · rw [max_eq_left hyx, min_eq_right hyx]
    have hf : Real.sqrt (1 + y ^ 2) ≤ Real.sqrt (1 + x ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsum := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (1 + y ^ 2))
    have hdiff := mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hr1)
    nlinarith

theorem determinantFactor_nonneg {a : ℝ} (ha : 0 ≤ a) (x y : ℝ) :
    0 ≤ determinantFactor a x y := div_nonneg (edgeRadius_pos ha).le (Real.sqrt_nonneg _)

theorem radius_factor_le {e a : ℝ} (ha : 0 ≤ a) (he : e ≤ a) (x y : ℝ) :
    edgeRadius e / Real.sqrt (1 + x ^ 2) ≤ determinantFactor a x y := by
  have hmin : 0 ≤ min (x ^ 2) (y ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
  apply div_le_div₀ (edgeRadius_pos ha).le (edgeRadius_mono he)
    (Real.sqrt_pos.2 (by linarith))
  exact Real.sqrt_le_sqrt (by linarith [min_le_left (x ^ 2) (y ^ 2)])

theorem determinantFactor_swap (a x y : ℝ) : determinantFactor a y x = determinantFactor a x y := by
  simp only [determinantFactor, min_comm]

theorem determinantFactor_neg (a x y : ℝ) : determinantFactor a (-x) (-y) = determinantFactor a x y := by
  simp only [determinantFactor, neg_sq]

theorem allocationNumerator_neg (a b x y : ℝ) :
    allocationNumerator a b (-x) (-y) = allocationNumerator a b x y := by
  simp only [allocationNumerator, neg_sq]

end BlaschkeLebesgue.Completion
