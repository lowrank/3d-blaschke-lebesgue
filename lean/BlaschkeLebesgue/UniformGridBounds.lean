module

public import BlaschkeLebesgue.UniformGridIntegral

/-! # Integrating signed bounds on the cells of a uniform grid -/

public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BlaschkeLebesgue

theorem rectangle_integral_lower {H : ℝ × ℝ → ℝ} (hH : Continuous H)
    {a b c d m : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hbnd : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, m ≤ H (x, y)) :
    (b - a) * (d - c) * m ≤ ∫ x in a..b, ∫ y in c..d, H (x, y) := by
  have hinner (x : ℝ) (hx : x ∈ Icc a b) : (d - c) * m ≤ ∫ y in c..d, H (x, y) := by
    have hi : IntervalIntegrable (fun y ↦ H (x, y)) volume c d :=
      (hH.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      intervalIntegral.integral_mono_on hcd intervalIntegrable_const hi (hbnd x hx)
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (intervalIntegrable_inner_of_continuous hH hab hcd) hinner
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_assoc] using h

theorem rectangle_integral_upper {H : ℝ × ℝ → ℝ} (hH : Continuous H)
    {a b c d M : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hbnd : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, H (x, y) ≤ M) :
    (∫ x in a..b, ∫ y in c..d, H (x, y)) ≤ (b - a) * (d - c) * M := by
  have h := rectangle_integral_lower hH.neg hab hcd (fun x hx y hy ↦ neg_le_neg (hbnd x hx y hy))
  simp only [Pi.neg_apply, intervalIntegral.integral_neg, mul_neg] at h
  exact neg_le_neg_iff.1 h

theorem iterated_intervalIntegral_sub {H K : ℝ × ℝ → ℝ} (hH : Continuous H) (hK : Continuous K)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, (H (x, y) - K (x, y))) =
      (∫ x in a..b, ∫ y in c..d, H (x, y)) - ∫ x in a..b, ∫ y in c..d, K (x, y) := by
  have hiH (x : ℝ) : IntervalIntegrable (fun y ↦ H (x, y)) volume c d :=
    (hH.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hiK (x : ℝ) : IntervalIntegrable (fun y ↦ K (x, y)) volume c d :=
    (hK.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  simp_rw [intervalIntegral.integral_sub (hiH _) (hiK _)]
  exact intervalIntegral.integral_sub (intervalIntegrable_inner_of_continuous hH hab hcd)
    (intervalIntegrable_inner_of_continuous hK hab hcd)

namespace UniformGrid

theorem cell_width {n : ℕ} (hn : 0 < n) (i : ℕ) : point n (i + 1) - point n i = 1 / n := by
  unfold point
  push_cast
  field_simp
  ring

theorem integral_bounds {H : ℝ × ℝ → ℝ} (hH : Continuous H) {n : ℕ} (hn : 0 < n)
    (lower upper : ℕ → ℕ → ℝ)
    (hbnd : ∀ i < n, ∀ j < n, ∀ p ∈ cell n i j, lower i j ≤ H p ∧ H p ≤ upper i j) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, area n * lower i j) ≤
      (∫ x in 0..1, ∫ y in 0..1, H (x, y)) ∧
    (∫ x in 0..1, ∫ y in 0..1, H (x, y)) ≤
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, area n * upper i j := by
  rw [integral_unitSquare_eq_sum hH hn]
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have h := rectangle_integral_lower hH (point_mono n (Nat.le_succ i)) (point_mono n (Nat.le_succ j))
      (fun x hx y hy ↦ (hbnd i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) (x, y) ⟨hx, hy⟩).1)
    simpa only [cell_width hn, area, one_div, inv_pow, pow_two, mul_inv_rev, mul_assoc] using h
  · apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have h := rectangle_integral_upper hH (point_mono n (Nat.le_succ i)) (point_mono n (Nat.le_succ j))
      (fun x hx y hy ↦ (hbnd i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) (x, y) ⟨hx, hy⟩).2)
    simpa only [cell_width hn, area, one_div, inv_pow, pow_two, mul_inv_rev, mul_assoc] using h

/-- Integrate signed secant bounds cell by cell. This needs no exchange of
differentiation and integration. -/
theorem integral_sub_bounds {H K : ℝ × ℝ → ℝ} (hH : Continuous H) (hK : Continuous K)
    {n : ℕ} (hn : 0 < n) (lower upper : ℕ → ℕ → ℝ) (delta : ℝ)
    (hbnd : ∀ i < n, ∀ j < n, ∀ p ∈ cell n i j,
      lower i j * delta ≤ H p - K p ∧ H p - K p ≤ upper i j * delta) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, area n * lower i j) * delta ≤
      (∫ x in 0..1, ∫ y in 0..1, H (x, y)) - (∫ x in 0..1, ∫ y in 0..1, K (x, y)) ∧
    (∫ x in 0..1, ∫ y in 0..1, H (x, y)) - (∫ x in 0..1, ∫ y in 0..1, K (x, y)) ≤
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, area n * upper i j) * delta := by
  have h := integral_bounds (hH.sub hK) hn (fun i j ↦ lower i j * delta) (fun i j ↦ upper i j * delta) hbnd
  simp only [Pi.sub_apply, ← mul_assoc, ← Finset.sum_mul] at h
  rw [iterated_intervalIntegral_sub hH hK (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)] at h
  exact h

end UniformGrid
end BlaschkeLebesgue
