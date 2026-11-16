module

public import BlaschkeLebesgue.ObliqueFrame
public import BlaschkeLebesgue.ContactArcCenter

/-! # Midpoint alignment estimates for the actual opposite contact edges -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)
  (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)

include h1 h2

theorem frame_sine_lower (hA : c.totalDeficit ≤ 2 / 25) :
    Real.sqrt (1 - Completion.obliquity (edgeBudget c) (crossBudget c) ^ 2) ≤ f.sine := by
  have ha : edgeBudget c < 1 := by linarith [budgets_sum c, crossBudget_nonneg c]
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have hb := Completion.obliquity_bounds (edgeBudget_nonneg c) (crossBudget_nonneg c) hab
  have hc : |f.chi| ≤ Completion.obliquity (edgeBudget c) (crossBudget c) := by
    simpa only [ObliqueFrame.chi, h1, h2, Completion.obliquity] using axes_inner_abs c ha
  have hs := (sq_le_sq₀ (abs_nonneg _) hb.1).2 hc
  rw [sq_abs] at hs
  exact Real.sqrt_le_sqrt (by linarith)

theorem firstMidpoint_inner_transverse :
    ⟪firstMidpoint c, f.transverse₁⟫_ℝ = -⟪separation c, secondAxis c⟫_ℝ / f.sine := by
  have hsep : ⟪separation c, secondAxis c⟫_ℝ = -⟪firstMidpoint c, secondAxis c⟫_ℝ := by
    rw [separation, inner_sub_left, secondMidpoint_inner_axis, zero_sub]
  simp only [ObliqueFrame.transverse₁, h1, h2, real_inner_smul_right, inner_sub_right,
    firstMidpoint_inner_axis, mul_zero, sub_zero, hsep]
  ring

theorem secondMidpoint_inner_transverse :
    ⟪secondMidpoint c, f.transverse₂⟫_ℝ = -⟪separation c, firstAxis c⟫_ℝ / f.sine := by
  have hsep : ⟪separation c, firstAxis c⟫_ℝ = ⟪secondMidpoint c, firstAxis c⟫_ℝ := by
    rw [separation, inner_sub_left, firstMidpoint_inner_axis, sub_zero]
  simp only [ObliqueFrame.transverse₂, h1, h2, real_inner_smul_right, inner_sub_right,
    secondMidpoint_inner_axis, mul_zero, zero_sub, hsep]
  ring

theorem midpoint_transverse_bounds (hA : c.totalDeficit ≤ 2 / 25) :
    |⟪firstMidpoint c, f.transverse₁⟫_ℝ| ≤
      crossBudget c / (4 * Real.sqrt (1 - edgeBudget c) *
        Real.sqrt (1 - Completion.obliquity (edgeBudget c) (crossBudget c) ^ 2)) ∧
    |⟪secondMidpoint c, f.transverse₂⟫_ℝ| ≤
      crossBudget c / (4 * Real.sqrt (1 - edgeBudget c) *
        Real.sqrt (1 - Completion.obliquity (edgeBudget c) (crossBudget c) ^ 2)) := by
  have ha : edgeBudget c < 1 := by linarith [budgets_sum c, crossBudget_nonneg c]
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have hc := Completion.obliquity_bounds (edgeBudget_nonneg c) (crossBudget_nonneg c) hab
  have hd : 0 < Real.sqrt (1 - Completion.obliquity (edgeBudget c) (crossBudget c) ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg (Completion.obliquity (edgeBudget c) (crossBudget c) - 1 / 25)]
  have hlower := frame_sine_lower c f h1 h2 hA
  have hnum : 0 ≤ crossBudget c / (4 * Real.sqrt (1 - edgeBudget c)) :=
    div_nonneg (crossBudget_nonneg c) (by positivity)
  constructor
  · rw [firstMidpoint_inner_transverse c f h1 h2, abs_div, abs_neg, abs_of_pos f.sine_pos]
    simpa only [div_div] using div_le_div₀ hnum (separation_inner_secondAxis_abs c ha) hd hlower
  · rw [secondMidpoint_inner_transverse c f h1 h2, abs_div, abs_neg, abs_of_pos f.sine_pos]
    simpa only [div_div] using div_le_div₀ hnum (separation_inner_firstAxis_abs c ha) hd hlower

theorem normalized_midpoint_transverse_bounds (hA : c.totalDeficit ≤ 2 / 25) :
    |⟪f.transverse₁, -NormedSpace.normalize (firstMidpoint c)⟫_ℝ| ≤
      Completion.midpointError (edgeBudget c) (crossBudget c) ∧
    |⟪f.transverse₂, NormedSpace.normalize (secondMidpoint c)⟫_ℝ| ≤
      Completion.midpointError (edgeBudget c) (crossBudget c) := by
  have hmid := midpoint_transverse_bounds c f h1 h2 hA
  have hm : 0 < Real.sqrt (1 / 8 - c.totalDeficit / 16) := by
    apply Real.sqrt_pos.2
    linarith
  have hm1 : Real.sqrt (1 / 8 - c.totalDeficit / 16) ≤ ‖firstMidpoint c‖ :=
    (Real.sqrt_le_left (norm_nonneg _)).2 (firstMidpoint_norm_sq_lower c)
  have hm2 : Real.sqrt (1 / 8 - c.totalDeficit / 16) ≤ ‖secondMidpoint c‖ :=
    (Real.sqrt_le_left (norm_nonneg _)).2 (secondMidpoint_norm_sq_lower c)
  have hnum : 0 ≤ crossBudget c / (4 * Real.sqrt (1 - edgeBudget c) *
      Real.sqrt (1 - Completion.obliquity (edgeBudget c) (crossBudget c) ^ 2)) :=
    div_nonneg (crossBudget_nonneg c) (by positivity)
  have heq1 : |⟪f.transverse₁, -NormedSpace.normalize (firstMidpoint c)⟫_ℝ| =
      |⟪firstMidpoint c, f.transverse₁⟫_ℝ| / ‖firstMidpoint c‖ := by
    simp only [NormedSpace.normalize, inner_neg_right, real_inner_smul_right,
      abs_neg, abs_mul, abs_inv, abs_norm, real_inner_comm (firstMidpoint c) f.transverse₁]
    ring
  have heq2 : |⟪f.transverse₂, NormedSpace.normalize (secondMidpoint c)⟫_ℝ| =
      |⟪secondMidpoint c, f.transverse₂⟫_ℝ| / ‖secondMidpoint c‖ := by
    simp only [NormedSpace.normalize, real_inner_smul_right, abs_mul, abs_inv,
      abs_norm, real_inner_comm (secondMidpoint c) f.transverse₂]
    ring
  constructor
  · rw [heq1]
    simpa only [Completion.midpointError, div_div, budgets_sum] using div_le_div₀ hnum hmid.1 hm hm1
  · rw [heq2]
    simpa only [Completion.midpointError, div_div, budgets_sum] using div_le_div₀ hnum hmid.2 hm hm2

theorem firstMidpoint_normal_alignment (hA : c.totalDeficit ≤ 2 / 25)
    (hside : ⟪firstMidpoint c, f.normal⟫_ℝ < 0) :
    Real.sqrt (1 - Completion.midpointError (edgeBudget c) (crossBudget c) ^ 2) ≤
      ⟪f.normal, -NormedSpace.normalize (firstMidpoint c)⟫_ℝ := by
  have hm := firstMidpoint_norm_pos c hA
  apply f.normal_alignment_first (arcCenterDirection_norm c hA)
  · simp only [arcCenterDirection, h1, NormedSpace.normalize, inner_neg_right, real_inner_smul_right,
      real_inner_comm (firstMidpoint c) (firstAxis c), firstMidpoint_inner_axis, mul_zero, neg_zero]
  · simp only [arcCenterDirection, NormedSpace.normalize, inner_neg_right, real_inner_smul_right,
      real_inner_comm (firstMidpoint c) f.normal]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hm.le) hside.le)
  · exact (normalized_midpoint_transverse_bounds c f h1 h2 hA).1

theorem secondMidpoint_normal_alignment (hA : c.totalDeficit ≤ 2 / 25)
    (hside : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ) :
    Real.sqrt (1 - Completion.midpointError (edgeBudget c) (crossBudget c) ^ 2) ≤
      ⟪f.normal, NormedSpace.normalize (secondMidpoint c)⟫_ℝ := by
  have hm : 0 < ‖secondMidpoint c‖ := by
    nlinarith [secondMidpoint_norm_sq_lower c, norm_nonneg (secondMidpoint c)]
  apply f.normal_alignment_second (NormedSpace.norm_normalize (norm_pos_iff.mp hm))
  · simp only [h2, NormedSpace.normalize, real_inner_smul_right,
      real_inner_comm (secondMidpoint c) (secondAxis c), secondMidpoint_inner_axis, mul_zero]
  · simp only [NormedSpace.normalize, real_inner_smul_right,
      real_inner_comm (secondMidpoint c) f.normal]
    exact mul_nonneg (inv_nonneg.mpr hm.le) hside.le
  · exact (normalized_midpoint_transverse_bounds c f h1 h2 hA).2

end BlaschkeLebesgue.BalancedContacts.Opposite
