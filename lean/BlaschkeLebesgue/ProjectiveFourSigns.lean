module

public import BlaschkeLebesgue.ProjectiveCompletionLower
public import BlaschkeLebesgue.CompletionObliquity

/-!
# The four-sign lower bound before integration

This is a pointwise inequality for the actual completion weight with the
explicit projective area factor. The change-of-variables theorem identifying
its integral with a spherical integral is a separate obligation.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def projectiveCompletionIntegrand (D : ConvexBody Space) (f : ObliqueFrame) (x y : ℝ) : ℝ :=
  missingWidth D (f.projectiveUnitNormal x y) * antipodalCompletionWeight D (f.projectiveUnitNormal x y) /
    (f.sine * Real.sqrt (f.W x y) ^ 3)

namespace BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem projective_completion_pair_density_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space))
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    2 * Completion.phi (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
        (Completion.determinantFactor (edgeBudget c) x y) (f.W x y) / f.sine ≤
      projectiveCompletionIntegrand D f x y + projectiveCompletionIntegrand D f (-x) (-y) := by
  have h := div_le_div_of_nonneg_right
    (projective_completion_pair_lower c f h1 h2 hA hside1 hside2 hbound hK hDK hx hy)
    (mul_nonneg f.sine_pos.le (pow_nonneg (Real.sqrt_nonneg (f.W x y)) 3))
  dsimp only at h ⊢
  unfold projectiveCompletionIntegrand
  rw [f.W_neg]
  simp only [Completion.phi, projectiveDetLower] at h ⊢
  convert h using 1 <;> ring

theorem projective_completion_four_sign_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space))
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    4 * Completion.phi (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
        (Completion.determinantFactor (edgeBudget c) x y) (Completion.uniformW (edgeBudget c) (crossBudget c) x y) ≤
      projectiveCompletionIntegrand D f x y + projectiveCompletionIntegrand D f (-x) (-y) +
        projectiveCompletionIntegrand D f x (-y) + projectiveCompletionIntegrand D f (-x) y := by
  have hp := projective_completion_pair_density_lower c f h1 h2 hA hside1 hside2 hbound hK hDK hx hy
  have hy' : |-y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c) := by simpa using hy
  have hn := projective_completion_pair_density_lower c f h1 h2 hA hside1 hside2 hbound hK hDK hx hy'
  dsimp only at hp hn ⊢
  rw [neg_neg, Completion.allocationNumerator_neg_right, Completion.determinantFactor_neg_right] at hn
  have hj := div_le_div_of_nonneg_right (projective_phi_sign_average_lower c f h1 h2 hA x y) f.sine_pos.le
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have ho := Completion.obliquity_bounds (edgeBudget_nonneg c) (crossBudget_nonneg c) hab
  have hgeo : 1 + max (x ^ 2) (y ^ 2) ≤ Completion.uniformW (edgeBudget c) (crossBudget c) x y := by
    apply Completion.averagedW_ge
    rw [abs_of_nonneg ho.1]
    linarith [ho.2]
  have hnonneg := Completion.phi_nonneg
    (N := Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
    (Completion.determinantFactor_sqrt_lower (edgeBudget_nonneg c) x y hgeo)
  have hs1 : f.sine ≤ 1 := by nlinarith [f.sine_sq, sq_nonneg f.chi, f.sine_pos]
  have hunit := (le_div_iff₀ f.sine_pos).2 (mul_le_of_le_one_right hnonneg hs1)
  simp only [add_div, mul_div_assoc] at hp hn hj
  linarith only [hp, hn, hj, hunit]

end BalancedContacts.Opposite
end BlaschkeLebesgue
