module

public import BlaschkeLebesgue.ProjectivePairing

/-!
# A pointwise paired lower bound for the actual completion integrand

The sign pair is taken in the projective rectangle. Its transverse error
cancels, the shared deficit budget supplies the coupled radius lower bound,
and nonnegative missing width permits the positive-part clamp. No support
formula is used outside the region where positive curvature proves it valid.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem projective_completion_pair_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space))
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    2 * max (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y / Real.sqrt (f.W x y) - 1) 0 *
      Completion.q (max (projectiveDetLower c f x y) 0) ≤
      missingWidth D (f.projectiveUnitNormal x y) * antipodalCompletionWeight D (f.projectiveUnitNormal x y) +
        missingWidth D (f.projectiveUnitNormal (-x) (-y)) *
          antipodalCompletionWeight D (f.projectiveUnitNormal (-x) (-y)) := by
  dsimp only
  have hg1 := missingWidth_nonneg hK hDK (f.projectiveUnitNormal x y)
  have hg2 := missingWidth_nonneg hK hDK (f.projectiveUnitNormal (-x) (-y))
  have hq := projective_q_nonneg c f x y
  have hw1 := projective_weight_lower c f h1 h2 hA hside1 hside2 (hne := hne) hbound hx hy
  have hx' : |-x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c) := by simpa using hx
  have hy' : |-y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c) := by simpa using hy
  have hw2 := projective_weight_lower c f h1 h2 hA hside1 hside2 (hne := hne) hbound hx' hy'
  rw [projectiveDetLower_neg] at hw2
  have hp1 := mul_le_mul_of_nonneg_left hw1 hg1
  have hp2 := mul_le_mul_of_nonneg_left hw2 hg2
  by_cases hp : 0 < projectiveDetLower c f x y
  · have hg := projective_missingWidth_pair_lower c f h1 h2 hA hside1 hside2
      (hne := hne) hbound hx hy hp
    dsimp only at hg
    have hclamp :
        2 * max (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y / Real.sqrt (f.W x y) - 1) 0 ≤
          missingWidth (clippedInnerBody c.radius (Set.range c.point) hne hbound) (f.projectiveUnitNormal x y) +
            missingWidth (clippedInnerBody c.radius (Set.range c.point) hne hbound) (f.projectiveUnitNormal (-x) (-y)) := by
      by_cases hgap : 0 ≤ Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y / Real.sqrt (f.W x y) - 1
      · rw [max_eq_left hgap]
        exact hg
      · rw [max_eq_right (le_of_not_ge hgap), mul_zero]
        exact add_nonneg hg1 hg2
    have h := mul_le_mul_of_nonneg_right hclamp hq
    nlinarith only [h, hp1, hp2]
  · rw [max_eq_right (le_of_not_gt hp), Completion.q]
    norm_num
    exact add_nonneg (mul_nonneg hg1 (hq.trans hw1)) (mul_nonneg hg2 (hq.trans hw2))

/-- All hypotheses are supplied by the original constant-width body, its actual
contact points, and the proved rectangle construction. -/
theorem projective_completion_pair_lower_of_contacts
    (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hcontacts : Set.range c.point ⊆ (K : Set Space)) (hball : ∀ p ∈ K, ‖p‖ ≤ c.radius)
    (hbound : c.radius ≤ 1) {x y : ℝ}
    (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) :
    let hne := hK.clippedOuter_nonempty hcontacts hball
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    2 * max (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y / Real.sqrt (f.W x y) - 1) 0 *
      Completion.q (max (projectiveDetLower c f x y) 0) ≤
      missingWidth D (f.projectiveUnitNormal x y) * antipodalCompletionWeight D (f.projectiveUnitNormal x y) +
        missingWidth D (f.projectiveUnitNormal (-x) (-y)) *
          antipodalCompletionWeight D (f.projectiveUnitNormal (-x) (-y)) := by
  dsimp only
  exact projective_completion_pair_lower c f h1 h2 hA hside1 hside2 hbound hK
    (hK.clippedBodies_sandwich hcontacts hball _ hbound).1 hx hy

end BlaschkeLebesgue.BalancedContacts.Opposite
