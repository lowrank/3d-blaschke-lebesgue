module

public import BlaschkeLebesgue.ProjectiveAllocation

/-!
# Exact pairing of rectangle coordinates

Changing both coordinate signs cancels the transverse midpoint term. The
common curvature lower bound applies to the actual smaller antipodal
determinant, including points where the lower bound is clamped to zero.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem projective_missingWidth_pair (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive : 0 < projectiveDetLower c f x y) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    missingWidth D (f.projectiveUnitNormal x y) + missingWidth D (f.projectiveUnitNormal (-x) (-y)) =
      2 * ((circleRadius c * Real.sqrt (1 + x ^ 2) + circleRadius (swapped c) * Real.sqrt (1 + y ^ 2) -
        ⟪separation c, f.normal⟫_ℝ) / Real.sqrt (f.W x y) - 1) := by
  have hp1 := hpositive.trans_le (projectiveDetLower_le_first c f x y)
  have hp2 := hpositive.trans_le (projectiveDetLower_le_second c f x y)
  have hx' : |-x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c) := by simpa using hx
  have hy' : |-y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c) := by simpa using hy
  have hp1' : 0 < 1 - projectiveRadiusTerm c f (-x) (-y) := by rw [projectiveRadiusTerm_neg]; exact hp1
  have hp2' : 0 < 1 - projectiveRadiusTerm (swapped c) f.swap (-y) (-x) := by
    rw [projectiveRadiusTerm_neg]; exact hp2
  dsimp only
  rw [projective_missingWidth c f h1 h2 hA hside1 hside2 hbound hx hy hp1 hp2,
    projective_missingWidth c f h1 h2 hA hside1 hside2 hbound hx' hy' hp1' hp2',
    projectiveTransverseError_neg, f.W_neg, neg_sq, neg_sq]
  ring

theorem projective_missingWidth_pair_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive : 0 < projectiveDetLower c f x y) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    2 * (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y / Real.sqrt (f.W x y) - 1) ≤
      missingWidth D (f.projectiveUnitNormal x y) + missingWidth D (f.projectiveUnitNormal (-x) (-y)) := by
  dsimp only
  rw [projective_missingWidth_pair c f h1 h2 hA hside1 hside2 hbound hx hy hpositive]
  have h := div_le_div_of_nonneg_right (projective_allocation_lower c f x y) (Real.sqrt_nonneg (f.W x y))
  linarith

theorem projective_antipodalCurvatureMin_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) :
    max (projectiveDetLower c f x y) 0 ≤
      antipodalCurvatureMin (clippedInnerBody c.radius (Set.range c.point) hne hbound)
        (f.projectiveUnitNormal x y) := by
  by_cases hp : 0 < projectiveDetLower c f x y
  · rw [max_eq_left hp.le, antipodalCurvatureMin,
      projective_clipped_opposite_complement_det c f h1 h2 hA hside2 hbound hy
        (hp.trans_le (projectiveDetLower_le_second c f x y)),
      projective_clipped_complement_det c f h1 h2 hA hside1 hbound hx
        (hp.trans_le (projectiveDetLower_le_first c f x y))]
    exact le_min (projectiveDetLower_le_second c f x y) (projectiveDetLower_le_first c f x y)
  · rw [max_eq_right (le_of_not_gt hp), antipodalCurvatureMin]
    have hD : clippedInnerBody c.radius (Set.range c.point) hne hbound +
        reflectBody (clippedOuterBody c.radius (Set.range c.point) hne) = unitBallBody := by
      have h := congrArg reflectBody (clippedBodies_complement c.radius (Set.range c.point) hne hbound)
      rw [reflectBody_add, reflectBody_reflectBody, reflectBody_unitBallBody] at h
      simpa only [add_comm] using h
    exact le_min (curvatureDet_bounds hD _).1 (curvatureDet_bounds hD _).1

theorem projective_weight_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) :
    Completion.q (max (projectiveDetLower c f x y) 0) ≤
      antipodalCompletionWeight (clippedInnerBody c.radius (Set.range c.point) hne hbound)
        (f.projectiveUnitNormal x y) :=
  (Completion.q_le_psi _).trans (Completion.psi_monotone
    (projective_antipodalCurvatureMin_lower c f h1 h2 hA hside1 hside2 hbound hx hy))

end BlaschkeLebesgue.BalancedContacts.Opposite
