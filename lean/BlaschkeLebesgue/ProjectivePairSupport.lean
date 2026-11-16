module

public import BlaschkeLebesgue.ProjectiveCurvature
public import BlaschkeLebesgue.AntipodalCompletion

/-! # The actual support gap and opposite determinants in a projective rectangle -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem missingWidth_eq_complement_support {C D : ConvexBody Space}
    (hCD : C + reflectBody D = unitBallBody) (u : UnitSphere) :
    missingWidth D u = support C u + support C (-(u : Space)) - 1 := by
  have h1 : support C u + support D (-(u : Space)) = 1 := by
    rw [← support_reflectBody, ← support_add, hCD, support_unitBallBody u.norm_eq_one]
  have h2 : support C (-(u : Space)) + support D u = 1 := by
    have h := congrArg (fun K : ConvexBody Space ↦ support K (-(u : Space))) hCD
    simpa only [support_add, support_reflectBody, neg_neg,
      support_unitBallBody (n := -(u : Space))
        (by simpa only [norm_neg] using u.norm_eq_one)] using h
  unfold missingWidth
  rw [sphereAntipode_val]
  linarith

namespace BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem projective_clipped_opposite_support (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} {x y : ℝ}
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive : 0 < 1 - projectiveRadiusTerm (swapped c) f.swap y x) :
    support (clippedOuterBody c.radius (Set.range c.point) hne) (-f.projectiveNormal x y) =
      ⟪-f.projectiveNormal x y, secondMidpoint c⟫_ℝ +
        circleRadius (swapped c) * Real.sqrt (1 + y ^ 2) / Real.sqrt (f.W x y) := by
  have hne' : (clippedOuter (swapped c).radius (Set.range (swapped c).point)).Nonempty := by
    rw [swapped_clippedOuter]; exact hne
  have h1' : f.swap.axis₁ = firstAxis (swapped c) := by rw [swapped_firstAxis]; exact h2
  have h2' : f.swap.axis₂ = secondAxis (swapped c) := by rw [swapped_secondAxis]; exact h1
  have hA' : (swapped c).totalDeficit ≤ 2 / 25 := by rw [swapped_totalDeficit]; exact hA
  have hside' : ⟪firstMidpoint (swapped c), f.swap.normal⟫_ℝ < 0 := by
    rw [swapped_firstMidpoint]
    change ⟪secondMidpoint c, -f.normal⟫_ℝ < 0
    rw [inner_neg_right]
    linarith
  have hy' : |y| < Completion.rectangleRadius (edgeBudget (swapped c)) (crossBudget (swapped c)) := by
    simpa only [swapped_edgeBudget, swapped_crossBudget] using hy
  have h := projective_clipped_support (swapped c) f.swap h1' h2' hA' hside'
    (hne := hne') hy' hpositive
  simpa only [clippedOuterBody_swapped c hne' hne, f.swap_projectiveNormal,
    swapped_firstMidpoint, f.swap_W] using h

theorem projective_clipped_opposite_complement_det (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive : 0 < 1 - projectiveRadiusTerm (swapped c) f.swap y x) :
    curvatureDet (clippedInnerBody c.radius (Set.range c.point) hne hbound)
      (f.projectiveUnitNormal x y) = 1 - projectiveRadiusTerm (swapped c) f.swap y x := by
  have hne' : (clippedOuter (swapped c).radius (Set.range (swapped c).point)).Nonempty := by
    rw [swapped_clippedOuter]; exact hne
  have hbound' : (swapped c).radius ≤ 1 := hbound
  have h1' : f.swap.axis₁ = firstAxis (swapped c) := by rw [swapped_firstAxis]; exact h2
  have h2' : f.swap.axis₂ = secondAxis (swapped c) := by rw [swapped_secondAxis]; exact h1
  have hA' : (swapped c).totalDeficit ≤ 2 / 25 := by rw [swapped_totalDeficit]; exact hA
  have hside' : ⟪firstMidpoint (swapped c), f.swap.normal⟫_ℝ < 0 := by
    rw [swapped_firstMidpoint]
    change ⟪secondMidpoint c, -f.normal⟫_ℝ < 0
    rw [inner_neg_right]
    linarith
  have hy' : |y| < Completion.rectangleRadius (edgeBudget (swapped c)) (crossBudget (swapped c)) := by
    simpa only [swapped_edgeBudget, swapped_crossBudget] using hy
  have h := projective_clipped_complement_det (swapped c) f.swap h1' h2' hA' hside'
    (hne := hne') hbound' hy' hpositive
  simpa only [clippedInnerBody_swapped c hne' hne hbound' hbound,
    f.swap_projectiveUnitNormal, sphereAntipode_involutive] using h

@[expose] def projectiveTransverseError (x y : ℝ) : ℝ := ⟪separation c, f.planeVector x y⟫_ℝ

theorem projectiveTransverseError_neg (x y : ℝ) :
    projectiveTransverseError c f (-x) (-y) = -projectiveTransverseError c f x y := by
  simp only [projectiveTransverseError, f.planeVector_neg, inner_neg_right]

/-- The manuscript's gap formula, for the actual forced inner body. -/
theorem projective_missingWidth (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive1 : 0 < 1 - projectiveRadiusTerm c f x y)
    (hpositive2 : 0 < 1 - projectiveRadiusTerm (swapped c) f.swap y x) :
    missingWidth (clippedInnerBody c.radius (Set.range c.point) hne hbound)
      (f.projectiveUnitNormal x y) =
      (circleRadius c * Real.sqrt (1 + x ^ 2) + circleRadius (swapped c) * Real.sqrt (1 + y ^ 2) -
        ⟪separation c, f.normal⟫_ℝ - projectiveTransverseError c f x y) / Real.sqrt (f.W x y) - 1 := by
  rw [missingWidth_eq_complement_support
    (clippedBodies_complement c.radius (Set.range c.point) hne hbound)]
  rw [ObliqueFrame.projectiveUnitNormal_val,
    projective_clipped_support c f h1 h2 hA hside1 hx hpositive1,
    projective_clipped_opposite_support c f h1 h2 hA hside2 hy hpositive2]
  rw [inner_neg_left]
  have hinner : ⟪f.projectiveNormal x y, firstMidpoint c⟫_ℝ -
      ⟪f.projectiveNormal x y, secondMidpoint c⟫_ℝ =
      -(⟪separation c, f.normal⟫_ℝ + projectiveTransverseError c f x y) / Real.sqrt (f.W x y) := by
    rw [← inner_sub_right, f.projectiveNormal_eq, real_inner_smul_left,
      inner_add_left, inner_sub_right, inner_sub_right]
    simp only [projectiveTransverseError, separation, inner_sub_left,
      real_inner_comm (firstMidpoint c) f.normal, real_inner_comm (secondMidpoint c) f.normal,
      real_inner_comm (firstMidpoint c) (f.planeVector x y),
      real_inner_comm (secondMidpoint c) (f.planeVector x y)]
    ring
  calc
    _ = (⟪f.projectiveNormal x y, firstMidpoint c⟫_ℝ -
        ⟪f.projectiveNormal x y, secondMidpoint c⟫_ℝ) +
        (circleRadius c * Real.sqrt (1 + x ^ 2) + circleRadius (swapped c) * Real.sqrt (1 + y ^ 2)) /
          Real.sqrt (f.W x y) - 1 := by ring
    _ = _ := by rw [hinner]; ring

end BalancedContacts.Opposite
end BlaschkeLebesgue
