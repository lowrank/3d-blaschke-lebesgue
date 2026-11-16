module

public import BlaschkeLebesgue.ProjectiveClipping

/-! # Actual support and curvature formulas in the projective rectangles -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def ObliqueFrame.projectiveUnitNormal (f : ObliqueFrame) (x y : ℝ) : UnitSphere :=
  ⟨f.projectiveNormal x y, by simpa only [Metric.mem_sphere, dist_zero_right] using f.projectiveNormal_norm x y⟩

theorem ObliqueFrame.projectiveUnitNormal_val (f : ObliqueFrame) (x y : ℝ) :
    (f.projectiveUnitNormal x y : Space) = f.projectiveNormal x y := rfl

theorem ObliqueFrame.swap_projectiveUnitNormal (f : ObliqueFrame) (x y : ℝ) :
    f.swap.projectiveUnitNormal y x = sphereAntipode (f.projectiveUnitNormal x y) := by
  apply Subtype.ext
  exact f.swap_projectiveNormal x y

namespace BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

@[expose] def projectiveRadiusTerm (x y : ℝ) : ℝ :=
  circleRadius c * Real.sqrt (f.W x y) / Real.sqrt (1 + x ^ 2)

theorem projective_circleProjection_norm (h1 : f.axis₁ = firstAxis c) (x y : ℝ) :
    ‖circleProjection c (f.projectiveNormal x y)‖ =
      Real.sqrt (1 + x ^ 2) / Real.sqrt (f.W x y) := by
  change ‖tangentProjection (firstAxis c) (f.projectiveNormal x y)‖ = _
  rw [← h1, f.projectiveNormal_first_projection_norm]

theorem projectiveRadiusTerm_eq (h1 : f.axis₁ = firstAxis c) (x y : ℝ) :
    projectiveRadiusTerm c f x y = circleRadius c / ‖circleProjection c (f.projectiveNormal x y)‖ := by
  rw [projective_circleProjection_norm c f h1, projectiveRadiusTerm]
  field_simp

theorem projective_normalCone_of_positive (h1 : f.axis₁ = firstAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) {x y : ℝ}
    (hpositive : 0 < 1 - projectiveRadiusTerm c f x y) :
    |⟪firstAxis c, f.projectiveNormal x y⟫_ℝ| < ‖firstEdge c‖ / 2 := by
  have ha : edgeBudget c < 1 := by linarith [budgets_sum c, crossBudget_nonneg c]
  apply circle_normal_cone_of_positive_complement c ha (f.projectiveNormal_norm x y)
  · rw [projective_circleProjection_norm c f h1]
    exact div_pos (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_pos.2 (f.W_pos x y))
  · rwa [← projectiveRadiusTerm_eq c f h1]

theorem projective_circle_sqrt (h1 : f.axis₁ = firstAxis c) (ha : edgeBudget c < 1) (x y : ℝ) :
    Real.sqrt (1 - ⟪firstAxis c, f.projectiveNormal x y⟫_ℝ ^ 2) =
      Real.sqrt (1 + x ^ 2) / Real.sqrt (f.W x y) := by
  rw [← circleProjection_norm_sq c ha (f.projectiveNormal_norm x y),
    Real.sqrt_sq (norm_nonneg _), projective_circleProjection_norm c f h1]

/-- A positive complementary curvature term supplies the normal-cone condition;
the rectangle supplies all actual ball constraints. -/
theorem projective_clipped_support (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} {x y : ℝ}
    (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive : 0 < 1 - projectiveRadiusTerm c f x y) :
    support (clippedOuterBody c.radius (Set.range c.point) hne) (f.projectiveNormal x y) =
      ⟪f.projectiveNormal x y, firstMidpoint c⟫_ℝ +
        circleRadius c * Real.sqrt (1 + x ^ 2) / Real.sqrt (f.W x y) := by
  have ha : edgeBudget c < 1 := by linarith [budgets_sum c, crossBudget_nonneg c]
  have hcone := projective_normalCone_of_positive c f h1 hA hpositive
  have hmem := projective_circleCandidate_mem_clippedOuter c f h1 h2 hA hside hx y
  rw [clippedOuter_support_circle_formula c ha (f.projectiveNormal_norm x y) hcone.le hmem,
    projective_circle_sqrt c f h1 ha]
  ring

theorem projective_clipped_complement_det (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive : 0 < 1 - projectiveRadiusTerm c f x y) :
    curvatureDet (clippedInnerBody c.radius (Set.range c.point) hne hbound)
      (sphereAntipode (f.projectiveUnitNormal x y)) = 1 - projectiveRadiusTerm c f x y := by
  have ha : edgeBudget c < 1 := by linarith [budgets_sum c, crossBudget_nonneg c]
  have hcone := projective_normalCone_of_positive c f h1 hA hpositive
  have hR := projective_circleCandidate_inside_radius c f h1 h2 hA hside hx y
  rw [clipped_circle_complement_det_of_inside_radius c hA hbound (f.projectiveUnitNormal x y)
    hcone hR]
  rw [ObliqueFrame.projectiveUnitNormal_val, projective_circle_sqrt c f h1 ha,
    projectiveRadiusTerm]
  field_simp

theorem clippedOuterBody_swapped
    (hne' : (clippedOuter (swapped c).radius (Set.range (swapped c).point)).Nonempty)
    (hne : (clippedOuter c.radius (Set.range c.point)).Nonempty) :
    clippedOuterBody (swapped c).radius (Set.range (swapped c).point) hne' =
      clippedOuterBody c.radius (Set.range c.point) hne := by
  apply SetLike.ext
  intro x
  change x ∈ clippedOuter (swapped c).radius (Set.range (swapped c).point) ↔
    x ∈ clippedOuter c.radius (Set.range c.point)
  rw [swapped_clippedOuter]

theorem clippedInnerBody_swapped
    (hne' : (clippedOuter (swapped c).radius (Set.range (swapped c).point)).Nonempty)
    (hne : (clippedOuter c.radius (Set.range c.point)).Nonempty)
    (hbound' : (swapped c).radius ≤ 1) (hbound : c.radius ≤ 1) :
    clippedInnerBody (swapped c).radius (Set.range (swapped c).point) hne' hbound' =
      clippedInnerBody c.radius (Set.range c.point) hne hbound := by
  apply SetLike.ext
  intro x
  change x ∈ ballTransform (clippedOuterBody (swapped c).radius (Set.range (swapped c).point) hne' : Set Space) ↔
    x ∈ ballTransform (clippedOuterBody c.radius (Set.range c.point) hne : Set Space)
  rw [clippedOuterBody_swapped]

end BalancedContacts.Opposite
end BlaschkeLebesgue
