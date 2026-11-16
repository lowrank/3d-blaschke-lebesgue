module

public import BlaschkeLebesgue.RectangleSignIntegration

/-!
# A lower bound on the actual positive-curvature spherical patch

All integrability hypotheses are proved for the actual clipped bodies. The
parameter integral retains only the region on which both circle normal-cone
conditions hold, so this estimate can subsequently be summed over disjoint
edge-pair regions.
-/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

namespace Completion

@[expose] def rectangleIntegral (a b : ℝ) : ℝ :=
  ∫ p in {p : ℝ × ℝ | |p.1| < rectangleRadius a b ∧ |p.2| < rectangleRadius a b},
    uniformDensity a b p.1 p.2

theorem rectangleIntegral_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    0 ≤ rectangleIntegral a b :=
  integral_nonneg (fun p ↦ uniformDensity_nonneg ha hb hab p.1 p.2)

end Completion

namespace BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem integral_active_projective_completion (D : ConvexBody Space) :
    (∫ u in f.projectivePatch (activeProjectiveRegion c f),
      missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure) =
      ∫ p in projectiveRectangle c, activeProjectiveIntegrand c f D p.1 p.2 := by
  rw [f.integral_projective_completion D (measurableSet_activeProjectiveRegion c f)]
  exact (setIntegral_indicator (s := projectiveRectangle c)
    (f := fun p : ℝ × ℝ ↦ projectiveCompletionIntegrand D f p.1 p.2)
    (measurableSet_positiveProjectiveCurvature c f)).symm

theorem active_projective_completion_integral_lower
    (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space)) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    Completion.rectangleIntegral (edgeBudget c) (crossBudget c) ≤
      ∫ u in f.projectivePatch (activeProjectiveRegion c f),
        missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure := by
  dsimp only
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have hD : clippedInnerBody c.radius (Set.range c.point) hne hbound +
      reflectBody (clippedOuterBody c.radius (Set.range c.point) hne) = unitBallBody := by
    have h := congrArg reflectBody (clippedBodies_complement c.radius (Set.range c.point) hne hbound)
    change reflectBody (_ + _) = reflectBody unitBallBody at h
    rw [reflectBody_add, reflectBody_reflectBody, reflectBody_unitBallBody] at h
    simpa only [add_comm] using h
  rw [integral_active_projective_completion]
  apply integral_rectangle_le_of_four_sign
  · exact integrableOn_abs_rectangle
      (Completion.continuous_uniformDensity (edgeBudget_nonneg c) (crossBudget_nonneg c) hab) _
  · exact integrableOn_activeProjectiveIntegrand c f hD
  · intro p hx hy
    exact active_projective_four_sign_lower c f h1 h2 hA hside1 hside2 hbound hK hDK hx hy

theorem active_projective_completion_integral_lower_of_contacts
    (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hcontacts : Set.range c.point ⊆ (K : Set Space)) (hball : ∀ p ∈ K, ‖p‖ ≤ c.radius)
    (hbound : c.radius ≤ 1) :
    let hne := hK.clippedOuter_nonempty hcontacts hball
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    Completion.rectangleIntegral (edgeBudget c) (crossBudget c) ≤
      ∫ u in f.projectivePatch (activeProjectiveRegion c f),
        missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure := by
  dsimp only
  exact active_projective_completion_integral_lower c f h1 h2 hA hside1 hside2 hbound hK
    (hK.clippedBodies_sandwich hcontacts hball _ hbound).1

end BalancedContacts.Opposite
end BlaschkeLebesgue
