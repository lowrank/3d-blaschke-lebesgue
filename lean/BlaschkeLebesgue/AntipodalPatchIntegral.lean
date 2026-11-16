module

public import BlaschkeLebesgue.RectangleQuadrantIntegral

/-! # The two actual antipodal patches contribute at least twice the scalar integral -/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem missingWidth_even (D : ConvexBody Space) (u : UnitSphere) :
    missingWidth D (sphereAntipode u) = missingWidth D u := by
  unfold missingWidth
  rw [sphereAntipode_involutive]
  ring

theorem integral_antipodal_union {h : UnitSphere → ℝ} (hi : Integrable h sphereMeasure)
    (he : ∀ u, h (sphereAntipode u) = h u) {s : Set UnitSphere}
    (hs : MeasurableSet s) (hd : Disjoint s (sphereAntipode '' s)) :
    (∫ u in s ∪ sphereAntipode '' s, h u ∂sphereMeasure) = 2 * ∫ u in s, h u ∂sphereMeasure := by
  rw [setIntegral_union hd (sphereAntipode.measurableEmbedding.measurableSet_image.2 hs)
    hi.integrableOn hi.integrableOn,
    sphereAntipode_measurePreserving.setIntegral_image_emb sphereAntipode.measurableEmbedding h s]
  simp_rw [he]
  ring

namespace BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

@[expose] def activeAntipodalPatches : Set UnitSphere :=
  f.projectivePatch (activeProjectiveRegion c f) ∪
    sphereAntipode '' f.projectivePatch (activeProjectiveRegion c f)

theorem measurableSet_activeAntipodalPatches : MeasurableSet (activeAntipodalPatches c f) := by
  have hs := f.measurableSet_projectivePatch (measurableSet_activeProjectiveRegion c f)
  exact hs.union (sphereAntipode.measurableEmbedding.measurableSet_image.2 hs)

theorem integral_activeAntipodalPatches {D D' : ConvexBody Space} (hD : D + D' = unitBallBody) :
    (∫ u in activeAntipodalPatches c f, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure) =
      2 * ∫ u in f.projectivePatch (activeProjectiveRegion c f),
        missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure := by
  apply integral_antipodal_union (integrable_missingWidth_weight hD)
  · intro u
    rw [missingWidth_even, antipodalCompletionWeight_even]
  · exact f.measurableSet_projectivePatch (measurableSet_activeProjectiveRegion c f)
  · exact f.projectivePatch_disjoint_antipode _ _

theorem active_antipodal_completion_integral_lower
    (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space)) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    2 * Completion.F (edgeBudget c) (crossBudget c) ≤
      ∫ u in activeAntipodalPatches c f, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure := by
  dsimp only
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have hD : clippedInnerBody c.radius (Set.range c.point) hne hbound +
      reflectBody (clippedOuterBody c.radius (Set.range c.point) hne) = unitBallBody := by
    have h := congrArg reflectBody (clippedBodies_complement c.radius (Set.range c.point) hne hbound)
    change reflectBody (_ + _) = reflectBody unitBallBody at h
    rw [reflectBody_add, reflectBody_reflectBody, reflectBody_unitBallBody] at h
    simpa only [add_comm] using h
  rw [integral_activeAntipodalPatches c f hD]
  have h := active_projective_completion_integral_lower c f h1 h2 hA hside1 hside2 hbound hK hDK
  rw [Completion.rectangleIntegral_eq_F (edgeBudget_nonneg c) (crossBudget_nonneg c) hab] at h
  linarith only [h]

end BalancedContacts.Opposite
end BlaschkeLebesgue
