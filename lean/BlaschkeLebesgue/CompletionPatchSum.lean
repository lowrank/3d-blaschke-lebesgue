module

public import BlaschkeLebesgue.DisjointCompletionPatches
public import BlaschkeLebesgue.WeightedCompletion

/-!
# Summing the three actual opposite-edge completion contributions

The frames, patches, their disjointness, and all integrability facts are
constructed from the balanced contacts. The resulting volume inequality is
the analytic reduction to the scalar integral and clipped-body volume bounds.
-/

public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space)

theorem pairPatches_integral_lower (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space))
    (j : Fin 3) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    2 * Completion.F (pairEdgeBudget c j) (pairCrossBudget c j) ≤
      ∫ u in pairPatches c hA j, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure := by
  have hne' : (clippedOuter (c.relabel (partition j)).radius (Set.range (c.relabel (partition j)).point)).Nonempty := by
    rwa [c.clippedOuter_relabel]
  have hD' := c.clippedInnerBody_relabel (partition j) hne' hne hbound hbound
  have hDK' : (clippedInnerBody (c.relabel (partition j)).radius
      (Set.range (c.relabel (partition j)).point) hne' hbound : Set Space) ⊆ (K : Set Space) := by
    rw [hD']
    exact hDK
  have hf := pairFrame_spec c hA j
  have h := active_antipodal_completion_integral_lower (c.relabel (partition j)) (pairFrame c hA j)
    hf.1 hf.2.1 (partition_totalDeficit_le c hA j) hf.2.2.1 hf.2.2.2 hbound hK hDK'
  dsimp only at h ⊢
  rwa [hD'] at h

theorem completion_integral_ge_sum (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space)) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    2 * (∑ j : Fin 3, Completion.F (pairEdgeBudget c j) (pairCrossBudget c j)) ≤
      ∫ u : UnitSphere, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure := by
  dsimp only
  have hD : clippedInnerBody c.radius (Set.range c.point) hne hbound +
      reflectBody (clippedOuterBody c.radius (Set.range c.point) hne) = unitBallBody := by
    have h := congrArg reflectBody (clippedBodies_complement c.radius (Set.range c.point) hne hbound)
    change reflectBody (_ + _) = reflectBody unitBallBody at h
    rw [reflectBody_add, reflectBody_reflectBody, reflectBody_unitBallBody] at h
    simpa only [add_comm] using h
  have hi := integrable_missingWidth_weight hD
  have hnonneg : ∀ u : UnitSphere,
      0 ≤ missingWidth (clippedInnerBody c.radius (Set.range c.point) hne hbound) u *
        antipodalCompletionWeight (clippedInnerBody c.radius (Set.range c.point) hne hbound) u := fun u ↦
    mul_nonneg (missingWidth_nonneg hK hDK u) (antipodalCompletionWeight_bounds hD u).1
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ ↦ pairPatches_integral_lower c hA hbound hK hDK j)
  rw [← Finset.mul_sum] at hsum
  have hu := integral_iUnion_fintype (measurableSet_pairPatches c hA)
    (pairPatches_pairwise_disjoint c hA (hne := hne) hbound) (fun _ ↦ hi.integrableOn)
  rw [← hu] at hsum
  exact hsum.trans (setIntegral_le_integral hi (Filter.Eventually.of_forall hnonneg))

/-- The manuscript's weighted completion estimate with all three scalar
contributions justified by actual disjoint subsets of the sphere. -/
theorem clipped_volume_ge_completion_sum {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hcontacts : Set.range c.point ⊆ (K : Set Space)) (hball : ∀ p ∈ K, ‖p‖ ≤ c.radius)
    (hA : c.totalDeficit ≤ 2 / 25) (hbound : c.radius < 1) :
    let hne := hK.clippedOuter_nonempty hcontacts hball
    let C := clippedOuterBody c.radius (Set.range c.point) hne
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound.le
    (47 * bodyVolume D - bodyVolume C) / 46 + (8 / 23 : ℝ) *
      (∑ j : Fin 3, Completion.F (pairEdgeBudget c j) (pairCrossBudget c j)) ≤ bodyVolume K := by
  dsimp only
  have h := hK.clipped_weighted_completion hcontacts hball hbound
  have hs := completion_integral_ge_sum c hA (hne := hK.clippedOuter_nonempty hcontacts hball) hbound.le hK
    (hK.clippedBodies_sandwich hcontacts hball _ hbound.le).1
  dsimp only at h hs
  linarith only [h, hs]

end BlaschkeLebesgue.BalancedContacts.Opposite
