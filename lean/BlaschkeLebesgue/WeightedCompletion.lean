module

public import BlaschkeLebesgue.AntipodalCompletion
public import BlaschkeLebesgue.ClippedBodies

/-!
# The weighted antipodal completion bound

The integrated curvature inequality, antipodal pairing, the Blaschke identity,
and the complementary-body coefficient identities together prove the weighted
completion bound for actual convex bodies. The clipped-body corollary constructs
all of its inputs from the original constant-width body and contact set.
-/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue

/-- The weighted completion proposition, with actual volume and spherical curvature densities. -/
theorem weighted_completion_bound {C D K : ConvexBody Space}
    (hCD : C + reflectBody D = unitBallBody) (hK : HasConstantWidth K 1)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hC0 : (0 : Space) ∈ interior (C : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) :
    (47 * bodyVolume D - bodyVolume C) / 46 + (4 / 23 : ℝ) *
      (∫ u : UnitSphere, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure) ≤
        bodyVolume K := by
  have hD : D + reflectBody C = unitBallBody := by
    have h := congrArg reflectBody hCD
    change reflectBody (C + reflectBody D) = reflectBody unitBallBody at h
    rw [reflectBody_add, reflectBody_reflectBody, reflectBody_unitBallBody] at h
    simpa only [add_comm] using h
  have hK0 := interior_mono hDK hD0
  have h := completion_antipodal_integral_lower hD hK hDK hD0
  rw [integral_missingWidth hD hK, (hK.blaschke_identity hK0).1] at h
  have hm := mean_coefficient_variation hD hK.add_reflectBody hDK hD0
  rw [(hK.blaschke_identity hK0).2] at hm
  obtain ⟨hv, hs, hmean⟩ := complementary_volume_coefficients hCD hC0 hD0
  linarith only [h, hm, hv, hs, hmean]

/-- Apply the proved inequality to the actual clipped outer body and its forced inner body. -/
theorem HasConstantWidth.clipped_weighted_completion {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) {R : ℝ} {Y : Set Space}
    (hY : Y ⊆ (K : Set Space)) (hbound : ∀ x ∈ K, ‖x‖ ≤ R) (hR : R < 1) :
    let hne := hK.clippedOuter_nonempty hY hbound
    let C := clippedOuterBody R Y hne
    let D := clippedInnerBody R Y hne hR.le
    (47 * bodyVolume D - bodyVolume C) / 46 + (4 / 23 : ℝ) *
      (∫ u : UnitSphere, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure) ≤
        bodyVolume K := by
  dsimp only
  exact weighted_completion_bound
    (clippedBodies_complement R Y (hK.clippedOuter_nonempty hY hbound) hR.le) hK
    (hK.clippedBodies_sandwich hY hbound _ hR.le).1
    (hK.clippedOuterBody_zero_mem_interior hY hbound hR _)
    (clippedInnerBody_zero_mem_interior R Y _ hR)

end BlaschkeLebesgue
