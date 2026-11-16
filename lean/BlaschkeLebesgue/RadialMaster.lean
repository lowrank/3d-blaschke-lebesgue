module

public import BlaschkeLebesgue.BlaschkeIdentity
public import BlaschkeLebesgue.ParallelVolume
public import BlaschkeLebesgue.Normalization

/-!
# The radial master inequality for actual convex bodies

The proved derivative of actual parallel volume and the radial expansion bound
give the flux inequality. The integrated tangent identity then gives the
manuscript's radial master inequality, with no smoothness or area interface.
-/

public noncomputable section

open MeasureTheory

namespace BlaschkeLebesgue

theorem HasConstantWidth.radial_flux_lower {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) :
    2 * bodyVolume K + 2 * Real.pi / 3 ≤ radialFluxIntegral K m :=
  hK.parallelBody_deriv_le_of_hasDerivWithinAt h0 hR hbound hm hmR
    (hK.parallelBody_volume_derivative h0)

theorem HasConstantWidth.radial_master {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) (t : ℝ) :
    2 * Real.pi / 3 - 4 * Real.pi * Radial.intercept m t +
      (∫ u : UnitSphere, Radial.gap m t (radialFunction K u) ∂sphereMeasure) ≤
        (3 * Radial.slope m t - 2) * bodyVolume K := by
  have hflux := hK.radial_flux_lower h0 hR hbound hm hmR
  have hgap := integral_radial_gap_eq h0 hm t
  change (∫ u : UnitSphere, Radial.gap m t (radialFunction K u) ∂sphereMeasure) =
    3 * Radial.slope m t * bodyVolume K + 4 * Real.pi * Radial.intercept m t -
      radialFluxIntegral K m at hgap
  nlinarith only [hflux, hgap]

theorem HasConstantWidth.radial_master_div {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m t : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) (hden : 0 < 3 * Radial.slope m t - 2) :
    (2 * Real.pi / 3 - 4 * Real.pi * Radial.intercept m t +
      (∫ u : UnitSphere, Radial.gap m t (radialFunction K u) ∂sphereMeasure)) /
        (3 * Radial.slope m t - 2) ≤ bodyVolume K := by
  apply (div_le_iff₀ hden).2
  simpa only [mul_comm (bodyVolume K)] using hK.radial_master h0 hR hbound hm hmR t

theorem HasConstantWidth.radial_master_without_gap {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m t : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) (ht : 0 ≤ t) :
    2 * Real.pi / 3 - 4 * Real.pi * Radial.intercept m t ≤
      (3 * Radial.slope m t - 2) * bodyVolume K := by
  have hgap : 0 ≤ ∫ u : UnitSphere, Radial.gap m t (radialFunction K u) ∂sphereMeasure :=
    integral_nonneg (fun u => Radial.gap_nonneg hm ht (radialFunction_pos h0 u.ne_zero).le)
  have h := hK.radial_master h0 hR hbound hm hmR t
  linarith only [hgap, h]

/-- The low-radius branch now bounds the volume of the original body. -/
theorem MinimumEnclosingBall.volume_gt_of_radius_le_three_fifths {K : ConvexBody Space}
    (b : MinimumEnclosingBall K) (hK : HasConstantWidth K 1) (hR : b.radius ≤ 3 / 5) :
    (259 / 625 : ℝ) < bodyVolume K := by
  have hmR : (16 / 25 : ℝ) ≤ 1 - b.radius ^ 2 := by nlinarith [b.radius_nonneg]
  have h := (b.centeredBody_width hK).radial_master_without_gap
    (b.centeredBody_zero_mem_interior hK) b.radius_nonneg (fun _ hx => b.centeredBody_norm_le hx)
    (by norm_num : (0 : ℝ) < 16 / 25) hmR (by norm_num : (0 : ℝ) ≤ 37 / 80)
  have hvol := Radial.low_radius_from_master h
  simpa only [MinimumEnclosingBall.centeredBody, bodyVolume_translateBody] using hvol

end BlaschkeLebesgue
