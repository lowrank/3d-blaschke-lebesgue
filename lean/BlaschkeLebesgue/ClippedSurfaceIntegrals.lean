module

public import BlaschkeLebesgue.ClippedFaceCurvature
public import BlaschkeLebesgue.CurvatureIntegrals

/-!
# Actual surface area and volume from the spherical face regions

The area density is now identified with the five face indicators. Substitution
in the proved support-curvature formula gives the volume in terms of actual
cap-region areas and first moments, without any assumed divergence theorem
for a piecewise smooth boundary.
-/

public noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

variable (c : BalancedContacts 4 Space)
  {hne : (clippedOuter c.radius (range c.point)).Nonempty}

theorem clippedOuter_zero_mem_interior (hR : 0 < c.radius) :
    (0 : Space) ∈ interior (clippedOuterBody c.radius (range c.point) hne : Set Space) := by
  have hR1 : c.radius < 1 := by nlinarith [c.radius_sq_le (by decide)]
  have hball := zero_mem_interior_ballTransform hR1 (C := range c.point) (by
    rintro _ ⟨i, rfl⟩
    exact (c.on_sphere i).le)
  apply mem_interior_iff_mem_nhds.2
  change closedBall (0 : Space) c.radius ∩ ballTransform (range c.point) ∈ 𝓝 (0 : Space)
  exact inter_mem (closedBall_mem_nhds _ hR) (mem_interior_iff_mem_nhds.1 hball)

theorem integral_mul_curvatureDet_clipped (hA : c.totalDeficit ≤ 2 / 25)
    (hR : 1 / 2 < c.radius) {f : UnitSphere → ℝ} (hf : Integrable f sphereMeasure) :
    (∫ u : UnitSphere, f u * curvatureDet (clippedOuterBody c.radius (range c.point) hne) u
      ∂sphereMeasure) = c.radius ^ 2 * (∫ u in c.radiusFaceNormals, f u ∂sphereMeasure) +
        ∑ i, ∫ u in c.unitFaceNormals i, f u ∂sphereMeasure := by
  classical
  have hR0 : 0 < c.radius := by linarith
  have hiR := (hf.const_mul (c.radius ^ 2)).indicator (c.measurableSet_radiusFaceNormals hR0)
  have hi (i : Fin 4) := hf.indicator (c.measurableSet_unitFaceNormals i)
  have he : (fun u : UnitSphere ↦ f u * curvatureDet
      (clippedOuterBody c.radius (range c.point) hne) u) =ᵐ[sphereMeasure]
      (fun u ↦ c.radiusFaceNormals.indicator (fun v ↦ c.radius ^ 2 * f v) u +
        ∑ i, (c.unitFaceNormals i).indicator f u) := by
    filter_upwards [c.curvatureDet_clipped_eq_faceIndicators_ae (hne := hne) hA hR] with u hu
    rw [hu, mul_add, Finset.mul_sum]
    congr 1
    · by_cases hmem : u ∈ c.radiusFaceNormals
      · rw [indicator_of_mem hmem, indicator_of_mem hmem, mul_comm]
      · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, mul_zero]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hmem : u ∈ c.unitFaceNormals i
      · rw [indicator_of_mem hmem, indicator_of_mem hmem, mul_one]
      · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, mul_zero]
  rw [integral_congr_ae he, integral_add hiR (integrable_finsetSum _ (fun i _ ↦ hi i)),
    integral_finsetSum _ (fun i _ ↦ hi i),
    integral_indicator (c.measurableSet_radiusFaceNormals hR0), integral_const_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_indicator (c.measurableSet_unitFaceNormals i)

/-- The linear Steiner coefficient is the sum of the actual spherical face areas. -/
theorem parallelLinear_clipped_eq_face_areas (hA : c.totalDeficit ≤ 2 / 25)
    (hR : 1 / 2 < c.radius) :
    parallelLinear (clippedOuterBody c.radius (range c.point) hne) =
      c.radius ^ 2 * sphereMeasure.real c.radiusFaceNormals +
        ∑ i, sphereMeasure.real (c.unitFaceNormals i) := by
  have hR0 : 0 < c.radius := by linarith
  have hR1 : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  rw [parallelLinear_eq_integral_curvatureDet
    (clippedBodies_complement c.radius (range c.point) hne hR1) (c.clippedOuter_zero_mem_interior hR0)]
  simpa only [one_mul, setIntegral_one_eq_measureReal] using
    c.integral_mul_curvatureDet_clipped (hne := hne) hA hR (integrable_const (1 : ℝ))

theorem integral_support_unitFace (i : Fin 4) :
    (∫ u in c.unitFaceNormals i, support (clippedOuterBody c.radius (range c.point) hne) (u : Space)
      ∂sphereMeasure) = sphereMeasure.real (c.unitFaceNormals i) +
        ∫ u in c.unitFaceNormals i, ⟪c.point i, (u : Space)⟫_ℝ ∂sphereMeasure := by
  have hi : Integrable (fun u : UnitSphere ↦ ⟪c.point i, (u : Space)⟫_ℝ) sphereMeasure :=
    (continuous_const.inner continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (∫ u in c.unitFaceNormals i,
      support (clippedOuterBody c.radius (range c.point) hne) (u : Space) ∂sphereMeasure) =
      ∫ u in c.unitFaceNormals i, ⟪c.point i, (u : Space)⟫_ℝ + 1 ∂sphereMeasure := by
    apply setIntegral_congr_fun (c.measurableSet_unitFaceNormals i)
    intro u hu
    dsimp only
    rw [c.support_unitFaceNormals (hne := hne) i hu, real_inner_comm]
  rw [he, integral_add hi.integrableOn (integrable_const 1), setIntegral_one_eq_measureReal, add_comm]

theorem integral_support_radiusFace (hR : 0 < c.radius) :
    (∫ u in c.radiusFaceNormals, support (clippedOuterBody c.radius (range c.point) hne) (u : Space)
      ∂sphereMeasure) = c.radius * sphereMeasure.real c.radiusFaceNormals := by
  have he : (∫ u in c.radiusFaceNormals,
      support (clippedOuterBody c.radius (range c.point) hne) (u : Space) ∂sphereMeasure) =
      ∫ _ in c.radiusFaceNormals, c.radius ∂sphereMeasure := by
    apply setIntegral_congr_fun (c.measurableSet_radiusFaceNormals hR)
    intro u hu
    exact c.support_radiusFaceNormals hu
  rw [he, setIntegral_const, smul_eq_mul, mul_comm]

/-- The volume formula for the actual clipped body, expressed through face areas and moments. -/
theorem bodyVolume_clipped_eq_face_integrals (hA : c.totalDeficit ≤ 2 / 25)
    (hR : 1 / 2 < c.radius) :
    3 * bodyVolume (clippedOuterBody c.radius (range c.point) hne) =
      (∑ i, sphereMeasure.real (c.unitFaceNormals i)) +
        c.radius ^ 3 * sphereMeasure.real c.radiusFaceNormals +
        ∑ i, ∫ u in c.unitFaceNormals i, ⟪c.point i, (u : Space)⟫_ℝ ∂sphereMeasure := by
  have hR0 : 0 < c.radius := by linarith
  have hR1 : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  have hsum := clippedBodies_complement c.radius (range c.point) hne hR1
  have hi : Integrable (fun u : UnitSphere ↦
      support (clippedOuterBody c.radius (range c.point) hne) (u : Space)) sphereMeasure :=
    (continuous_support_sphere hsum).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_support_curvatureDet hsum (c.clippedOuter_zero_mem_interior hR0),
    c.integral_mul_curvatureDet_clipped hA hR hi, c.integral_support_radiusFace hR0]
  simp_rw [c.integral_support_unitFace]
  rw [Finset.sum_add_distrib]
  ring

end BlaschkeLebesgue.BalancedContacts
