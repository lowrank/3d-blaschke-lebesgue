module

public import BlaschkeLebesgue.ClippingCircleArcMeasure

/-! # The exact curvature integral on each enclosing-sphere edge -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

variable (c : BalancedContacts 4 Space)

@[expose] def radiusCircleNormals (i : Fin 4) : Set UnitSphere :=
  {u | ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ∈
      Icc (-(1 / (2 * c.radius))) (1 - 1 / (2 * c.radius ^ 2)) ∧
    ∀ j, ‖c.clippingCircleCandidate i u - c.point j‖ ≤ 1}

theorem radiusCircleNormals_eq_wedge (hR : 1 / 2 < c.radius) (i : Fin 4)
    (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (c.clippingCircleAxis i) = coordinatePole) :
    c.radiusCircleNormals i = orthogonalWedge e (-(1 / (2 * c.radius)))
      (1 - 1 / (2 * c.radius ^ 2)) (c.radiusCircleLongitudes i e) := by
  ext u
  rw [mem_orthogonalWedge e hek]
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro hcone
  have hp := c.clippingCircleProjection_ne_zero hR u i hcone.1 hcone.2
  have he : c.clippingCircleCandidate i u =
      c.clippingCircleAnglePoint i e (longitude (sphereIsometry e u)) := by
    exact congrArg (c.clippingCirclePoint i) (normalize_axisProjection_eq_equator e hek u hp)
  simp only [he, radiusCircleLongitudes, mem_ofPred_eq]

theorem measurableSet_radiusCircleNormals (hR : 1 / 2 < c.radius) (i : Fin 4) :
    MeasurableSet (c.radiusCircleNormals i) := by
  have hk := c.clippingCircleAxis_norm (by linarith : 0 < c.radius) i
  obtain ⟨e, hek, _⟩ := exists_isometry_cap_axes hk hk
  rw [c.radiusCircleNormals_eq_wedge hR i e hek]
  exact measurableSet_orthogonalWedge e _ _ (c.measurableSet_radiusCircleLongitudes i e)

theorem normalSupport_radiusCircleNormals (hR : 1 / 2 < c.radius)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} (i : Fin 4) {u : UnitSphere}
    (hu : u ∈ c.radiusCircleNormals i) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      c.clippingCircleCandidate i u := by
  apply c.normalSupport_clipped_clippingCircleCandidate hR i u hu.1.1 hu.1.2
  have hp := c.clippingCircleProjection_ne_zero hR u i hu.1.1 hu.1.2
  have hf := c.clippingCircleDirection_frame (by linarith : 0 < c.radius) i hp
  have hs := c.clippingCirclePoint_mem_spheres hR hf.1 hf.2
  rw [c.mem_clippedOuter_range_iff]
  refine ⟨?_, hu.2⟩
  exact le_of_eq (by simpa only [mem_sphere, dist_zero_right, clippingCircleCandidate] using hs.1)

theorem radiusCircleNormals_ae_strict (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.radiusCircleNormals i →
      -(1 / (2 * c.radius)) < ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ∧
      ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ < 1 - 1 / (2 * c.radius ^ 2) ∧
      ∀ j, j ≠ i → ‖c.clippingCircleCandidate i u - c.point j‖ < 1 := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  have hR0 : 0 < c.radius := by linarith
  have hk := c.clippingCircleAxis_norm hR0 i
  obtain ⟨e, hek, _⟩ := exists_isometry_cap_axes hk hk
  have h₁ : ∀ᵐ u : UnitSphere ∂sphereMeasure,
      ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ≠ -(1 / (2 * c.radius)) := by
    rw [ae_iff]
    simpa only [not_not] using sphereMeasure_inner_level_unit hk (-(1 / (2 * c.radius)))
  have h₂ : ∀ᵐ u : UnitSphere ∂sphereMeasure,
      ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ≠ 1 - 1 / (2 * c.radius ^ 2) := by
    rw [ae_iff]
    simpa only [not_not] using sphereMeasure_inner_level_unit hk (1 - 1 / (2 * c.radius ^ 2))
  have h₃ : ∀ j, ∀ᵐ u : UnitSphere ∂sphereMeasure, j ≠ i →
      ¬ (axisProjection (c.clippingCircleAxis i) (u : Space) ≠ 0 ∧
        ⟪c.clippingPairDirection i j,
          NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) (u : Space))⟫_ℝ =
            c.clippingPairCos i j) := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hji).elim
    · have h := sphereMeasure_normal_direction_level e hek (c.clippingPairDirection_norm hA (Ne.symm hji))
        (c.clippingPairDirection_inner_axis hR0 i j) (c.clippingPairCos i j)
      have h' : ∀ᵐ u : UnitSphere ∂sphereMeasure,
          ¬ (axisProjection (c.clippingCircleAxis i) (u : Space) ≠ 0 ∧
            ⟪c.clippingPairDirection i j,
              NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) (u : Space))⟫_ℝ =
                c.clippingPairCos i j) := by
        rw [ae_iff]
        simpa only [not_not] using h
      exact h'.mono fun _ hu _ ↦ hu
  filter_upwards [h₁, h₂, Filter.eventually_all.2 h₃] with u hu₁ hu₂ hu₃ hu
  refine ⟨lt_of_le_of_ne hu.1.1 hu₁.symm, lt_of_le_of_ne hu.1.2 hu₂, ?_⟩
  have hp := c.clippingCircleProjection_ne_zero hR u i hu.1.1 hu.1.2
  have hf := c.clippingCircleDirection_frame hR0 i hp
  intro j hji
  apply lt_of_le_of_ne (hu.2 j)
  intro he
  have hi := (c.clippingCircle_distance_eq_pair_iff hA hji.symm hf.1 hf.2).1 he
  exact hu₃ j hji ⟨hp, hi⟩

theorem integral_radiusCircleNormals_curvatureTrace (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} (i : Fin 4) :
    (∫ u in c.radiusCircleNormals i,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      ClippingCircle.radius c.radius * (2 * Real.pi - 2 * ∑ j, c.clippingPairAngle i j) *
        Real.arccos (1 / (2 * c.radius)) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  have he : (∫ u in c.radiusCircleNormals i,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      ∫ u in c.radiusCircleNormals i, ClippingCircle.radius c.radius /
        Real.sqrt (1 - ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ^ 2) ∂sphereMeasure := by
    apply integral_congr_ae
    apply (ae_restrict_iff' (c.measurableSet_radiusCircleNormals hR i)).2
    filter_upwards [c.radiusCircleNormals_ae_strict hA i] with u hu huS
    exact c.clipped_clippingCircle_curvatureTrace hR i u (hu huS).1 (hu huS).2.1 (hu huS).2.2
  rw [he]
  have hk := c.clippingCircleAxis_norm (by linarith : 0 < c.radius) i
  obtain ⟨e, hek, _⟩ := exists_isometry_cap_axes hk hk
  rw [c.radiusCircleNormals_eq_wedge hR i e hek,
    integral_orthogonalWedge_height e hek _ _ _
      (fun z ↦ ClippingCircle.radius c.radius / Real.sqrt (1 - z ^ 2)),
    integral_unit_radius_wedge hR (c.measurableSet_radiusCircleLongitudes i e),
    c.volume_real_radiusCircleLongitudes hA i e hek]

end BlaschkeLebesgue.BalancedContacts
