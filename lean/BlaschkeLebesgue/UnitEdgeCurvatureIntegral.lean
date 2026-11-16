module

public import BlaschkeLebesgue.EquatorMeasure
public import BlaschkeLebesgue.ContactArcIncidence

/-! # The curvature integral of an actual unit--unit edge -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

variable (c : BalancedContacts 4 Space)

@[expose] def unitCircleNormals : Set UnitSphere :=
  {u | |⟪firstAxis c, (u : Space)⟫_ℝ| ≤ ‖firstEdge c‖ / 2 ∧
    ‖circleCandidate c u‖ ≤ c.radius}

@[expose] def unitCircleLongitudes (e : Space ≃ₗᵢ[ℝ] Space) : Set (AddCircle (2 * Real.pi)) :=
  {a | clippingCos c ≤ ⟪e (arcCenterDirection c), equatorPoint a⟫_ℝ}

theorem edgeBudget_lt_one_of_small_deficit (hA : c.totalDeficit ≤ 2 / 25) : edgeBudget c < 1 := by
  linarith [budgets_sum c, crossBudget_nonneg c]

theorem arcCenterDirection_inner_axis : ⟪firstAxis c, arcCenterDirection c⟫_ℝ = 0 := by
  simp only [firstAxis, NormedSpace.normalize, real_inner_smul_left,
    arcCenterDirection_inner_edge c, mul_zero]

theorem unitCircleNormals_eq_wedge (hA : c.totalDeficit ≤ 2 / 25)
    (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (firstAxis c) = coordinatePole) :
    unitCircleNormals c = orthogonalWedge e (-(‖firstEdge c‖ / 2)) (‖firstEdge c‖ / 2)
      (unitCircleLongitudes c e) := by
  ext u
  rw [mem_orthogonalWedge e hek]
  change (|⟪firstAxis c, (u : Space)⟫_ℝ| ≤ ‖firstEdge c‖ / 2 ∧ _) ↔
    ((-(‖firstEdge c‖ / 2) ≤ ⟪firstAxis c, (u : Space)⟫_ℝ ∧
      ⟪firstAxis c, (u : Space)⟫_ℝ ≤ ‖firstEdge c‖ / 2) ∧ _)
  rw [← abs_le]
  apply and_congr_right
  intro hcone
  have ha := edgeBudget_lt_one_of_small_deficit c hA
  have hf := circleDirection_frame c ha u.norm_eq_one hcone
  have hp := norm_pos_iff.1 (circleProjection_norm_pos c ha u.norm_eq_one hcone)
  have he := normalize_axisProjection_eq_equator e hek u hp
  have hi : ⟪circleDirection c u, arcCenterDirection c⟫_ℝ =
      ⟪e (arcCenterDirection c), equatorPoint (longitude (sphereIsometry e u))⟫_ℝ := by
    change ⟪NormedSpace.normalize (axisProjection (firstAxis c) (u : Space)), arcCenterDirection c⟫_ℝ = _
    rw [he, real_inner_comm]
    rw [← e.inner_map_map, e.apply_symm_apply]
  have h := circlePoint_mem_radius_ball_iff c hA hf.1
  simp only [mem_closedBall, dist_zero_right] at h
  change (‖circleCandidate c u‖ ≤ c.radius ↔
    clippingCos c ≤ ⟪circleDirection c u, arcCenterDirection c⟫_ℝ) at h
  rw [hi] at h
  exact h

theorem measurableSet_unitCircleLongitudes (e : Space ≃ₗᵢ[ℝ] Space) :
    MeasurableSet (unitCircleLongitudes c e) :=
  (isClosed_le continuous_const (continuous_const.inner continuous_equatorPoint)).measurableSet

theorem measurableSet_unitCircleNormals (hA : c.totalDeficit ≤ 2 / 25) :
    MeasurableSet (unitCircleNormals c) := by
  obtain ⟨e, hek, _⟩ := exists_isometry_cap_axes
    (firstAxis_norm c (edgeBudget_lt_one_of_small_deficit c hA)) (arcCenterDirection_norm c hA)
  rw [unitCircleNormals_eq_wedge c hA e hek]
  exact measurableSet_orthogonalWedge e _ _ (measurableSet_unitCircleLongitudes c e)

theorem volume_real_unitCircleLongitudes (hA : c.totalDeficit ≤ 2 / 25)
    (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (firstAxis c) = coordinatePole) :
    volume.real (unitCircleLongitudes c e) = 2 * Real.arccos (clippingCos c) := by
  apply volume_real_equator_inner_ge
  · rw [e.norm_map, arcCenterDirection_norm c hA]
  · rw [← hek, e.inner_map_map, arcCenterDirection_inner_axis]

theorem normalSupport_unitCircleNormals (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} {u : UnitSphere}
    (hu : u ∈ unitCircleNormals c) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) = circleCandidate c u := by
  have ha := edgeBudget_lt_one_of_small_deficit c hA
  have hf := circleDirection_frame c ha u.norm_eq_one hu.1
  have hR1 : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  apply normalSupport_circleCandidate c ha
    (clippedBodies_complement c.radius (range c.point) hne hR1) u.norm_eq_one hu.1
    (fun y hy ↦ hy.2 _ ⟨0, rfl⟩) (fun y hy ↦ hy.2 _ ⟨1, rfl⟩)
  exact (circlePoint_mem_clippedOuter_iff c hA hf.1 hf.2.1).2 hu.2

theorem unitCircleNormals_ae_strict (hA : c.totalDeficit ≤ 2 / 25) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ unitCircleNormals c →
      |⟪firstAxis c, (u : Space)⟫_ℝ| < ‖firstEdge c‖ / 2 ∧
        ‖circleCandidate c u‖ < c.radius := by
  have ha := edgeBudget_lt_one_of_small_deficit c hA
  have hk := firstAxis_norm c ha
  obtain ⟨e, hek, _⟩ := exists_isometry_cap_axes hk (arcCenterDirection_norm c hA)
  have h₁ : ∀ᵐ u : UnitSphere ∂sphereMeasure, ⟪firstAxis c, (u : Space)⟫_ℝ ≠ ‖firstEdge c‖ / 2 := by
    rw [ae_iff]
    simpa only [not_not] using sphereMeasure_inner_level_unit hk (‖firstEdge c‖ / 2)
  have h₂ : ∀ᵐ u : UnitSphere ∂sphereMeasure, ⟪firstAxis c, (u : Space)⟫_ℝ ≠ -(‖firstEdge c‖ / 2) := by
    rw [ae_iff]
    simpa only [not_not] using sphereMeasure_inner_level_unit hk (-(‖firstEdge c‖ / 2))
  have h₃ : ∀ᵐ u : UnitSphere ∂sphereMeasure,
      ¬ (axisProjection (firstAxis c) (u : Space) ≠ 0 ∧
        ⟪arcCenterDirection c, NormedSpace.normalize (axisProjection (firstAxis c) (u : Space))⟫_ℝ =
          clippingCos c) := by
    rw [ae_iff]
    simpa only [not_not] using sphereMeasure_normal_direction_level e hek
      (arcCenterDirection_norm c hA) (arcCenterDirection_inner_axis c) (clippingCos c)
  filter_upwards [h₁, h₂, h₃] with u hu₁ hu₂ hu₃ hu
  have hf := circleDirection_frame c ha u.norm_eq_one hu.1
  have hp := norm_pos_iff.1 (circleProjection_norm_pos c ha u.norm_eq_one hu.1)
  have hcl : clippingCos c ≤ ⟪circleDirection c u, arcCenterDirection c⟫_ℝ :=
    (circlePoint_mem_radius_ball_iff c hA hf.1).1
      (by simpa only [mem_closedBall, dist_zero_right, circleCandidate] using hu.2)
  have hne : ⟪circleDirection c u, arcCenterDirection c⟫_ℝ ≠ clippingCos c := by
    intro he
    exact hu₃ ⟨hp, (real_inner_comm _ _).trans he⟩
  refine ⟨abs_lt.2 ⟨lt_of_le_of_ne (abs_le.1 hu.1).1 hu₂.symm,
    lt_of_le_of_ne (abs_le.1 hu.1).2 hu₁⟩, ?_⟩
  simpa only [mem_ball, dist_zero_right, circleCandidate] using
    (circlePoint_mem_radius_openBall_iff c hA hf.1).2 (lt_of_le_of_ne hcl hne.symm)

theorem integral_unitCircleNormals_curvatureTrace (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} :
    (∫ u in unitCircleNormals c,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      2 * circleRadius c * (2 * Real.arccos (clippingCos c)) * Real.arcsin (‖firstEdge c‖ / 2) := by
  have ha := edgeBudget_lt_one_of_small_deficit c hA
  have hs := firstEdge_norm_sq_le_one c
  have hs0 : 0 < ‖firstEdge c‖ := norm_pos_iff.2 (firstEdge_ne_zero c ha)
  have hs1 : ‖firstEdge c‖ ≤ 1 := by nlinarith
  have he : (∫ u in unitCircleNormals c,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      ∫ u in unitCircleNormals c,
        circleRadius c / Real.sqrt (1 - ⟪firstAxis c, (u : Space)⟫_ℝ ^ 2) ∂sphereMeasure := by
    apply integral_congr_ae
    apply (ae_restrict_iff' (measurableSet_unitCircleNormals c hA)).2
    filter_upwards [unitCircleNormals_ae_strict c hA] with u hu huS
    exact (clipped_circle_curvature_of_inside_radius c hA u (hu huS).1 (hu huS).2).1
  rw [he]
  obtain ⟨e, hek, _⟩ := exists_isometry_cap_axes (firstAxis_norm c ha) (arcCenterDirection_norm c hA)
  rw [unitCircleNormals_eq_wedge c hA e hek,
    integral_orthogonalWedge_circleDensity e hek (by linarith) (by linarith) (by linarith)
      (measurableSet_unitCircleLongitudes c e), volume_real_unitCircleLongitudes c hA e hek,
    Real.arcsin_neg]
  ring

end BlaschkeLebesgue.BalancedContacts.Opposite
