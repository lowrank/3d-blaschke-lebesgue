module

public import BlaschkeLebesgue.VolumeVariation

/-!
# The reference inner ball

A sufficiently small centered ball lies inside a body containing zero in its
interior. Its support, curvature, and parallel-volume coefficients can all be
computed directly, providing the reference body for the integral identities.
-/

public noncomputable section

open MeasureTheory Set Metric NormedSpace Filter Topology
open scoped InnerProductSpace Pointwise

namespace BlaschkeLebesgue

theorem support_scaledBall {r : ℝ} (hr : 0 ≤ r) {u : Space} (hu : ‖u‖ = 1) :
    support (r • unitBallBody) u = r := by
  rw [support_smul _ _ hr, support_unitBallBody hu, mul_one]

theorem scaledBall_complement {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r • unitBallBody + (1 - r) • unitBallBody = unitBallBody := by
  apply eq_of_unit_support_eq
  intro u hu
  rw [support_add, support_scaledBall hr hu, support_scaledBall (sub_nonneg.2 hr1) hu,
    support_unitBallBody hu]
  ring

theorem scaledBall_zero_mem_interior {r : ℝ} (hr : 0 < r) :
    (0 : Space) ∈ interior (r • unitBallBody : ConvexBody Space) := by
  apply mem_interior_of_support_margin _ hr
  intro u hu
  rw [inner_zero_right, zero_add, support_scaledBall hr.le hu]

theorem parallelBody_scaledBall {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    parallelBody (r • unitBallBody) t = (r + t) • unitBallBody := by
  apply eq_of_unit_support_eq
  intro u hu
  rw [support_parallelBody _ ht hu, support_scaledBall hr hu,
    support_scaledBall (add_nonneg hr ht) hu]

theorem scaledBall_parallelCoefficients {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    parallelLinear (r • unitBallBody) = 4 * Real.pi * r ^ 2 ∧
      parallelQuadratic (r • unitBallBody) = 4 * Real.pi * r := by
  have hc := scaledBall_complement hr.le hr1
  have h0 := scaledBall_zero_mem_interior hr
  have h1 := parallelBody_volume_polynomial hc h0 (t := 1) (by norm_num)
  have h2 := parallelBody_volume_polynomial hc h0 (t := 2) (by norm_num)
  rw [parallelBody_scaledBall hr.le (by norm_num : (0 : ℝ) ≤ 1),
    bodyVolume_smul _ (by positivity), bodyVolume_smul _ hr.le, bodyVolume_unitBallBody] at h1
  rw [parallelBody_scaledBall hr.le (by norm_num : (0 : ℝ) ≤ 2),
    bodyVolume_smul _ (by positivity), bodyVolume_smul _ hr.le, bodyVolume_unitBallBody] at h2
  constructor <;> nlinarith only [h1, h2]

theorem normalSupport_scaledBall {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {x : Space} (hx : x ≠ 0) : normalSupport (r • unitBallBody) x = r • normalize x := by
  symm
  apply supportPoint_unique_of_ball_sum (scaledBall_complement hr hr1) (norm_normalize hx)
  · exact Set.smul_mem_smul_set (mem_unitBallBody.2 (norm_normalize hx).le)
  · rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_normalize hx, one_pow, mul_one,
      support_scaledBall hr (norm_normalize hx)]

theorem sphereCurvature_scaledBall {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : UnitSphere) :
    sphereCurvature (r • unitBallBody) u = r • tangentProjection u := by
  have hd : HasFDerivAt (normalSupport (r • unitBallBody)) (r • tangentProjection u) (u : Space) := by
    apply ((hasFDerivAt_normalize_unit u.norm_eq_one).const_smul r).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds u.ne_zero] with x hx
    exact normalSupport_scaledBall hr hr1 hx
  exact hd.fderiv

theorem curvatureTrace_scaledBall {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : UnitSphere) :
    curvatureTrace (r • unitBallBody) u = 2 * r := by
  rw [curvatureTrace, sphereCurvature_scaledBall hr hr1]
  change LinearMap.trace ℝ Space (r • (tangentProjection u).toLinearMap) = _
  rw [map_smul, trace_tangentProjection, smul_eq_mul, mul_comm]

theorem exists_inner_scaledBall {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (r • unitBallBody : ConvexBody Space) ≤ K := by
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h0)
  let r := min (a / 2) (1 / 2 : ℝ)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hra : r < a := (min_le_left _ _).trans_lt (by linarith only [ha])
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (by norm_num)
  refine ⟨r, hr, hr1, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  apply hball
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  exact (mul_le_of_le_one_right hr.le (mem_unitBallBody.1 hy)).trans_lt hra

end BlaschkeLebesgue
