module

public import BlaschkeLebesgue.CircleDerivative

/-!
# Curvature on explicit open regions of the actual clipped body

Strict membership in the enclosing ball and in the other two unit balls,
together with the strict two-ball normal cone, gives an open region where the
actual support map equals the circle candidate. No local smoothness or support
identity is assumed.
-/

public noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space)

theorem circleProjection_smul (r : ℝ) (x : Space) :
    circleProjection c (r • x) = r • circleProjection c x := by
  simp only [circleProjection, real_inner_smul_right]
  module

theorem circleCandidate_smul {r : ℝ} (hr : 0 < r) (x : Space) :
    circleCandidate c (r • x) = circleCandidate c x := by
  simp only [circleCandidate, circleDirection, circleProjection_smul,
    NormedSpace.normalize_smul_of_pos hr]

theorem circleCandidate_normalize {x : Space} (hx : x ≠ 0) :
    circleCandidate c (NormedSpace.normalize x) = circleCandidate c x :=
  circleCandidate_smul c (inv_pos.mpr (norm_pos_iff.mpr hx)) x

theorem normalSupport_clippedOuter_eventually_circle (ha : edgeBudget c < 1)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} {n : Space}
    (hn : ‖n‖ = 1) (hcone : |⟪firstAxis c, n⟫_ℝ| < ‖firstEdge c‖ / 2)
    (hR : ‖circleCandidate c n‖ < c.radius)
    (h2 : ‖circleCandidate c n - c.point 2‖ < 1)
    (h3 : ‖circleCandidate c n - c.point 3‖ < 1) :
    normalSupport (clippedOuterBody c.radius (Set.range c.point) hne) =ᶠ[𝓝 n]
      circleCandidate c := by
  have hn0 : n ≠ 0 := by intro hh; simp [hh] at hn
  have hp0 := norm_pos_iff.mp (circleProjection_norm_pos c ha hn hcone.le)
  have hcand := (hasFDerivAt_circleCandidate c ha hp0).continuousAt
  have hnorm := (hasFDerivAt_normalize hn0).continuousAt
  have hcone' : ∀ᶠ x in 𝓝 n,
      |⟪firstAxis c, NormedSpace.normalize x⟫_ℝ| < ‖firstEdge c‖ / 2 := by
    apply Filter.Tendsto.eventually_lt_const
      (show |⟪firstAxis c, NormedSpace.normalize n⟫_ℝ| < ‖firstEdge c‖ / 2 by
        simpa only [NormedSpace.normalize_eq_self_of_norm_eq_one hn] using hcone)
    exact (continuousAt_const.inner hnorm).abs
  have hR' := Filter.Tendsto.eventually_lt_const hR hcand.norm
  have h2' := Filter.Tendsto.eventually_lt_const h2 (hcand.sub continuousAt_const).norm
  have h3' := Filter.Tendsto.eventually_lt_const h3 (hcand.sub continuousAt_const).norm
  have hrad : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  have hsum := clippedBodies_complement c.radius (Set.range c.point) hne hrad
  filter_upwards [isOpen_ne.mem_nhds hn0, hcone', hR', h2', h3'] with x hx hcx hRx h2x h3x
  have hunit := NormedSpace.norm_normalize hx
  have hframe := circleDirection_frame c ha hunit hcx.le
  have hspheres := circlePoint_mem_unit_spheres c hframe.1 hframe.2.1
  have hmem : circleCandidate c (NormedSpace.normalize x) ∈
      clippedOuterBody c.radius (Set.range c.point) hne := by
    constructor
    · simpa only [Metric.mem_closedBall, dist_zero_right, circleCandidate_normalize c hx] using hRx.le
    · rintro y ⟨i, rfl⟩
      fin_cases i
      · exact le_of_eq (by simpa [Metric.mem_sphere, dist_eq_norm, circleCandidate] using hspheres.1)
      · exact le_of_eq (by simpa [Metric.mem_sphere, dist_eq_norm, circleCandidate] using hspheres.2)
      · simpa [circleCandidate_normalize c hx, Pi.sub_apply] using h2x.le
      · simpa [circleCandidate_normalize c hx, Pi.sub_apply] using h3x.le
  have heq := normalSupport_circleCandidate c ha hsum hunit hcx.le
    (fun y hy ↦ hy.2 _ ⟨0, rfl⟩) (fun y hy ↦ hy.2 _ ⟨1, rfl⟩) hmem
  simpa only [normalSupport_normalize, circleCandidate_normalize c hx] using heq

theorem hasFDerivAt_normalSupport_clipped_circle (ha : edgeBudget c < 1)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} {n : Space}
    (hn : ‖n‖ = 1) (hcone : |⟪firstAxis c, n⟫_ℝ| < ‖firstEdge c‖ / 2)
    (hR : ‖circleCandidate c n‖ < c.radius)
    (h2 : ‖circleCandidate c n - c.point 2‖ < 1)
    (h3 : ‖circleCandidate c n - c.point 3‖ < 1) :
    HasFDerivAt (normalSupport (clippedOuterBody c.radius (Set.range c.point) hne))
      (circleCurvature c n) n := by
  apply (hasFDerivAt_circleCandidate c ha
    (norm_pos_iff.mp (circleProjection_norm_pos c ha hn hcone.le))).congr_of_eventuallyEq
  exact normalSupport_clippedOuter_eventually_circle c ha hn hcone hR h2 h3

/-- The trace and determinant of the actual clipped body's curvature on each
explicit circle-support region, including the exact nonzero curvature radius. -/
theorem clipped_circle_curvature (ha : edgeBudget c < 1)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (n : UnitSphere)
    (hcone : |⟪firstAxis c, (n : Space)⟫_ℝ| < ‖firstEdge c‖ / 2)
    (hR : ‖circleCandidate c n‖ < c.radius)
    (h2 : ‖circleCandidate c n - c.point 2‖ < 1)
    (h3 : ‖circleCandidate c n - c.point 3‖ < 1) :
    curvatureTrace (clippedOuterBody c.radius (Set.range c.point) hne) n =
      circleRadius c / Real.sqrt (1 - ⟪firstAxis c, (n : Space)⟫_ℝ ^ 2) ∧
    curvatureDet (clippedOuterBody c.radius (Set.range c.point) hne) n = 0 := by
  have hd := hasFDerivAt_normalSupport_clipped_circle c ha (hne := hne)
    n.norm_eq_one hcone hR h2 h3
  have heq : sphereCurvature (clippedOuterBody c.radius (Set.range c.point) hne) n =
      circleCurvature c n := hd.fderiv
  have hnorm : ‖circleProjection c n‖ = Real.sqrt (1 - ⟪firstAxis c, (n : Space)⟫_ℝ ^ 2) := by
    rw [← circleProjection_norm_sq c ha n.norm_eq_one, Real.sqrt_sq (norm_nonneg _)]
  constructor
  · unfold curvatureTrace
    rw [heq, trace_circleCurvature c ha n.norm_eq_one hcone.le, hnorm]
  · unfold curvatureDet augmentedCurvature
    rw [heq]
    exact circleCurvature_augmented_det c ha n.norm_eq_one hcone.le

end BlaschkeLebesgue.BalancedContacts.Opposite
