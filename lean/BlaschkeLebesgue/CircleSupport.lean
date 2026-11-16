module

public import BlaschkeLebesgue.CircleNormalCone
public import BlaschkeLebesgue.SupportDifferentiation
public import BlaschkeLebesgue.ClippedBodies

/-!
# Actual support on an active contact circle

The normal-cone condition is proved sufficient. Membership of the candidate in
the remaining balls is an explicit hypothesis here; proving the required open
support regions is a separate geometric obligation.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unitSphere_normal_supports_ball {p x y : E} (hx : ‖x - p‖ = 1)
    (hy : ‖y - p‖ ≤ 1) : ⟪x - p, y - x⟫_ℝ ≤ 0 := by
  have h := real_inner_le_norm (x - p) (y - p)
  rw [hx, one_mul] at h
  have hyx : y - x = (y - p) - (x - p) := by abel
  rw [hyx, inner_sub_right, real_inner_self_eq_norm_sq, hx]
  linarith

namespace BalancedContacts.Opposite

variable (c : BalancedContacts 4 E)

theorem circleCandidate_inner_le (ha : edgeBudget c < 1) {n y : E} (hn : ‖n‖ = 1)
    (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2)
    (hy0 : ‖y - c.point 0‖ ≤ 1) (hy1 : ‖y - c.point 1‖ ≤ 1) :
    ⟪n, y⟫_ℝ ≤ ⟪n, circleCandidate c n⟫_ℝ := by
  obtain ⟨l₀, l₁, hl₀, hl₁, hnormal⟩ := circle_normal_cone c ha hn hcone
  have hframe := circleDirection_frame c ha hn hcone
  have hsphere := circlePoint_mem_unit_spheres c hframe.1 hframe.2.1
  have h0 := unitSphere_normal_supports_ball
    (show ‖circleCandidate c n - c.point 0‖ = 1 by
      simpa only [Metric.mem_sphere, dist_eq_norm, circleCandidate] using hsphere.1) hy0
  have h1 := unitSphere_normal_supports_ball
    (show ‖circleCandidate c n - c.point 1‖ = 1 by
      simpa only [Metric.mem_sphere, dist_eq_norm, circleCandidate] using hsphere.2) hy1
  have hinner : ⟪n, y - circleCandidate c n⟫_ℝ ≤ 0 := by
    conv_lhs => lhs; rw [hnormal]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hl₀ h0)
      (mul_nonpos_of_nonneg_of_nonpos hl₁ h1)
  rw [inner_sub_right] at hinner
  linarith

theorem circleCandidate_support (ha : edgeBudget c < 1) {K : ConvexBody E} {n : E}
    (hn : ‖n‖ = 1) (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2)
    (hK0 : ∀ y ∈ K, ‖y - c.point 0‖ ≤ 1)
    (hK1 : ∀ y ∈ K, ‖y - c.point 1‖ ≤ 1) (hmem : circleCandidate c n ∈ K) :
    support K n = ⟪n, circleCandidate c n⟫_ℝ := by
  apply le_antisymm
  · apply (support_le_iff _ _ _).2
    intro y hy
    exact circleCandidate_inner_le c ha hn hcone (hK0 y hy) (hK1 y hy)
  · exact inner_le_support K n hmem

theorem circleCandidate_inner_formula (ha : edgeBudget c < 1) {n : E} (hn : ‖n‖ = 1)
    (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2) :
    ⟪n, circleCandidate c n⟫_ℝ = ⟪n, firstMidpoint c⟫_ℝ +
      circleRadius c * Real.sqrt (1 - ⟪firstAxis c, n⟫_ℝ ^ 2) := by
  have hframe := circleDirection_frame c ha hn hcone
  have hnorm : ‖circleProjection c n‖ = Real.sqrt (1 - ⟪firstAxis c, n⟫_ℝ ^ 2) := by
    rw [← circleProjection_norm_sq c ha hn, Real.sqrt_sq (norm_nonneg _)]
  simp only [circleCandidate, circlePoint, inner_add_right, real_inner_smul_right,
    hframe.2.2, hnorm]

theorem support_circle_formula (ha : edgeBudget c < 1) {K : ConvexBody E} {n : E}
    (hn : ‖n‖ = 1) (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2)
    (hK0 : ∀ y ∈ K, ‖y - c.point 0‖ ≤ 1)
    (hK1 : ∀ y ∈ K, ‖y - c.point 1‖ ≤ 1) (hmem : circleCandidate c n ∈ K) :
    support K n = ⟪n, firstMidpoint c⟫_ℝ +
      circleRadius c * Real.sqrt (1 - ⟪firstAxis c, n⟫_ℝ ^ 2) := by
  rw [circleCandidate_support c ha hn hcone hK0 hK1 hmem]
  exact circleCandidate_inner_formula c ha hn hcone

variable (c : BalancedContacts 4 Space)

theorem normalSupport_circleCandidate (ha : edgeBudget c < 1) {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {n : Space} (hn : ‖n‖ = 1)
    (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2)
    (hK0 : ∀ y ∈ K, ‖y - c.point 0‖ ≤ 1)
    (hK1 : ∀ y ∈ K, ‖y - c.point 1‖ ≤ 1) (hmem : circleCandidate c n ∈ K) :
    normalSupport K n = circleCandidate c n := by
  have h := supportPoint_unique_of_ball_sum hKL hn hmem
    (circleCandidate_support c ha hn hcone hK0 hK1 hmem).symm
  simpa only [normalSupport, NormedSpace.normalize_eq_self_of_norm_eq_one hn] using h.symm

/-- The support formula applies to the actual clipped body whenever the circle
candidate passes all its ball constraints. -/
theorem clippedOuter_support_circle_formula (ha : edgeBudget c < 1)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} {n : Space}
    (hn : ‖n‖ = 1) (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2)
    (hmem : circleCandidate c n ∈ clippedOuterBody c.radius (Set.range c.point) hne) :
    support (clippedOuterBody c.radius (Set.range c.point) hne) n =
      ⟪n, firstMidpoint c⟫_ℝ + circleRadius c * Real.sqrt (1 - ⟪firstAxis c, n⟫_ℝ ^ 2) := by
  apply support_circle_formula c ha hn hcone _ _ hmem
  · intro y hy
    exact hy.2 _ ⟨0, rfl⟩
  · intro y hy
    exact hy.2 _ ⟨1, rfl⟩

end BalancedContacts.Opposite
end BlaschkeLebesgue
