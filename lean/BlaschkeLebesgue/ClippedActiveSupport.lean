module

public import BlaschkeLebesgue.TwoBallSupport
public import BlaschkeLebesgue.CircleSupportRegion
public import BlaschkeLebesgue.ClippingCircle

/-! # Classification of support points with one or two active balls -/

public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts

variable (c : BalancedContacts 4 Space)
  {hne : (clippedOuter c.radius (range c.point)).Nonempty}

theorem normalSupport_clipped_eq_face_of_one_active (u : UnitSphere) (i : Option (Fin 4))
    (hstrict : ∀ j, j ≠ i →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) -
        c.clippedBallCenter j‖ < c.clippedBallRadius j) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      c.clippedBallCenter i + c.clippedBallRadius i • (u : Space) := by
  have hm := c.normalSupport_clipped_maxOn_active (u : Space) {i}
    (by simpa only [mem_singleton_iff] using hstrict)
  rw [biInter_singleton] at hm
  apply eq_ball_face_of_isMaxOn u.norm_eq_one _ hm
  have hx := normalSupport_mem (clippedOuterBody c.radius (range c.point) hne) (u : Space)
  change normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) ∈
    clippedOuter c.radius (range c.point) at hx
  rw [c.clippedOuter_eq_five_balls] at hx
  simpa only [mem_closedBall, dist_eq_norm] using mem_iInter.1 hx i

theorem normalSupport_clipped_maxOn_unit_pair (u : Space) (i j : Fin 4)
    (hR : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) u‖ < c.radius)
    (hother : ∀ k, k ≠ i → k ≠ j →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) u - c.point k‖ < 1) :
    IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (closedBall (c.point i) 1 ∩ closedBall (c.point j) 1)
      (normalSupport (clippedOuterBody c.radius (range c.point) hne) u) := by
  have hm := c.normalSupport_clipped_maxOn_active (hne := hne) u {some i, some j}
    (by
      intro k hk
      cases k with
      | none => simpa only [clippedBallCenter, clippedBallRadius, sub_zero] using hR
      | some k =>
        simp only [mem_insert_iff, mem_singleton_iff, Option.some.injEq, not_or] at hk
        exact hother k hk.1 hk.2)
  simpa only [biInter_pair, clippedBallCenter, clippedBallRadius] using hm

theorem normalSupport_clipped_maxOn_radius_pair (u : Space) (i : Fin 4)
    (hother : ∀ j, j ≠ i →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) u - c.point j‖ < 1) :
    IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (closedBall 0 c.radius ∩ closedBall (c.point i) 1)
      (normalSupport (clippedOuterBody c.radius (range c.point) hne) u) := by
  have hm := c.normalSupport_clipped_maxOn_active (hne := hne) u {none, some i}
    (by
      intro k hk
      cases k with
      | none => exact (hk (by simp)).elim
      | some j =>
        simp only [mem_insert_iff, mem_singleton_iff, reduceCtorEq, Option.some.injEq,
          false_or] at hk
        exact hother j hk)
  simpa only [biInter_pair, clippedBallCenter, clippedBallRadius] using hm

namespace Opposite

theorem active_unit_pair_normal_bounds (ha : edgeBudget c < 1) (u : UnitSphere)
    (h₀ : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) -
      c.point 0‖ = 1)
    (h₁ : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) -
      c.point 1‖ = 1)
    (hR : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ < c.radius)
    (hother : ∀ k, k ≠ 0 → k ≠ 1 →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point k‖ < 1) :
    |⟪firstAxis c, (u : Space)⟫_ℝ| ≤ ‖firstEdge c‖ / 2 := by
  have hb := two_ball_support_axis_bounds (firstAxis_norm c ha) u.norm_eq_one
    (norm_pos_iff.2 (firstEdge_ne_zero c ha)) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
    (show c.point 1 - c.point 0 = ‖firstEdge c‖ • firstAxis c from
      (NormedSpace.norm_smul_normalize (firstEdge c)).symm)
    (show (1 : ℝ) ^ 2 + ‖firstEdge c‖ ^ 2 - 1 ^ 2 =
      2 * ‖firstEdge c‖ * (‖firstEdge c‖ / 2) by ring)
    h₀ h₁ (c.normalSupport_clipped_maxOn_unit_pair (u : Space) 0 1 hR hother)
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

theorem normalSupport_eq_circleCandidate_of_two_active (ha : edgeBudget c < 1) (u : UnitSphere)
    (h₀ : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) -
      c.point 0‖ = 1)
    (h₁ : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) -
      c.point 1‖ = 1)
    (hR : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ < c.radius)
    (hother : ∀ k, k ≠ 0 → k ≠ 1 →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point k‖ < 1) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      circleCandidate c (u : Space) := by
  have hcone := active_unit_pair_normal_bounds c ha u h₀ h₁ hR hother
  obtain ⟨v, hv, hve, hx⟩ := unit_spheres_circle_parametrization c
    (by simpa only [mem_sphere, dist_eq_norm] using h₀)
    (by simpa only [mem_sphere, dist_eq_norm] using h₁)
  have hvk : ⟪firstAxis c, v⟫_ℝ = 0 := by
    simp only [firstAxis, NormedSpace.normalize, real_inner_smul_left, hve, mul_zero]
  apply eq_circle_point_of_support (firstAxis_norm c ha) (circleRadius_pos c)
    (norm_pos_iff.1 (circleProjection_norm_pos c ha u.norm_eq_one hcone))
  · rw [hx, circlePoint, add_sub_cancel_left]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (circleRadius_pos c), hv, mul_one]
  · rw [hx, circlePoint, add_sub_cancel_left, real_inner_smul_right, hvk, mul_zero]
  · intro w hw hwk
    have hwe : ⟪firstEdge c, w⟫_ℝ = 0 := by
      rw [← NormedSpace.norm_smul_normalize (firstEdge c), real_inner_smul_left]
      change ‖firstEdge c‖ * ⟪firstAxis c, w⟫_ℝ = 0
      rw [hwk, mul_zero]
    have hs := circlePoint_mem_unit_spheres c hw hwe
    exact c.normalSupport_clipped_maxOn_unit_pair (u : Space) 0 1 hR hother
      ⟨sphere_subset_closedBall hs.1, sphere_subset_closedBall hs.2⟩

end Opposite

@[expose] def clippingCircleCandidate (i : Fin 4) (u : Space) : Space :=
  c.clippingCirclePoint i (NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u))

theorem active_radius_pair_normal_bounds (hR : 1 / 2 < c.radius) (u : UnitSphere) (i : Fin 4)
    (hx : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ = c.radius)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hother : ∀ j, j ≠ i →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ < 1) :
    -(1 / (2 * c.radius)) ≤ ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ∧
      ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ≤ 1 - 1 / (2 * c.radius ^ 2) := by
  have hR0 : 0 < c.radius := by linarith
  have ht : c.radius ^ 2 + c.radius ^ 2 - 1 ^ 2 =
      2 * c.radius * ClippingCircle.height c.radius := by
    unfold ClippingCircle.height
    field_simp
    ring
  have hb := two_ball_support_axis_bounds (c.clippingCircleAxis_norm hR0 i) u.norm_eq_one
    hR0 hR0 (by norm_num : (0 : ℝ) < 1)
    (show c.point i - 0 = c.radius • c.clippingCircleAxis i by
      rw [sub_zero, c.radius_smul_clippingCircleAxis hR0.ne']) ht
    (by simpa only [sub_zero] using hx) hi
    (c.normalSupport_clipped_maxOn_radius_pair (u : Space) i hother)
  have he : ClippingCircle.height c.radius / c.radius = 1 - 1 / (2 * c.radius ^ 2) := by
    unfold ClippingCircle.height
    field_simp
  rw [div_one, he] at hb
  constructor
  · simpa only [ClippingCircle.height, sub_sub_cancel_left] using hb.1
  · exact hb.2

theorem clippingCircleProjection_ne_zero (hR : 1 / 2 < c.radius) (u : UnitSphere) (i : Fin 4)
    (hlo : -(1 / (2 * c.radius)) ≤ ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)
    (hhi : ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ≤ 1 - 1 / (2 * c.radius ^ 2)) :
    axisProjection (c.clippingCircleAxis i) (u : Space) ≠ 0 := by
  have hR0 : 0 < c.radius := by linarith
  have ha : 1 / (2 * c.radius) < (1 : ℝ) :=
    (div_lt_one (by positivity)).2 (by linarith)
  have hb : 0 < 1 / (2 * c.radius ^ 2) := by positivity
  have hzlo : -1 < ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ := by linarith
  have hzhi : ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ < 1 := by linarith
  have hs := axisProjection_norm_sq (c.clippingCircleAxis_norm hR0 i) u.norm_eq_one
  intro he
  rw [he, norm_zero] at hs
  nlinarith [mul_pos (by linarith : 0 < 1 - ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)
    (by linarith : 0 < 1 + ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)]

theorem normalSupport_eq_clippingCircleCandidate_of_two_active
    (hR : 1 / 2 < c.radius) (u : UnitSphere) (i : Fin 4)
    (hx : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ = c.radius)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hother : ∀ j, j ≠ i →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ < 1) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      c.clippingCircleCandidate i (u : Space) := by
  have hR0 : 0 < c.radius := by linarith
  have hcone := c.active_radius_pair_normal_bounds hR u i hx hi hother
  have hp := c.clippingCircleProjection_ne_zero hR u i hcone.1 hcone.2
  obtain ⟨v, hv, hvc, he⟩ := c.clipping_spheres_parametrization hR
    (by simpa only [mem_sphere, dist_zero_right] using hx)
    (by simpa only [mem_sphere, dist_eq_norm] using hi)
  have hvk : ⟪c.clippingCircleAxis i, v⟫_ℝ = 0 := by
    simp only [clippingCircleAxis, real_inner_smul_left, hvc, mul_zero]
  apply eq_circle_point_of_support (c.clippingCircleAxis_norm hR0 i)
    (ClippingCircle.radius_pos hR) hp
  · rw [he, clippingCirclePoint, add_sub_cancel_left]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (ClippingCircle.radius_pos hR), hv, mul_one]
  · rw [he, clippingCirclePoint, add_sub_cancel_left, real_inner_smul_right, hvk, mul_zero]
  · intro w hw hwk
    have hwc : ⟪c.point i, w⟫_ℝ = 0 := by
      rw [← c.radius_smul_clippingCircleAxis hR0.ne' i, real_inner_smul_left, hwk, mul_zero]
    have hs := c.clippingCirclePoint_mem_spheres hR hw hwc
    exact c.normalSupport_clipped_maxOn_radius_pair (u : Space) i hother
      ⟨sphere_subset_closedBall hs.1, sphere_subset_closedBall hs.2⟩

end BlaschkeLebesgue.BalancedContacts
