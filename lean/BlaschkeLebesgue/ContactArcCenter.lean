module

public import BlaschkeLebesgue.ContactCircle
public import BlaschkeLebesgue.ContactBallConstraints

/-! # An interior point of every clipped contact-circle arc -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

@[expose] def arcCenterDirection : E := -NormedSpace.normalize (firstMidpoint c)
@[expose] def arcCenter : E := circlePoint c (arcCenterDirection c)

theorem arcCenterDirection_norm (hA : c.totalDeficit ≤ 2 / 25) :
    ‖arcCenterDirection c‖ = 1 := by
  rw [arcCenterDirection, norm_neg]
  exact NormedSpace.norm_normalize (norm_pos_iff.mp (firstMidpoint_norm_pos c hA))

theorem arcCenterDirection_inner_edge : ⟪firstEdge c, arcCenterDirection c⟫_ℝ = 0 := by
  simp only [arcCenterDirection, NormedSpace.normalize, inner_neg_right, real_inner_smul_right,
    real_inner_comm (firstMidpoint c) (firstEdge c), firstMidpoint_inner_edge, mul_zero, neg_zero]

theorem arcCenter_norm_lt_radius (hA : c.totalDeficit ≤ 2 / 25) : ‖arcCenter c‖ < c.radius := by
  have h := (circlePoint_mem_radius_openBall_iff c hA (arcCenterDirection_norm c hA)).2
    (show clippingCos c < ⟪arcCenterDirection c, -NormedSpace.normalize (firstMidpoint c)⟫_ℝ by
      change clippingCos c < ⟪arcCenterDirection c, arcCenterDirection c⟫_ℝ
      rw [real_inner_self_eq_norm_sq, arcCenterDirection_norm c hA, one_pow]
      exact (clippingCos_bounds c hA).2)
  simpa only [Metric.mem_ball, dist_zero_right, arcCenter] using h

theorem firstMidpoint_point_inner (i : Fin 4) :
    ⟪firstMidpoint c, c.point i⟫_ℝ = c.radius ^ 2 - 1 / 2 +
      (c.edgeDeficit 0 i + c.edgeDeficit 1 i) / 4 := by
  simp only [firstMidpoint, edgeDeficit, real_inner_smul_left, inner_add_left,
    norm_sub_sq_real, c.on_sphere]
  ring

theorem firstMidpoint_other_inner_neg (hA : c.totalDeficit ≤ 2 / 25)
    (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : ⟪firstMidpoint c, c.point i⟫_ℝ < 0 := by
  have he : c.edgeDeficit 0 i + c.edgeDeficit 1 i ≤ c.totalDeficit := by
    have h01 := c.edgeDeficit_nonneg 0 1
    have h02 := c.edgeDeficit_nonneg 0 2
    have h03 := c.edgeDeficit_nonneg 0 3
    have h12 := c.edgeDeficit_nonneg 1 2
    have h13 := c.edgeDeficit_nonneg 1 3
    have h23 := c.edgeDeficit_nonneg 2 3
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hi1 rfl).elim
    · unfold totalDeficit
      norm_num only [Fin.reduceFinMk]
      linarith
    · unfold totalDeficit
      norm_num only [Fin.reduceFinMk]
      linarith
  rw [firstMidpoint_point_inner]
  have hR := c.radius_sq_le (by decide)
  linarith

theorem arcCenter_other_inner_pos (hA : c.totalDeficit ≤ 2 / 25)
    (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : 0 < ⟪arcCenter c, c.point i⟫_ℝ := by
  have hm := firstMidpoint_norm_pos c hA
  have hr := circleRadius_pos c
  have hR := c.radius_sq_le (by decide)
  have hr2 := circleRadius_sq c
  have hm2 := firstMidpoint_norm_sq c
  have hlt : ‖firstMidpoint c‖ < circleRadius c := by nlinarith
  have hcoef : 1 - circleRadius c / ‖firstMidpoint c‖ < 0 := by
    have h := (one_lt_div hm).2 hlt
    linarith
  have hid : ⟪arcCenter c, c.point i⟫_ℝ =
      (1 - circleRadius c / ‖firstMidpoint c‖) * ⟪firstMidpoint c, c.point i⟫_ℝ := by
    simp only [arcCenter, circlePoint, arcCenterDirection, NormedSpace.normalize,
      inner_add_left, real_inner_smul_left, inner_neg_left]
    ring
  rw [hid]
  exact mul_pos_of_neg_of_neg hcoef (firstMidpoint_other_inner_neg c hA i hi0 hi1)

/-- The arc center is strictly inside both remaining unit balls for every
configuration in the deficit domain, including its boundary. -/
theorem arcCenter_mem_other_ball (hA : c.totalDeficit ≤ 2 / 25)
    (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : ‖arcCenter c - c.point i‖ < 1 := by
  have hx := arcCenter_norm_lt_radius c hA
  have hR0 : 0 ≤ c.radius := le_trans (norm_nonneg _) hx.le
  have hx2 := (sq_lt_sq₀ (norm_nonneg _) hR0).2 hx
  have hinner := arcCenter_other_inner_pos c hA i hi0 hi1
  have hR := c.radius_sq_le (by decide)
  have hid := norm_sub_sq_real (arcCenter c) (c.point i)
  rw [c.on_sphere i] at hid
  nlinarith [norm_nonneg (arcCenter c - c.point i)]

end BlaschkeLebesgue.BalancedContacts.Opposite
