module

public import BlaschkeLebesgue.ContactCircleBounds

/-! # Actual points on the intersection circle and its clipped arc -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

theorem circlePoint_sub_first (v : E) :
    circlePoint c v - c.point 0 = (1 / 2 : ℝ) • firstEdge c + circleRadius c • v := by
  unfold circlePoint firstMidpoint firstEdge
  module

theorem circlePoint_sub_second (v : E) :
    circlePoint c v - c.point 1 = (-1 / 2 : ℝ) • firstEdge c + circleRadius c • v := by
  unfold circlePoint firstMidpoint firstEdge
  module

theorem norm_edge_circle_combination_sq {v : E} (hv : ‖v‖ = 1)
    (hperp : ⟪firstEdge c, v⟫_ℝ = 0) (t : ℝ) :
    ‖t • firstEdge c + circleRadius c • v‖ ^ 2 =
      t ^ 2 * ‖firstEdge c‖ ^ 2 + circleRadius c ^ 2 := by
  rw [norm_add_sq_real]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hv,
    real_inner_smul_left, real_inner_smul_right, hperp]
  ring

/-- These are points on both actual unit spheres, not just a formal support formula. -/
theorem circlePoint_mem_unit_spheres {v : E} (hv : ‖v‖ = 1)
    (hperp : ⟪firstEdge c, v⟫_ℝ = 0) :
    circlePoint c v ∈ Metric.sphere (c.point 0) 1 ∧
      circlePoint c v ∈ Metric.sphere (c.point 1) 1 := by
  have h0 : ‖circlePoint c v - c.point 0‖ ^ 2 = 1 := by
    rw [circlePoint_sub_first, norm_edge_circle_combination_sq c hv hperp, circleRadius_sq]
    ring
  have h1 : ‖circlePoint c v - c.point 1‖ ^ 2 = 1 := by
    rw [circlePoint_sub_second, norm_edge_circle_combination_sq c hv hperp, circleRadius_sq]
    ring
  simp only [Metric.mem_sphere, dist_eq_norm]
  constructor <;> nlinarith [norm_nonneg (circlePoint c v - c.point 0),
    norm_nonneg (circlePoint c v - c.point 1)]

/-- Conversely every point on the two unit spheres has this circle
parametrization, with a unit direction perpendicular to their contact edge. -/
theorem unit_spheres_circle_parametrization {x : E}
    (h0 : x ∈ Metric.sphere (c.point 0) 1)
    (h1 : x ∈ Metric.sphere (c.point 1) 1) :
    ∃ v : E, ‖v‖ = 1 ∧ ⟪firstEdge c, v⟫_ℝ = 0 ∧ x = circlePoint c v := by
  let d := x - firstMidpoint c
  have hx0 : x - c.point 0 = d + (1 / 2 : ℝ) • firstEdge c := by
    dsimp [d, firstMidpoint, firstEdge]
    module
  have hx1 : x - c.point 1 = d + (-1 / 2 : ℝ) • firstEdge c := by
    dsimp [d, firstMidpoint, firstEdge]
    module
  have hs0 : ‖x - c.point 0‖ ^ 2 = 1 := by
    rw [show ‖x - c.point 0‖ = 1 by simpa only [Metric.mem_sphere, dist_eq_norm] using h0]
    norm_num
  have hs1 : ‖x - c.point 1‖ ^ 2 = 1 := by
    rw [show ‖x - c.point 1‖ = 1 by simpa only [Metric.mem_sphere, dist_eq_norm] using h1]
    norm_num
  rw [hx0, norm_add_sq_real] at hs0
  rw [hx1, norm_add_sq_real] at hs1
  norm_num [norm_smul, mul_pow, Real.norm_eq_abs, real_inner_smul_right] at hs0 hs1
  have hdperp : ⟪d, firstEdge c⟫_ℝ = 0 := by linarith
  have hr := circleRadius_pos c
  have hrsq := circleRadius_sq c
  have hd : ‖d‖ = circleRadius c := by nlinarith [norm_nonneg d]
  let v := (circleRadius c)⁻¹ • d
  refine ⟨v, ?_, ?_, ?_⟩
  · simp only [v, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hd,
      inv_mul_cancel₀ hr.ne']
  · simp only [v, real_inner_smul_right, real_inner_comm d (firstEdge c), hdperp, mul_zero]
  · simp only [circlePoint, v, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    dsimp only [d]
    abel

theorem circlePoint_norm_sq {v : E} (hv : ‖v‖ = 1) :
    ‖circlePoint c v‖ ^ 2 = c.radius ^ 2 + 1 - ‖firstEdge c‖ ^ 2 / 2 +
      2 * circleRadius c * ⟪firstMidpoint c, v⟫_ℝ := by
  simp only [circlePoint, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, hv, real_inner_smul_right]
  rw [firstMidpoint_norm_sq, circleRadius_sq]
  ring

/-- The clipping by the enclosing ball is exactly the claimed circular-arc
inequality around the negative midpoint direction. -/
theorem circlePoint_mem_radius_ball_iff (hA : c.totalDeficit ≤ 2 / 25)
    {v : E} (hv : ‖v‖ = 1) :
    circlePoint c v ∈ Metric.closedBall 0 c.radius ↔
      clippingCos c ≤ ⟪v, -NormedSpace.normalize (firstMidpoint c)⟫_ℝ := by
  have hR : 0 ≤ c.radius := by rw [← c.on_sphere 0]; exact norm_nonneg _
  have hr := circleRadius_pos c
  have hm := firstMidpoint_norm_pos c hA
  have hden : 0 < 2 * circleRadius c * ‖firstMidpoint c‖ := by positivity
  have hinner : ⟪v, -NormedSpace.normalize (firstMidpoint c)⟫_ℝ =
      -⟪firstMidpoint c, v⟫_ℝ / ‖firstMidpoint c‖ := by
    simp only [NormedSpace.normalize, inner_neg_right, real_inner_smul_right,
      real_inner_comm v (firstMidpoint c), div_eq_mul_inv]
    ring
  have hcancel : (-⟪firstMidpoint c, v⟫_ℝ / ‖firstMidpoint c‖) *
      (2 * circleRadius c * ‖firstMidpoint c‖) =
        -2 * circleRadius c * ⟪firstMidpoint c, v⟫_ℝ := by
    field_simp
  rw [Metric.mem_closedBall, dist_zero_right,
    ← sq_le_sq₀ (norm_nonneg _) hR, circlePoint_norm_sq c hv,
    clippingCos, hinner, div_le_iff₀ hden, hcancel]
  constructor <;> intro h <;> linarith

end BlaschkeLebesgue.BalancedContacts.Opposite
