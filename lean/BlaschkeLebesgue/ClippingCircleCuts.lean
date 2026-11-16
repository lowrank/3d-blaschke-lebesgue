module

public import BlaschkeLebesgue.ClippedVertexAngles
public import BlaschkeLebesgue.ContactCircleBounds

/-!
# The interval removed from an enclosing-sphere circle

For the pair of contacts `0,1`, the other ball removes exactly the angular cap
with the manuscript's half-angle `Psi`. All directions and angles come from
the actual contact positions.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

@[expose] def enclosingCutProjection : E :=
  ClippingCircle.faceTangent (c.clippingCircleAxis 0) (c.point 1)

@[expose] def enclosingCutDirection : E := NormedSpace.normalize (enclosingCutProjection c)

@[expose] def enclosingCutCos : ℝ :=
  (1 - 2 * c.radius ^ 2) * ‖firstEdge c‖ /
    (4 * c.radius * ClippingCircle.radius c.radius * ‖firstMidpoint c‖)

@[expose] def enclosingCutAngle : ℝ := Real.arccos (enclosingCutCos c)

theorem radius_gt_half_of_small_deficit (hA : c.totalDeficit ≤ 2 / 25) :
    1 / 2 < c.radius := by
  have hR : 0 ≤ c.radius := by rw [← c.on_sphere 0]; exact norm_nonneg _
  nlinarith [c.deficit_lower]

theorem firstEdge_norm_pos_of_small_deficit (hA : c.totalDeficit ≤ 2 / 25) :
    0 < ‖firstEdge c‖ := by
  apply norm_pos_iff.2
  apply firstEdge_ne_zero c
  linarith [budgets_sum c, crossBudget_nonneg c]

theorem enclosingCut_axis_inner (hR : 0 < c.radius) :
    ⟪c.clippingCircleAxis 0, c.point 1⟫_ℝ = c.radius - ‖firstEdge c‖ ^ 2 / (2 * c.radius) := by
  have hp : ⟪c.point 0, c.point 1⟫_ℝ = c.radius ^ 2 - ‖firstEdge c‖ ^ 2 / 2 := by
    have h := norm_sub_sq_real (c.point 1) (c.point 0)
    rw [c.on_sphere 0, c.on_sphere 1, real_inner_comm (c.point 0) (c.point 1)] at h
    change ‖firstEdge c‖ ^ 2 = _ at h
    linarith
  rw [clippingCircleAxis, real_inner_smul_left, hp]
  field_simp

theorem enclosingCutProjection_norm (hR : 0 < c.radius) :
    ‖enclosingCutProjection c‖ = ‖firstEdge c‖ * ‖firstMidpoint c‖ / c.radius := by
  have hp := ClippingCircle.faceTangent_inner (v := c.point 1) (w := c.point 1)
    (c.clippingCircleAxis_norm hR 0)
  simp only [real_inner_self_eq_norm_sq, c.on_sphere, enclosingCut_axis_inner c hR] at hp
  have hs : ‖enclosingCutProjection c‖ ^ 2 =
      (‖firstEdge c‖ * ‖firstMidpoint c‖ / c.radius) ^ 2 := by
    change ‖ClippingCircle.faceTangent (c.clippingCircleAxis 0) (c.point 1)‖ ^ 2 = _
    rw [hp, div_pow, mul_pow, firstMidpoint_norm_sq]
    field_simp
    ring
  have hn : 0 ≤ ‖firstEdge c‖ * ‖firstMidpoint c‖ / c.radius := by positivity
  nlinarith [norm_nonneg (enclosingCutProjection c)]

theorem enclosingCutDirection_norm (hA : c.totalDeficit ≤ 2 / 25) :
    ‖enclosingCutDirection c‖ = 1 := by
  have hR : 0 < c.radius := lt_trans (by norm_num) (radius_gt_half_of_small_deficit c hA)
  have hs := firstEdge_norm_pos_of_small_deficit c hA
  have hm := firstMidpoint_norm_pos c hA
  apply NormedSpace.norm_normalize
  apply norm_pos_iff.1
  rw [enclosingCutProjection_norm c hR]
  positivity

theorem enclosingCut_discriminant (hR : 1 / 2 < c.radius) :
    (4 * c.radius * ClippingCircle.radius c.radius * ‖firstMidpoint c‖) ^ 2 -
        ((1 - 2 * c.radius ^ 2) * ‖firstEdge c‖) ^ 2 =
      4 * c.radius ^ 2 * (c.radius ^ 2 * (4 - ‖firstEdge c‖ ^ 2) - 1) := by
  have hR0 : c.radius ≠ 0 := by linarith
  simp only [mul_pow, ClippingCircle.radius_sq hR, firstMidpoint_norm_sq]
  field_simp
  ring

theorem enclosingCutCos_bounds (hA : c.totalDeficit ≤ 2 / 25) :
    0 < enclosingCutCos c ∧ enclosingCutCos c < 1 := by
  have hR := radius_gt_half_of_small_deficit c hA
  have hR0 : 0 < c.radius := by linarith
  have hs := firstEdge_norm_pos_of_small_deficit c hA
  have hm := firstMidpoint_norm_pos c hA
  have hk := ClippingCircle.radius_pos hR
  have hnum : 0 < (1 - 2 * c.radius ^ 2) * ‖firstEdge c‖ :=
    mul_pos (by linarith [c.radius_sq_le (by decide)]) hs
  have hden : 0 < 4 * c.radius * ClippingCircle.radius c.radius * ‖firstMidpoint c‖ := by positivity
  refine ⟨div_pos hnum hden, ?_⟩
  apply (div_lt_one hden).2
  apply (sq_lt_sq₀ hnum.le hden.le).1
  have hd : 0 < c.radius ^ 2 * (4 - ‖firstEdge c‖ ^ 2) - 1 := by
    linarith [clipping_discriminant_lower c]
  have hprod := mul_pos (show 0 < 4 * c.radius ^ 2 by positivity) hd
  linarith [enclosingCut_discriminant c hR]

theorem enclosingCutAngle_bounds (hA : c.totalDeficit ≤ 2 / 25) :
    0 < enclosingCutAngle c ∧ enclosingCutAngle c < Real.pi / 2 := by
  exact ⟨Real.arccos_pos.2 (enclosingCutCos_bounds c hA).2,
    Real.arccos_lt_pi_div_two.2 (enclosingCutCos_bounds c hA).1⟩

theorem inner_enclosingCutDirection (hR : 0 < c.radius) {v : E}
    (hperp : ⟪c.point 0, v⟫_ℝ = 0) :
    ⟪v, c.point 1⟫_ℝ = (‖firstEdge c‖ * ‖firstMidpoint c‖ / c.radius) *
      ⟪v, enclosingCutDirection c⟫_ℝ := by
  have hva : ⟪v, c.clippingCircleAxis 0⟫_ℝ = 0 := by
    rw [clippingCircleAxis, real_inner_smul_right, real_inner_comm (c.point 0) v, hperp, mul_zero]
  have hproj : ⟪v, enclosingCutProjection c⟫_ℝ = ⟪v, c.point 1⟫_ℝ := by
    simp only [enclosingCutProjection, ClippingCircle.faceTangent, inner_sub_right,
      real_inner_smul_right, hva, mul_zero, sub_zero]
  have h := congrArg (fun z ↦ ⟪v, z⟫_ℝ) (NormedSpace.norm_smul_normalize (enclosingCutProjection c))
  simpa only [real_inner_smul_right, enclosingCutProjection_norm c hR, hproj,
    enclosingCutDirection] using h.symm

theorem clippingCircle_mem_other_ball_iff (hA : c.totalDeficit ≤ 2 / 25) {v : E}
    (hv : ‖v‖ = 1) (hperp : ⟪c.point 0, v⟫_ℝ = 0) :
    c.clippingCirclePoint 0 v ∈ Metric.closedBall (c.point 1) 1 ↔
      -enclosingCutCos c ≤ ⟪v, enclosingCutDirection c⟫_ℝ := by
  have hR := radius_gt_half_of_small_deficit c hA
  have hR0 : 0 < c.radius := by linarith
  have hs := firstEdge_norm_pos_of_small_deficit c hA
  have hm := firstMidpoint_norm_pos c hA
  have hk := ClippingCircle.radius_pos hR
  have hden : 0 < 2 * ClippingCircle.radius c.radius * ‖firstMidpoint c‖ := by positivity
  have hscale : 0 < ‖firstEdge c‖ / c.radius := by positivity
  have he : ‖c.point 0 - c.point 1‖ = ‖firstEdge c‖ := by
    rw [firstEdge, norm_sub_rev]
  have hneg : -enclosingCutCos c =
      ClippingCircle.height c.radius * ‖firstEdge c‖ /
        (2 * ClippingCircle.radius c.radius * ‖firstMidpoint c‖) := by
    unfold enclosingCutCos ClippingCircle.height
    field_simp
    ring
  rw [c.clippingCirclePoint_mem_ball_iff hR hv hperp 1, he,
    inner_enclosingCutDirection c hR0 hperp, hneg, div_le_iff₀ hden]
  convert (mul_le_mul_iff_right₀ hscale
    (b := ClippingCircle.height c.radius * ‖firstEdge c‖)
    (c := ⟪v, enclosingCutDirection c⟫_ℝ *
      (2 * ClippingCircle.radius c.radius * ‖firstMidpoint c‖))) using 1
  ring_nf

theorem clippingCircle_excluded_iff_inner (hA : c.totalDeficit ≤ 2 / 25) {v : E}
    (hv : ‖v‖ = 1) (hperp : ⟪c.point 0, v⟫_ℝ = 0) :
    1 < ‖c.clippingCirclePoint 0 v - c.point 1‖ ↔
      enclosingCutCos c < ⟪v, -enclosingCutDirection c⟫_ℝ := by
  have h := not_congr (clippingCircle_mem_other_ball_iff c hA hv hperp)
  simp only [Metric.mem_closedBall, dist_eq_norm, not_le] at h
  rw [h, inner_neg_right]
  constructor <;> intro h <;> linarith

/-- The forbidden interval has precisely the claimed half-angle `Psi`. -/
theorem clippingCircle_excluded_iff_angle (hA : c.totalDeficit ≤ 2 / 25) {v : E}
    (hv : ‖v‖ = 1) (hperp : ⟪c.point 0, v⟫_ℝ = 0) :
    1 < ‖c.clippingCirclePoint 0 v - c.point 1‖ ↔
      InnerProductGeometry.angle v (-enclosingCutDirection c) < enclosingCutAngle c := by
  have hdir : ‖-enclosingCutDirection c‖ = 1 := by rw [norm_neg, enclosingCutDirection_norm c hA]
  have hdot : ⟪v, -enclosingCutDirection c⟫_ℝ ≤ 1 := by
    have h := norm_sub_sq_real v (-enclosingCutDirection c)
    rw [hv, hdir] at h
    nlinarith [sq_nonneg ‖v - -enclosingCutDirection c‖]
  rw [clippingCircle_excluded_iff_inner c hA hv hperp, InnerProductGeometry.angle,
    hv, hdir, mul_one, div_one, enclosingCutAngle]
  constructor
  · intro h
    exact Real.arccos_lt_arccos (by linarith [(enclosingCutCos_bounds c hA).1]) h hdot
  · intro h
    by_contra! hn
    exact (not_lt_of_ge (Real.arccos_le_arccos hn)) h

end BlaschkeLebesgue.BalancedContacts.Opposite
