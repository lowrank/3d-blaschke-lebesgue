module

public import BlaschkeLebesgue.Contacts

/-!
# The circles where the enclosing sphere meets a contact sphere

The centers, radii, and parametrizations below describe actual intersections
of spheres. The remaining ball constraints are reduced to exact linear
inequalities in the circle direction.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

namespace ClippingCircle

@[expose] def radius (R : ℝ) : ℝ := Real.sqrt (1 - 1 / (4 * R ^ 2))
@[expose] def height (R : ℝ) : ℝ := R - 1 / (2 * R)

theorem radius_pos {R : ℝ} (hR : 1 / 2 < R) : 0 < radius R := by
  apply Real.sqrt_pos.2
  have hden : 0 < 4 * R ^ 2 := by positivity
  have hlt : 1 / (4 * R ^ 2) < (1 : ℝ) := (div_lt_one hden).2 (by nlinarith)
  linarith

theorem radius_sq {R : ℝ} (hR : 1 / 2 < R) :
    radius R ^ 2 = 1 - 1 / (4 * R ^ 2) := by
  apply Real.sq_sqrt
  have hden : 0 < 4 * R ^ 2 := by positivity
  have hlt : 1 / (4 * R ^ 2) < (1 : ℝ) := (div_lt_one hden).2 (by nlinarith)
  linarith

theorem height_sq_add_radius_sq {R : ℝ} (hR : 1 / 2 < R) :
    height R ^ 2 + radius R ^ 2 = R ^ 2 := by
  rw [radius_sq hR]
  have hR0 : R ≠ 0 := by linarith
  unfold height
  field_simp
  ring

theorem offset_sq_add_radius_sq {R : ℝ} (hR : 1 / 2 < R) :
    (height R - R) ^ 2 + radius R ^ 2 = 1 := by
  rw [radius_sq hR]
  have hR0 : R ≠ 0 := by linarith
  unfold height
  field_simp
  ring

end ClippingCircle

namespace BalancedContacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (c : BalancedContacts n E)

@[expose] def clippingCircleAxis (i : Fin n) : E := c.radius⁻¹ • c.point i

@[expose] def clippingCirclePoint (i : Fin n) (v : E) : E :=
  ClippingCircle.height c.radius • c.clippingCircleAxis i + ClippingCircle.radius c.radius • v

theorem clippingCircleAxis_norm (hR : 0 < c.radius) (i : Fin n) :
    ‖c.clippingCircleAxis i‖ = 1 := by
  simp only [clippingCircleAxis, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hR, c.on_sphere, inv_mul_cancel₀ hR.ne']

theorem radius_smul_clippingCircleAxis (hR : c.radius ≠ 0) (i : Fin n) :
    c.radius • c.clippingCircleAxis i = c.point i := by
  simp only [clippingCircleAxis, smul_smul, mul_inv_cancel₀ hR, one_smul]

theorem clippingCirclePoint_sub_contact (hR : c.radius ≠ 0) (i : Fin n) (v : E) :
    c.clippingCirclePoint i v - c.point i =
      (ClippingCircle.height c.radius - c.radius) • c.clippingCircleAxis i +
        ClippingCircle.radius c.radius • v := by
  rw [← c.radius_smul_clippingCircleAxis hR i]
  unfold clippingCirclePoint
  module

theorem clippingCircle_combination_norm_sq (hR : 0 < c.radius) {i : Fin n} {v : E}
    (hv : ‖v‖ = 1) (hperp : ⟪c.point i, v⟫_ℝ = 0) (t : ℝ) :
    ‖t • c.clippingCircleAxis i + ClippingCircle.radius c.radius • v‖ ^ 2 =
      t ^ 2 + ClippingCircle.radius c.radius ^ 2 := by
  have hap : ⟪c.clippingCircleAxis i, v⟫_ℝ = 0 := by
    simp only [clippingCircleAxis, real_inner_smul_left, hperp, mul_zero]
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, sq_abs,
    c.clippingCircleAxis_norm hR, hv, mul_one, real_inner_smul_left,
    real_inner_smul_right, hap, mul_zero, add_zero]

theorem clippingCirclePoint_mem_spheres (hR : 1 / 2 < c.radius) {i : Fin n} {v : E}
    (hv : ‖v‖ = 1) (hperp : ⟪c.point i, v⟫_ℝ = 0) :
    c.clippingCirclePoint i v ∈ Metric.sphere 0 c.radius ∧
      c.clippingCirclePoint i v ∈ Metric.sphere (c.point i) 1 := by
  have hR0 : 0 < c.radius := by linarith
  have hn : ‖c.clippingCirclePoint i v‖ ^ 2 = c.radius ^ 2 := by
    exact (c.clippingCircle_combination_norm_sq hR0 hv hperp _).trans
      (ClippingCircle.height_sq_add_radius_sq hR)
  have hd : ‖c.clippingCirclePoint i v - c.point i‖ ^ 2 = 1 := by
    rw [c.clippingCirclePoint_sub_contact hR0.ne', c.clippingCircle_combination_norm_sq hR0 hv hperp]
    exact ClippingCircle.offset_sq_add_radius_sq hR
  simp only [Metric.mem_sphere, dist_eq_norm, sub_zero]
  constructor <;> nlinarith [norm_nonneg (c.clippingCirclePoint i v),
    norm_nonneg (c.clippingCirclePoint i v - c.point i)]

theorem clippingCircle_inner_contact {i : Fin n} {x : E}
    (hR : ‖x‖ = c.radius) (hi : ‖x - c.point i‖ = 1) :
    ⟪x, c.point i⟫_ℝ = c.radius ^ 2 - 1 / 2 := by
  have h := norm_sub_sq_real x (c.point i)
  rw [hR, hi, c.on_sphere i] at h
  nlinarith

theorem clipping_spheres_parametrization (hR : 1 / 2 < c.radius) {i : Fin n} {x : E}
    (hx : x ∈ Metric.sphere 0 c.radius) (hi : x ∈ Metric.sphere (c.point i) 1) :
    ∃ v : E, ‖v‖ = 1 ∧ ⟪c.point i, v⟫_ℝ = 0 ∧ x = c.clippingCirclePoint i v := by
  have hR0 : 0 < c.radius := by linarith
  have hxR : ‖x‖ = c.radius := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  have hxi : ‖x - c.point i‖ = 1 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hi
  have hinner := c.clippingCircle_inner_contact hxR hxi
  have hxa : ⟪x, c.clippingCircleAxis i⟫_ℝ = ClippingCircle.height c.radius := by
    rw [clippingCircleAxis, real_inner_smul_right, hinner]
    unfold ClippingCircle.height
    field_simp
  let d := x - ClippingCircle.height c.radius • c.clippingCircleAxis i
  have hdperp : ⟪c.clippingCircleAxis i, d⟫_ℝ = 0 := by
    simp only [d, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      c.clippingCircleAxis_norm hR0, one_pow, mul_one]
    rw [real_inner_comm, hxa, sub_self]
  have hd : ‖d‖ = ClippingCircle.radius c.radius := by
    have hs : ‖d‖ ^ 2 = c.radius ^ 2 - ClippingCircle.height c.radius ^ 2 := by
      simp only [d, norm_sub_sq_real, hxR, norm_smul, Real.norm_eq_abs,
        sq_abs, c.clippingCircleAxis_norm hR0, mul_one,
        real_inner_smul_right, hxa]
      ring
    nlinarith [ClippingCircle.height_sq_add_radius_sq hR,
      ClippingCircle.radius_pos hR, norm_nonneg d]
  let v := (ClippingCircle.radius c.radius)⁻¹ • d
  have hr := ClippingCircle.radius_pos hR
  refine ⟨v, ?_, ?_, ?_⟩
  · simp only [v, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hd,
      inv_mul_cancel₀ hr.ne']
  · rw [← c.radius_smul_clippingCircleAxis hR0.ne' i]
    simp only [v, real_inner_smul_left, real_inner_smul_right, hdperp, mul_zero]
  · simp only [clippingCirclePoint, v, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    dsimp only [d]
    abel

theorem clippingCirclePoint_sub_sq (hR : 1 / 2 < c.radius) {i : Fin n} {v : E}
    (hv : ‖v‖ = 1) (hperp : ⟪c.point i, v⟫_ℝ = 0) (j : Fin n) :
    ‖c.clippingCirclePoint i v - c.point j‖ ^ 2 =
      1 + ClippingCircle.height c.radius / c.radius * ‖c.point i - c.point j‖ ^ 2 -
        2 * ClippingCircle.radius c.radius * ⟪v, c.point j⟫_ℝ := by
  have hR0 : c.radius ≠ 0 := by linarith
  have hxR : ‖c.clippingCirclePoint i v‖ = c.radius := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      (c.clippingCirclePoint_mem_spheres hR hv hperp).1
  have hij : ⟪c.point i, c.point j⟫_ℝ =
      c.radius ^ 2 - ‖c.point i - c.point j‖ ^ 2 / 2 := by
    have h := norm_sub_sq_real (c.point i) (c.point j)
    rw [c.on_sphere i, c.on_sphere j] at h
    linarith
  rw [norm_sub_sq_real, hxR, c.on_sphere j]
  simp only [clippingCirclePoint, inner_add_left, real_inner_smul_left,
    clippingCircleAxis, hij, ClippingCircle.height]
  field_simp
  ring

theorem clippingCirclePoint_mem_ball_iff (hR : 1 / 2 < c.radius) {i : Fin n} {v : E}
    (hv : ‖v‖ = 1) (hperp : ⟪c.point i, v⟫_ℝ = 0) (j : Fin n) :
    c.clippingCirclePoint i v ∈ Metric.closedBall (c.point j) 1 ↔
      ClippingCircle.height c.radius / c.radius * ‖c.point i - c.point j‖ ^ 2 ≤
        2 * ClippingCircle.radius c.radius * ⟪v, c.point j⟫_ℝ := by
  rw [Metric.mem_closedBall, dist_eq_norm,
    ← sq_le_sq₀ (norm_nonneg _) zero_le_one, one_pow,
    c.clippingCirclePoint_sub_sq hR hv hperp j]
  constructor <;> intro h <;> linarith

end BalancedContacts
end BlaschkeLebesgue
