module

public import BlaschkeLebesgue.ActiveSupportLocalization

/-! # Necessary support-normal bounds for an intersection of two balls -/

public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_le_ball_face {p y u : E} {r : ℝ} (hu : ‖u‖ = 1)
    (hy : ‖y - p‖ ≤ r) : ⟪u, y⟫_ℝ ≤ ⟪u, p + r • u⟫_ℝ := by
  have h := real_inner_le_norm u (y - p)
  simp only [inner_sub_right, hu, one_mul] at h
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hu, one_pow, mul_one]
  linarith

theorem two_ball_support_axis_upper {p q k x u : E} {d r₀ r₁ t : ℝ}
    (hk : ‖k‖ = 1) (hu : ‖u‖ = 1) (hd : 0 < d) (hr₀ : 0 < r₀) (hr₁ : 0 ≤ r₁)
    (hpq : q - p = d • k) (ht : r₀ ^ 2 + d ^ 2 - r₁ ^ 2 = 2 * d * t)
    (hx₀ : ‖x - p‖ = r₀) (hx₁ : ‖x - q‖ = r₁)
    (hmax : IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (closedBall p r₀ ∩ closedBall q r₁) x) :
    ⟪k, u⟫_ℝ ≤ t / r₀ := by
  by_contra! hn
  have hz : t < r₀ * ⟪k, u⟫_ℝ := by
    have := (div_lt_iff₀ hr₀).1 hn
    linarith
  have hdist : ‖p + r₀ • u - q‖ ^ 2 =
      r₀ ^ 2 + d ^ 2 - 2 * r₀ * d * ⟪k, u⟫_ℝ := by
    have he : p + r₀ • u - q = r₀ • u - d • k := by rw [← hpq]; module
    rw [he, norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, sq_abs, hu, hk,
      mul_one, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm u k]
    ring
  have hy₀ : p + r₀ • u ∈ closedBall p r₀ := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr₀, hu, mul_one, le_refl]
  have hy₁ : p + r₀ • u ∈ closedBall q r₁ := by
    rw [mem_closedBall, dist_eq_norm]
    nlinarith [mul_pos hd (sub_pos.2 hz), norm_nonneg (p + r₀ • u - q)]
  have hm : IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (closedBall p r₀) x := by
    intro y hy
    exact (inner_le_ball_face hu (by simpa only [mem_closedBall, dist_eq_norm] using hy)).trans
      (hmax ⟨hy₀, hy₁⟩)
  have he := eq_ball_face_of_isMaxOn hu hx₀.le hm
  rw [← he, hx₁] at hdist
  nlinarith [mul_pos hd (sub_pos.2 hz)]

theorem two_ball_support_axis_bounds {p q k x u : E} {d r₀ r₁ t : ℝ}
    (hk : ‖k‖ = 1) (hu : ‖u‖ = 1) (hd : 0 < d) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hpq : q - p = d • k) (ht : r₀ ^ 2 + d ^ 2 - r₁ ^ 2 = 2 * d * t)
    (hx₀ : ‖x - p‖ = r₀) (hx₁ : ‖x - q‖ = r₁)
    (hmax : IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (closedBall p r₀ ∩ closedBall q r₁) x) :
    (t - d) / r₁ ≤ ⟪k, u⟫_ℝ ∧ ⟪k, u⟫_ℝ ≤ t / r₀ := by
  refine ⟨?_, two_ball_support_axis_upper hk hu hd hr₀ hr₁.le hpq ht hx₀ hx₁ hmax⟩
  have hpq' : p - q = d • (-k) := by rw [smul_neg, ← hpq]; abel
  have ht' : r₁ ^ 2 + d ^ 2 - r₀ ^ 2 = 2 * d * (d - t) := by nlinarith
  have hm : IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (closedBall q r₁ ∩ closedBall p r₀) x := by
    simpa only [inter_comm] using hmax
  have h := two_ball_support_axis_upper (by simpa only [norm_neg] using hk)
    hu hd hr₁ hr₀.le hpq' ht' hx₁ hx₀ hm
  rw [inner_neg_left] at h
  have he : (d - t) / r₁ = -((t - d) / r₁) := by ring
  rw [he] at h
  linarith

@[expose] def axisProjection (k u : E) : E := u - ⟪k, u⟫_ℝ • k

theorem axisProjection_inner_axis {k : E} (hk : ‖k‖ = 1) (u : E) :
    ⟪k, axisProjection k u⟫_ℝ = 0 := by
  simp only [axisProjection, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hk, one_pow, mul_one, sub_self]

theorem axisProjection_norm_sq {k u : E} (hk : ‖k‖ = 1) (hu : ‖u‖ = 1) :
    ‖axisProjection k u‖ ^ 2 = 1 - ⟪k, u⟫_ℝ ^ 2 := by
  simp only [axisProjection, norm_sub_sq_real, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, hk, hu, real_inner_smul_right, real_inner_comm u k]
  ring

theorem eq_circle_point_of_support {k m x u : E} {r : ℝ}
    (hk : ‖k‖ = 1) (hr : 0 < r) (hp : axisProjection k u ≠ 0)
    (hx : ‖x - m‖ = r) (hxk : ⟪k, x - m⟫_ℝ = 0)
    (hmax : ∀ v, ‖v‖ = 1 → ⟪k, v⟫_ℝ = 0 →
      ⟪u, m + r • v⟫_ℝ ≤ ⟪u, x⟫_ℝ) :
    x = m + r • NormedSpace.normalize (axisProjection k u) := by
  let w := axisProjection k u
  have hw : 0 < ‖w‖ := norm_pos_iff.2 hp
  have hkw : ⟪k, NormedSpace.normalize w⟫_ℝ = 0 := by
    simp only [NormedSpace.normalize, real_inner_smul_right,
      axisProjection_inner_axis hk, mul_zero, w]
  have hup : ⟪u, NormedSpace.normalize w⟫_ℝ = ‖w‖ := by
    have hu : u = w + ⟪k, u⟫_ℝ • k := by dsimp only [w, axisProjection]; module
    conv_lhs => lhs; rw [hu]
    rw [inner_add_left, real_inner_smul_left, hkw, mul_zero, add_zero]
    simp only [NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hm := hmax _ (NormedSpace.norm_normalize hp) hkw
  rw [inner_add_right, real_inner_smul_right, hup] at hm
  have hid : ⟪w, x - m⟫_ℝ = ⟪u, x⟫_ℝ - ⟪u, m⟫_ℝ := by
    change ⟪u - ⟪k, u⟫_ℝ • k, x - m⟫_ℝ = _
    rw [inner_sub_left, real_inner_smul_left, hxk, mul_zero, sub_zero, inner_sub_right]
  have hi : ⟪w, x - m⟫_ℝ = ‖w‖ * ‖x - m‖ := by
    apply le_antisymm (real_inner_le_norm _ _)
    rw [hid, hx]
    nlinarith
  have he := inner_eq_norm_mul_iff_real.1 hi
  rw [hx] at he
  have hd : x - m = r • NormedSpace.normalize w := by
    rw [NormedSpace.normalize, smul_smul]
    apply (smul_right_injective _ hw.ne')
    dsimp only
    rw [smul_smul]
    have hh : ‖w‖ * (r * ‖w‖⁻¹) = r := by field_simp
    rw [hh]
    exact he.symm
  rw [← sub_add_cancel x m, hd]
  abel

end BlaschkeLebesgue
