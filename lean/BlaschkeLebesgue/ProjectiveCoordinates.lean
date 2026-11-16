module

public import BlaschkeLebesgue.ObliqueFrame

/-! # Exact projective coordinates in the common-normal hemisphere -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.ObliqueFrame

variable (f : ObliqueFrame)

@[expose] def planeVector (x y : ℝ) : Space :=
  ((x - f.chi * y) / (1 - f.chi ^ 2)) • f.transverse₁ +
    ((y - f.chi * x) / (1 - f.chi ^ 2)) • f.transverse₂

@[expose] def W (x y : ℝ) : ℝ := 1 + (x ^ 2 + y ^ 2 - 2 * f.chi * x * y) / (1 - f.chi ^ 2)
@[expose] def projectiveNormal (x y : ℝ) : Space := NormedSpace.normalize (f.normal + f.planeVector x y)

theorem normal_inner_planeVector (x y : ℝ) : ⟪f.normal, f.planeVector x y⟫_ℝ = 0 := by
  simp only [planeVector, inner_add_right, real_inner_smul_right,
    f.normal_inner_transverse₁, f.normal_inner_transverse₂, mul_zero, add_zero]

theorem planeVector_first_coordinate (x y : ℝ) : ⟪f.transverse₁, f.planeVector x y⟫_ℝ = x := by
  simp only [planeVector, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    f.transverse₁_norm, f.transverse_inner]
  field_simp [f.one_sub_chi_sq_pos.ne']
  ring

theorem planeVector_second_coordinate (x y : ℝ) : ⟪f.transverse₂, f.planeVector x y⟫_ℝ = y := by
  simp only [planeVector, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    f.transverse₂_norm, real_inner_comm f.transverse₁ f.transverse₂, f.transverse_inner]
  field_simp [f.one_sub_chi_sq_pos.ne']
  ring

theorem planeVector_norm_sq (x y : ℝ) :
    ‖f.planeVector x y‖ ^ 2 = (x ^ 2 + y ^ 2 - 2 * f.chi * x * y) / (1 - f.chi ^ 2) := by
  simp only [planeVector, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    f.transverse₁_norm, f.transverse₂_norm, real_inner_smul_left, real_inner_smul_right,
    f.transverse_inner]
  field_simp [f.one_sub_chi_sq_pos.ne']
  ring

theorem W_eq_norm_sq (x y : ℝ) : f.W x y = 1 + ‖f.planeVector x y‖ ^ 2 := by
  rw [f.planeVector_norm_sq]
  rfl

theorem W_ge_one (x y : ℝ) : 1 ≤ f.W x y := by
  rw [f.W_eq_norm_sq]
  nlinarith [sq_nonneg ‖f.planeVector x y‖]

theorem W_pos (x y : ℝ) : 0 < f.W x y := lt_of_lt_of_le zero_lt_one (f.W_ge_one x y)

theorem normal_add_planeVector_norm (x y : ℝ) :
    ‖f.normal + f.planeVector x y‖ = Real.sqrt (f.W x y) := by
  have hs : ‖f.normal + f.planeVector x y‖ ^ 2 = f.W x y := by
    rw [norm_add_sq_real, f.normal_norm, f.normal_inner_planeVector, f.W_eq_norm_sq]
    ring
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem normal_add_planeVector_ne_zero (x y : ℝ) : f.normal + f.planeVector x y ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [f.normal_add_planeVector_norm]
  exact (Real.sqrt_pos.2 (f.W_pos x y)).ne'

theorem projectiveNormal_norm (x y : ℝ) : ‖f.projectiveNormal x y‖ = 1 :=
  NormedSpace.norm_normalize (f.normal_add_planeVector_ne_zero x y)

theorem projectiveNormal_eq (x y : ℝ) :
    f.projectiveNormal x y = (Real.sqrt (f.W x y))⁻¹ • (f.normal + f.planeVector x y) := by
  rw [projectiveNormal, NormedSpace.normalize, f.normal_add_planeVector_norm]

theorem normal_inner_projectiveNormal (x y : ℝ) :
    ⟪f.normal, f.projectiveNormal x y⟫_ℝ = (Real.sqrt (f.W x y))⁻¹ := by
  rw [f.projectiveNormal_eq, real_inner_smul_right, inner_add_right,
    real_inner_self_eq_norm_sq, f.normal_norm, f.normal_inner_planeVector]
  ring

theorem projectiveNormal_first_projection (x y : ℝ) :
    tangentProjection f.axis₁ (f.projectiveNormal x y) =
      (Real.sqrt (f.W x y))⁻¹ • (f.normal + x • f.transverse₁) := by
  have hm := f.decompose_first (f.planeVector x y)
  rw [f.normal_inner_planeVector, f.planeVector_first_coordinate, zero_smul, zero_add] at hm
  have haxis : ⟪f.axis₁, f.normal⟫_ℝ = 0 := by
    rw [real_inner_comm f.normal f.axis₁, f.normal_inner_axis₁]
  rw [f.projectiveNormal_eq, map_smul, tangentProjection_apply,
    inner_add_right, haxis, zero_add]
  conv_lhs => arg 2; lhs; rhs; rw [hm]
  module

theorem projectiveNormal_second_projection (x y : ℝ) :
    tangentProjection f.axis₂ (f.projectiveNormal x y) =
      (Real.sqrt (f.W x y))⁻¹ • (f.normal + y • f.transverse₂) := by
  have hm := f.decompose_second (f.planeVector x y)
  rw [f.normal_inner_planeVector, f.planeVector_second_coordinate, zero_smul, zero_add] at hm
  have haxis : ⟪f.axis₂, f.normal⟫_ℝ = 0 := by
    rw [real_inner_comm f.normal f.axis₂, f.normal_inner_axis₂]
  rw [f.projectiveNormal_eq, map_smul, tangentProjection_apply,
    inner_add_right, haxis, zero_add]
  conv_lhs => arg 2; lhs; rhs; rw [hm]
  module

theorem normal_add_transverse₁_norm (x : ℝ) :
    ‖f.normal + x • f.transverse₁‖ = Real.sqrt (1 + x ^ 2) := by
  have hs : ‖f.normal + x • f.transverse₁‖ ^ 2 = 1 + x ^ 2 := by
    simp only [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      f.normal_norm, f.transverse₁_norm, real_inner_smul_right, f.normal_inner_transverse₁]
    ring
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem normal_add_transverse₂_norm (y : ℝ) :
    ‖f.normal + y • f.transverse₂‖ = Real.sqrt (1 + y ^ 2) := by
  have hs : ‖f.normal + y • f.transverse₂‖ ^ 2 = 1 + y ^ 2 := by
    simp only [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      f.normal_norm, f.transverse₂_norm, real_inner_smul_right, f.normal_inner_transverse₂]
    ring
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem projectiveNormal_first_projection_norm (x y : ℝ) :
    ‖tangentProjection f.axis₁ (f.projectiveNormal x y)‖ =
      Real.sqrt (1 + x ^ 2) / Real.sqrt (f.W x y) := by
  rw [f.projectiveNormal_first_projection, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.sqrt_pos.2 (f.W_pos x y)), f.normal_add_transverse₁_norm]
  ring

theorem projectiveNormal_second_projection_norm (x y : ℝ) :
    ‖tangentProjection f.axis₂ (f.projectiveNormal x y)‖ =
      Real.sqrt (1 + y ^ 2) / Real.sqrt (f.W x y) := by
  rw [f.projectiveNormal_second_projection, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.sqrt_pos.2 (f.W_pos x y)), f.normal_add_transverse₂_norm]
  ring

theorem W_ge_one_add_first_sq (x y : ℝ) : 1 + x ^ 2 ≤ f.W x y := by
  have h := abs_real_inner_le_norm f.transverse₁ (f.planeVector x y)
  rw [f.planeVector_first_coordinate, f.transverse₁_norm, one_mul] at h
  have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 h
  rw [sq_abs] at hs
  rw [f.W_eq_norm_sq]
  linarith

theorem W_ge_one_add_second_sq (x y : ℝ) : 1 + y ^ 2 ≤ f.W x y := by
  have h := abs_real_inner_le_norm f.transverse₂ (f.planeVector x y)
  rw [f.planeVector_second_coordinate, f.transverse₂_norm, one_mul] at h
  have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 h
  rw [sq_abs] at hs
  rw [f.W_eq_norm_sq]
  linarith

theorem planeVector_neg (x y : ℝ) : f.planeVector (-x) (-y) = -f.planeVector x y := by
  unfold planeVector
  module

theorem W_neg (x y : ℝ) : f.W (-x) (-y) = f.W x y := by unfold W; ring

theorem swap_W (x y : ℝ) : f.swap.W y x = f.W x y := by
  simp only [W, f.swap_chi]
  ring

theorem swap_planeVector (x y : ℝ) : f.swap.planeVector y x = -f.planeVector x y := by
  simp only [planeVector, f.swap_chi, f.swap_transverse₁, f.swap_transverse₂]
  module

theorem swap_projectiveNormal (x y : ℝ) : f.swap.projectiveNormal y x = -f.projectiveNormal x y := by
  rw [projectiveNormal, f.swap_planeVector]
  change NormedSpace.normalize (-f.normal + -f.planeVector x y) = _
  rw [← neg_add, NormedSpace.normalize_neg]
  rfl

end BlaschkeLebesgue.ObliqueFrame
