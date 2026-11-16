module

public import BlaschkeLebesgue.OppositeEdgeBounds

/-! # Constructing a common normal by inverting the two-axis Gram matrix -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[expose] def axisProjectionCoeff (u v w : E) : ℝ :=
  (⟪w, u⟫_ℝ - ⟪u, v⟫_ℝ * ⟪w, v⟫_ℝ) / (1 - ⟪u, v⟫_ℝ ^ 2)

@[expose] def twoAxisResidual (u v w : E) : E :=
  w - (axisProjectionCoeff u v w • u + axisProjectionCoeff v u w • v)

theorem twoAxisResidual_inner_first {u v w : E} (hu : ‖u‖ = 1) (_hv : ‖v‖ = 1)
    (hden : 1 - ⟪u, v⟫_ℝ ^ 2 ≠ 0) : ⟪twoAxisResidual u v w, u⟫_ℝ = 0 := by
  simp only [twoAxisResidual, axisProjectionCoeff, inner_sub_left, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hu, real_inner_comm v u]
  have hden' : 1 - ⟪v, u⟫_ℝ ^ 2 ≠ 0 := by simpa only [real_inner_comm v u] using hden
  field_simp [hden, hden']
  ring

theorem twoAxisResidual_symm (u v w : E) : twoAxisResidual u v w = twoAxisResidual v u w := by
  simp only [twoAxisResidual, add_comm]

theorem twoAxisResidual_inner_second {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hden : 1 - ⟪u, v⟫_ℝ ^ 2 ≠ 0) : ⟪twoAxisResidual u v w, v⟫_ℝ = 0 := by
  rw [twoAxisResidual_symm]
  exact twoAxisResidual_inner_first hv hu (by simpa only [real_inner_comm v u] using hden)

theorem twoAxisResidual_inner_self {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hden : 1 - ⟪u, v⟫_ℝ ^ 2 ≠ 0) :
    ⟪w, twoAxisResidual u v w⟫_ℝ = ‖twoAxisResidual u v w‖ ^ 2 := by
  have h1 := twoAxisResidual_inner_first (w := w) hu hv hden
  have h2 := twoAxisResidual_inner_second (w := w) hu hv hden
  have hid : w = twoAxisResidual u v w +
      (axisProjectionCoeff u v w • u + axisProjectionCoeff v u w • v) := by
    unfold twoAxisResidual
    abel
  conv_lhs => lhs; rw [hid]
  rw [inner_add_left, real_inner_self_eq_norm_sq, inner_add_left,
    real_inner_smul_left, real_inner_smul_left,
    real_inner_comm (twoAxisResidual u v w) u,
    real_inner_comm (twoAxisResidual u v w) v, h1, h2]
  ring

/-- A deliberately loose rational coefficient bound, used only to certify that
the normal residual is nonzero. The sharp geometric estimates are retained
separately for the integration rectangle. -/
theorem axisProjectionCoeff_abs_le {u v w : E}
    (hc : |⟪u, v⟫_ℝ| ≤ 1 / 25) (hp : |⟪w, u⟫_ℝ| ≤ 1 / 40)
    (hq : |⟪w, v⟫_ℝ| ≤ 1 / 40) : |axisProjectionCoeff u v w| ≤ 1 / 32 := by
  have hc' := abs_le.mp hc
  have hsq : ⟪u, v⟫_ℝ ^ 2 ≤ (1 / 25 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 25 - ⟪u, v⟫_ℝ by linarith)
      (show 0 ≤ 1 / 25 + ⟪u, v⟫_ℝ by linarith)]
  have hd : 0 < 1 - ⟪u, v⟫_ℝ ^ 2 := by linarith
  have habs := abs_sub ⟪w, u⟫_ℝ (⟪u, v⟫_ℝ * ⟪w, v⟫_ℝ)
  rw [abs_mul] at habs
  have hprod := mul_le_mul hc hq (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 25)
  unfold axisProjectionCoeff
  rw [abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  linarith

/-- Explicitly construct a unit vector perpendicular to both nearly orthogonal
axes and oriented toward a separated midpoint. -/
theorem exists_common_normal {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hc : |⟪u, v⟫_ℝ| ≤ 1 / 25) (hp : |⟪w, u⟫_ℝ| ≤ 1 / 40)
    (hq : |⟪w, v⟫_ℝ| ≤ 1 / 40) (hw : 1 / 4 < ‖w‖ ^ 2) :
    ∃ z : E, ‖z‖ = 1 ∧ ⟪z, u⟫_ℝ = 0 ∧ ⟪z, v⟫_ℝ = 0 ∧ 0 < ⟪w, z⟫_ℝ := by
  have hc' := abs_le.mp hc
  have hden : 1 - ⟪u, v⟫_ℝ ^ 2 ≠ 0 := by
    have hh := mul_nonneg (show 0 ≤ 1 / 25 - ⟪u, v⟫_ℝ by linarith)
      (show 0 ≤ 1 / 25 + ⟪u, v⟫_ℝ by linarith)
    nlinarith
  have hp' := axisProjectionCoeff_abs_le hc hp hq
  have hq' := axisProjectionCoeff_abs_le
    (show |⟪v, u⟫_ℝ| ≤ 1 / 25 by simpa only [real_inner_comm v u] using hc) hq hp
  have hne : twoAxisResidual u v w ≠ 0 := by
    intro hz
    have heq : w = axisProjectionCoeff u v w • u + axisProjectionCoeff v u w • v :=
      sub_eq_zero.mp hz
    have hn := norm_add_le (axisProjectionCoeff u v w • u) (axisProjectionCoeff v u w • v)
    rw [← heq, norm_smul, norm_smul, hu, hv, Real.norm_eq_abs, Real.norm_eq_abs] at hn
    have hsmall : ‖w‖ ≤ 1 / 16 := by linarith
    nlinarith [norm_nonneg w]
  let z := NormedSpace.normalize (twoAxisResidual u v w)
  refine ⟨z, NormedSpace.norm_normalize hne, ?_, ?_, ?_⟩
  · simp only [z, NormedSpace.normalize, real_inner_smul_left,
      twoAxisResidual_inner_first hu hv hden, mul_zero]
  · simp only [z, NormedSpace.normalize, real_inner_smul_left,
      twoAxisResidual_inner_second hu hv hden, mul_zero]
  · simp only [z, NormedSpace.normalize, real_inner_smul_right,
      twoAxisResidual_inner_self hu hv hden]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hne)) (sq_pos_of_pos (norm_pos_iff.mpr hne))

end BlaschkeLebesgue
