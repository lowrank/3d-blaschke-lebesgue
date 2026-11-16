module

public import BlaschkeLebesgue.RadialProjectiveMap

/-! # The exact three-dimensional projective Jacobian -/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem matrix_det_radial_projective (n₀ n₁ n₂ a b t c s : ℝ) :
    Matrix.det !![n₀, -t * a * n₀, -t * b * n₀;
      n₁, t * (c / s - a * n₁), t * (-(1 / s) - b * n₁);
      n₂, t * (1 - a * n₂), -t * b * n₂] = t ^ 2 * n₀ / s := by
  simp [Matrix.det_fin_three]
  ring

namespace ObliqueFrame

variable (f : ObliqueFrame)

theorem det_radialProjectiveDeriv (p : Space) :
    (f.radialProjectiveDeriv p).det = ⟪f.normal, p⟫_ℝ ^ 2 /
      (f.sine * Real.sqrt (f.W ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ) ^ 3) := by
  obtain ⟨b, hb0, hb1, hb2⟩ := f.exists_first_basis
  let n := NormedSpace.normalize (f.projectiveLift p)
  let t := ⟪f.normal, p⟫_ℝ / ‖f.projectiveLift p‖
  let a := ⟪n, f.projectivePlaneMap f.axis₁⟫_ℝ
  let d := ⟪n, f.projectivePlaneMap f.transverse₁⟫_ℝ
  have hm : LinearMap.toMatrix b.toBasis b.toBasis (f.radialProjectiveDeriv p).toLinearMap =
      !![⟪f.normal, n⟫_ℝ, -t * a * ⟪f.normal, n⟫_ℝ, -t * d * ⟪f.normal, n⟫_ℝ;
        ⟪f.axis₁, n⟫_ℝ, t * (f.chi / f.sine - a * ⟪f.axis₁, n⟫_ℝ),
          t * (-(1 / f.sine) - d * ⟪f.axis₁, n⟫_ℝ);
        ⟪f.transverse₁, n⟫_ℝ, t * (1 - a * ⟪f.transverse₁, n⟫_ℝ), -t * d * ⟪f.transverse₁, n⟫_ℝ] := by
    ext i j
    rw [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply]
    simp only [OrthonormalBasis.coe_toBasis]
    fin_cases i <;> fin_cases j <;>
      norm_num [hb0, hb1, hb2, f.radialProjectiveDeriv_apply,
        f.projectivePlaneMap_normal, f.normal_inner_axis₁, f.normal_inner_transverse₁,
        real_inner_self_eq_norm_sq, f.normal_norm, inner_add_right, inner_sub_right, real_inner_smul_right,
        t, a, d, n, f.projectivePlaneMap_axis₁, f.projectivePlaneMap_transverse₁,
        inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, f.axis₁_norm, f.transverse₁_norm,
        f.normal_inner_axis₁, f.normal_inner_transverse₁, f.axis₁_inner_transverse₁,
        real_inner_comm f.axis₁ f.transverse₁] <;> ring
  change (f.radialProjectiveDeriv p).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix b.toBasis, hm, matrix_det_radial_projective]
  have hn : n = f.projectiveNormal ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ := by
    dsimp only [n]
    rw [f.projectiveLift_eq]
    rfl
  rw [hn, f.normal_inner_projectiveNormal]
  dsimp only [t]
  rw [f.projectiveLift_norm]
  ring

theorem abs_det_fderiv_radialProjectiveMap (p : Space) :
    |(fderiv ℝ f.radialProjectiveMap p).det| = ⟪f.normal, p⟫_ℝ ^ 2 /
      (f.sine * Real.sqrt (f.W ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ) ^ 3) := by
  rw [(f.hasFDerivAt_radialProjectiveMap p).fderiv, f.det_radialProjectiveDeriv]
  exact abs_of_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg f.sine_pos.le (by positivity)))

theorem integral_image_radialProjectiveMap {s : Set Space} (hs : MeasurableSet s)
    (hpos : s ⊆ {p : Space | 0 < ⟪f.normal, p⟫_ℝ}) (g : Space → ℝ) :
    (∫ q in f.radialProjectiveMap '' s, g q) =
      ∫ p in s, (⟪f.normal, p⟫_ℝ ^ 2 /
        (f.sine * Real.sqrt (f.W ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ) ^ 3)) * g (f.radialProjectiveMap p) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun p (_ : p ∈ s) ↦ (f.hasFDerivAt_radialProjectiveMap p).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (f.radialProjectiveMap_injOn.mono hpos) g
  simpa only [f.abs_det_fderiv_radialProjectiveMap, smul_eq_mul] using h

end ObliqueFrame
end BlaschkeLebesgue
