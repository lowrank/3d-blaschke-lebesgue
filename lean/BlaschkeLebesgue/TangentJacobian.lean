module

public import BlaschkeLebesgue.CurvatureDensity
public import BlaschkeLebesgue.ParallelJacobian

/-!
# The support Jacobian and the tangent determinant

A rank-one determinant identity separates the normal support height from the
tangent derivative. This links the curvature operator to the Jacobian of the
actual homogeneous support parametrization.
-/

public noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem matrix_det_one_add_vecMulVec (v w : Fin 3 → ℝ) :
    (1 + Matrix.vecMulVec v w).det = 1 + ∑ i, w i * v i := by
  simp [Matrix.det_fin_three, Matrix.add_apply, Matrix.vecMulVec_apply, Fin.sum_univ_three]
  ring

theorem det_id_add_smulRight (f : Space →L[ℝ] ℝ) (v : Space) :
    (ContinuousLinearMap.id ℝ Space + f.smulRight v).det = 1 + f v := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  change LinearMap.det (LinearMap.id + f.toLinearMap.smulRight v) = _
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, matrix_det_one_add_vecMulVec]
  congr 1
  calc
    ∑ i, (f.toLinearMap ∘ b) i * b.repr v i = f (∑ i, b.repr v i • b i) := by
      change (∑ i, f (b i) * b.repr v i) = _
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = f v := by rw [b.sum_repr]

theorem det_tangent_add_normal {u : Space} (hu : ‖u‖ = 1)
    (A : Space →L[ℝ] Space) (hA : ∀ v, ⟪u, A v⟫_ℝ = 0) (p : Space) :
    (A + (innerSL ℝ u).smulRight p).det =
      ⟪u, p⟫_ℝ * (A + normalProjection u).det := by
  let B := ContinuousLinearMap.id ℝ Space + (innerSL ℝ u).smulRight (p - u)
  have hfactor : B.comp (A + normalProjection u) = A + (innerSL ℝ u).smulRight p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [B, ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, normalProjection_apply,
      inner_add_right, inner_smul_right, hA, real_inner_self_eq_norm_sq, hu,
      one_pow, mul_one, zero_add]
    module
  rw [← hfactor]
  change LinearMap.det (B.toLinearMap.comp (A + normalProjection u).toLinearMap) = _
  rw [LinearMap.det_comp]
  change B.det * (A + normalProjection u).det = _
  have hB : B.det = ⟪u, p⟫_ℝ := by
    dsimp only [B]
    rw [det_id_add_smulRight]
    simp only [innerSL_apply_apply, inner_sub_right, real_inner_self_eq_norm_sq, hu, one_pow]
    ring
  rw [hB]

theorem hasFDerivAt_homogeneousSupport_of_normal {K : ConvexBody Space}
    {u : Space} (hu : ‖u‖ = 1) {A : Space →L[ℝ] Space}
    (hd : HasFDerivAt (normalSupport K) A u) :
    HasFDerivAt (homogeneousSupport K)
      (A + (innerSL ℝ u).smulRight (normalSupport K u)) u := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hn : HasFDerivAt (fun x : Space => ‖x‖) (innerSL ℝ u) u := by
    simpa only [normalize_eq_self_of_norm_eq_one hu] using hasFDerivAt_space_norm hu0
  change HasFDerivAt ((fun x : Space => ‖x‖) • normalSupport K)
    (A + (innerSL ℝ u).smulRight (normalSupport K u)) u
  simpa only [hu, one_smul] using hn.smul hd

/-- The Jacobian of the actual support parametrization is support height times tangent determinant. -/
theorem homogeneousSupport_det_eq_curvature_ae {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure,
      (fderiv ℝ (homogeneousSupport K) (u : Space)).det = support K u * curvatureDet K u := by
  filter_upwards [normalSupport_sphere_ae_differentiable hKL] with u hu
  rw [(hasFDerivAt_homogeneousSupport_of_normal u.norm_eq_one hu.hasFDerivAt).fderiv,
    det_tangent_add_normal u.norm_eq_one _
      (normalSupport_derivative_tangent hKL u.ne_zero hu.hasFDerivAt), inner_normalSupport]
  rfl

end BlaschkeLebesgue
