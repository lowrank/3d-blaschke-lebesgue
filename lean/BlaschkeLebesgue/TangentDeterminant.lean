module

public import BlaschkeLebesgue.NormalFrame

/-!
# The quadratic tangent determinant

For an operator that kills the normal and has tangent range, its tangent
determinant under scaling and parallel shift is a quadratic. The proof uses
an adapted orthonormal basis and the ordinary three-by-three determinant.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem matrix_det_tangent_smul_shift (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hrow : ∀ j, M 0 j = 0) (hcol : ∀ i, M i 0 = 0) (s t : ℝ) :
    (s • M + t • (1 - Matrix.single 0 0 1) + Matrix.single 0 0 1).det =
      s ^ 2 * (M + Matrix.single 0 0 1).det + s * t * M.trace + t ^ 2 := by
  simp [Matrix.det_fin_three, Matrix.trace, Matrix.diag_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.single, Fin.sum_univ_three, hrow, hcol]
  ring

theorem det_tangent_smul_shift (u : UnitSphere) (A : Space →L[ℝ] Space)
    (hAn : A u = 0) (hAt : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0) (s t : ℝ) :
    (s • A + t • tangentProjection u + normalProjection u).det =
      s ^ 2 * (A + normalProjection u).det +
        s * t * LinearMap.trace ℝ Space A.toLinearMap + t ^ 2 := by
  obtain ⟨b, hb⟩ := exists_normalFrame u
  let M := LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap
  have hR : LinearMap.toMatrix b.toBasis b.toBasis (normalProjection u).toLinearMap =
      Matrix.single 0 0 1 := by
    rw [← hb]
    exact toMatrix_normalProjection b
  have hN : LinearMap.toMatrix b.toBasis b.toBasis (tangentProjection u).toLinearMap =
      1 - Matrix.single 0 0 1 := by
    change LinearMap.toMatrix b.toBasis b.toBasis
      (LinearMap.id - (normalProjection u).toLinearMap) = _
    rw [map_sub, LinearMap.toMatrix_id, hR]
  have hrow : ∀ j, M 0 j = 0 := fun j =>
    toMatrix_tangent_row_zero b A (by simpa only [hb] using hAt) j
  have hcol : ∀ i, M i 0 = 0 := fun i =>
    toMatrix_tangent_col_zero b A (by simpa only [hb] using hAn) i
  have hdet : (A + normalProjection u).det = (M + Matrix.single 0 0 1).det := by
    change LinearMap.det (A.toLinearMap + (normalProjection u).toLinearMap) = _
    rw [← LinearMap.det_toMatrix b.toBasis, map_add, hR]
  rw [hdet, LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  change LinearMap.det (s • A.toLinearMap + t • (tangentProjection u).toLinearMap +
    (normalProjection u).toLinearMap) = _
  rw [← LinearMap.det_toMatrix b.toBasis, map_add, map_add, map_smul, map_smul, hN, hR]
  exact matrix_det_tangent_smul_shift M hrow hcol s t

theorem curvature_tangent_det_shift {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) (t : ℝ) :
    (sphereCurvature K u + t • tangentProjection u + normalProjection u).det =
      curvatureDet K u + t * curvatureTrace K u + t ^ 2 := by
  simpa only [one_smul, one_pow, one_mul, curvatureDet, augmentedCurvature, curvatureTrace] using
    det_tangent_smul_shift u (sphereCurvature K u) (sphereCurvature_apply_normal K u)
      (sphereCurvature_apply_tangent hKL u) 1 t

theorem curvatureDet_complement_ae {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure,
      curvatureDet L u = 1 - curvatureTrace K u + curvatureDet K u := by
  filter_upwards [sphereCurvature_complement_ae hKL] with u hu
  have h := det_tangent_smul_shift u (sphereCurvature K u) (sphereCurvature_apply_normal K u)
    (sphereCurvature_apply_tangent hKL u) (-1) 1
  rw [curvatureDet, augmentedCurvature, hu]
  have he : tangentProjection u - sphereCurvature K u + normalProjection u =
      (-1 : ℝ) • sphereCurvature K u + (1 : ℝ) • tangentProjection u + normalProjection u := by
    module
  rw [he, h]
  change (-1 : ℝ) ^ 2 * curvatureDet K u + (-1 : ℝ) * 1 * curvatureTrace K u + 1 ^ 2 = _
  ring

end BlaschkeLebesgue
