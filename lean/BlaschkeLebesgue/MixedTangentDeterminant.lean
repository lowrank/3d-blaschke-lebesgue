module

public import BlaschkeLebesgue.TangentDeterminant

/-!
# Polarization of the tangent determinant

The two-dimensional determinant is quadratic. We express its polarization
using ambient determinants with the normal projection added, and prove the
identity in an adapted orthonormal frame.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem matrix_det_tangent_combination (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (hMr : ∀ j, M 0 j = 0) (hMc : ∀ i, M i 0 = 0)
    (hNr : ∀ j, N 0 j = 0) (hNc : ∀ i, N i 0 = 0) (s t : ℝ) :
    (s • M + t • N + Matrix.single 0 0 1).det =
      s ^ 2 * (M + Matrix.single 0 0 1).det +
      s * t * ((M + N + Matrix.single 0 0 1).det -
        (M + Matrix.single 0 0 1).det - (N + Matrix.single 0 0 1).det) +
      t ^ 2 * (N + Matrix.single 0 0 1).det := by
  simp [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, Matrix.single,
    hMr, hMc, hNr, hNc]
  ring

@[expose] def tangentMixedDet (u : UnitSphere) (A B : Space →L[ℝ] Space) : ℝ :=
  ((A + B + normalProjection u).det - (A + normalProjection u).det -
    (B + normalProjection u).det) / 2

theorem det_tangent_combination (u : UnitSphere) (A B : Space →L[ℝ] Space)
    (hAn : A u = 0) (hAt : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0)
    (hBn : B u = 0) (hBt : ∀ v, ⟪(u : Space), B v⟫_ℝ = 0) (s t : ℝ) :
    (s • A + t • B + normalProjection u).det =
      s ^ 2 * (A + normalProjection u).det + 2 * s * t * tangentMixedDet u A B +
        t ^ 2 * (B + normalProjection u).det := by
  obtain ⟨b, hb⟩ := exists_normalFrame u
  let M := LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap
  let N := LinearMap.toMatrix b.toBasis b.toBasis B.toLinearMap
  have hR : LinearMap.toMatrix b.toBasis b.toBasis (normalProjection u).toLinearMap =
      Matrix.single 0 0 1 := by rw [← hb]; exact toMatrix_normalProjection b
  have hMr : ∀ j, M 0 j = 0 := fun j =>
    toMatrix_tangent_row_zero b A (by simpa only [hb] using hAt) j
  have hMc : ∀ i, M i 0 = 0 := fun i =>
    toMatrix_tangent_col_zero b A (by simpa only [hb] using hAn) i
  have hNr : ∀ j, N 0 j = 0 := fun j =>
    toMatrix_tangent_row_zero b B (by simpa only [hb] using hBt) j
  have hNc : ∀ i, N i 0 = 0 := fun i =>
    toMatrix_tangent_col_zero b B (by simpa only [hb] using hBn) i
  unfold tangentMixedDet
  change LinearMap.det (s • A.toLinearMap + t • B.toLinearMap + (normalProjection u).toLinearMap) =
    s ^ 2 * LinearMap.det (A.toLinearMap + (normalProjection u).toLinearMap) +
      2 * s * t * ((LinearMap.det (A.toLinearMap + B.toLinearMap + (normalProjection u).toLinearMap) -
        LinearMap.det (A.toLinearMap + (normalProjection u).toLinearMap) -
        LinearMap.det (B.toLinearMap + (normalProjection u).toLinearMap)) / 2) +
      t ^ 2 * LinearMap.det (B.toLinearMap + (normalProjection u).toLinearMap)
  simp only [← LinearMap.det_toMatrix b.toBasis, map_add, map_smul, hR]
  rw [matrix_det_tangent_combination M N hMr hMc hNr hNc]
  ring

@[expose] def mixedCurvature (D K : ConvexBody Space) (u : UnitSphere) : ℝ :=
  tangentMixedDet u (sphereCurvature D u) (sphereCurvature K u)

theorem curvature_det_combination {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (u : UnitSphere) (s t : ℝ) :
    (s • sphereCurvature D u + t • sphereCurvature K u + normalProjection u).det =
      s ^ 2 * curvatureDet D u + 2 * s * t * mixedCurvature D K u +
        t ^ 2 * curvatureDet K u :=
  det_tangent_combination u _ _ (sphereCurvature_apply_normal D u)
    (sphereCurvature_apply_tangent hD u) (sphereCurvature_apply_normal K u)
    (sphereCurvature_apply_tangent hK u) s t

end BlaschkeLebesgue
