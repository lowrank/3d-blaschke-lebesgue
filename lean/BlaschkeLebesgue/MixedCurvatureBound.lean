module

public import BlaschkeLebesgue.TangentCofactor

/-!
# A lower bound for the actual mixed curvature

Polarization identifies the mixed determinant with a cofactor trace. Positivity
then gives `2 D2(Q_D,Q_K) ≥ det(Q_D) tr(Q_K)` without selecting a measurable
eigenframe or making an assumption about the relative curvature directions.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem matrix_tangent_mixed_trace (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (hMr : ∀ j, M 0 j = 0) (hMc : ∀ i, M i 0 = 0)
    (hNr : ∀ j, N 0 j = 0) (hNc : ∀ i, N i 0 = 0) :
    (M + N + Matrix.single 0 0 1).det - (M + Matrix.single 0 0 1).det -
      (N + Matrix.single 0 0 1).det = M.trace * N.trace - (M * N).trace := by
  simp [Matrix.det_fin_three, Matrix.add_apply, Matrix.single, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_three, hMr, hMc, hNr, hNc]
  ring

theorem tangentMixedDet_eq_trace (u : UnitSphere) (A B : Space →L[ℝ] Space)
    (hAn : A u = 0) (hAt : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0)
    (hBn : B u = 0) (hBt : ∀ v, ⟪(u : Space), B v⟫_ℝ = 0) :
    2 * tangentMixedDet u A B = LinearMap.trace ℝ Space A.toLinearMap *
      LinearMap.trace ℝ Space B.toLinearMap - LinearMap.trace ℝ Space (A.comp B).toLinearMap := by
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
  change 2 * ((LinearMap.det (A.toLinearMap + B.toLinearMap + (normalProjection u).toLinearMap) -
    LinearMap.det (A.toLinearMap + (normalProjection u).toLinearMap) -
    LinearMap.det (B.toLinearMap + (normalProjection u).toLinearMap)) / 2) = _
  simp only [← LinearMap.det_toMatrix b.toBasis, map_add, hR,
    LinearMap.trace_eq_matrix_trace ℝ b.toBasis, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis]
  rw [matrix_tangent_mixed_trace M N hMr hMc hNr hNc]
  ring

theorem tangentMixedDet_eq_cofactor_trace (u : UnitSphere) (A B : Space →L[ℝ] Space)
    (hAn : A u = 0) (hAt : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0)
    (hBn : B u = 0) (hBt : ∀ v, ⟪(u : Space), B v⟫_ℝ = 0) :
    2 * tangentMixedDet u A B = LinearMap.trace ℝ Space ((tangentCofactor u B).comp A).toLinearMap := by
  rw [tangentMixedDet_eq_trace u A B hAn hAt hBn hBt]
  change _ = LinearMap.trace ℝ Space ((LinearMap.trace ℝ Space B.toLinearMap •
    (tangentProjection u).toLinearMap - B.toLinearMap).comp A.toLinearMap)
  rw [LinearMap.sub_comp, LinearMap.smul_comp, map_sub, map_smul,
    show (tangentProjection u).toLinearMap.comp A.toLinearMap = A.toLinearMap from
      congrArg ContinuousLinearMap.toLinearMap (tangentProjection_comp_eq u A hAt),
    LinearMap.trace_comp_comm']
  simp only [smul_eq_mul, ContinuousLinearMap.toLinearMap_comp]
  ring

theorem mixedCurvature_lower {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (u : UnitSphere) :
    curvatureDet D u * curvatureTrace K u ≤ 2 * mixedCurvature D K u := by
  let C := tangentCofactor u (sphereCurvature K u)
  have hC : C.IsPositive := tangentCofactor_isPositive u _ (sphereCurvature_isPositive hK u)
    (sphereCurvature_apply_normal K u) (sphereCurvature_apply_tangent hK u)
  have h := trace_comp_nonneg (sphereCurvature_sub_det_tangent_isPositive hD u).toLinearMap hC.toLinearMap
  change 0 ≤ LinearMap.trace ℝ Space
    (((sphereCurvature D u).toLinearMap - curvatureDet D u • (tangentProjection u).toLinearMap).comp
      C.toLinearMap) at h
  rw [LinearMap.sub_comp, LinearMap.smul_comp, map_sub, map_smul,
    show (tangentProjection u).toLinearMap.comp C.toLinearMap = C.toLinearMap from
      congrArg ContinuousLinearMap.toLinearMap
        (tangentProjection_comp_eq u C (tangentCofactor_apply_tangent u _
          (sphereCurvature_apply_tangent hK u))), trace_tangentCofactor,
    LinearMap.trace_comp_comm'] at h
  have hm := tangentMixedDet_eq_cofactor_trace u (sphereCurvature D u) (sphereCurvature K u)
    (sphereCurvature_apply_normal D u) (sphereCurvature_apply_tangent hD u)
    (sphereCurvature_apply_normal K u) (sphereCurvature_apply_tangent hK u)
  change 2 * mixedCurvature D K u = LinearMap.trace ℝ Space (C.comp (sphereCurvature D u)).toLinearMap at hm
  change 0 ≤ LinearMap.trace ℝ Space (C.comp (sphereCurvature D u)).toLinearMap -
    curvatureDet D u * curvatureTrace K u at h
  linarith only [h, hm]

end BlaschkeLebesgue
