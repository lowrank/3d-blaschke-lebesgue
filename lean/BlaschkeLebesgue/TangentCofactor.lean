module

public import BlaschkeLebesgue.MixedTangentDeterminant
public import BlaschkeLebesgue.PositiveTrace

/-!
# Positive tangent cofactors

Compression to the tangent plane preserves positivity. The cofactor of a
positive two-dimensional tangent operator is positive, and a positive tangent
contraction dominates its determinant times the tangent projection.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem tangent_compression_isPositive (u : UnitSphere) {A : Space →L[ℝ] Space}
    (hA : A.IsPositive) :
    ((tangentProjection u).comp (A.comp (tangentProjection u))).IsPositive := by
  have h := hA.conj_adjoint (tangentProjection u)
  rw [(tangentProjection_isPositive u.norm_eq_one).isSelfAdjoint.adjoint_eq] at h
  exact h

theorem tangent_compression_eq (u : UnitSphere) (A : Space →L[ℝ] Space)
    (hAn : A u = 0) (hAt : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0) (a c : ℝ) :
    (tangentProjection u).comp
      ((a • ContinuousLinearMap.id ℝ Space + A + c • normalProjection u).comp
        (tangentProjection u)) = a • tangentProjection u + A := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, tangentProjection_apply, normalProjection_apply,
    map_sub, map_smul, hAn, inner_add_right,
    inner_smul_right, hAt, real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow, mul_one,
    add_zero]
  module

@[expose] def tangentCofactor (u : UnitSphere) (A : Space →L[ℝ] Space) : Space →L[ℝ] Space :=
  LinearMap.trace ℝ Space A.toLinearMap • tangentProjection u - A

theorem tangentCofactor_isPositive (u : UnitSphere) (A : Space →L[ℝ] Space)
    (hA : A.IsPositive) (hAn : A u = 0) (hAt : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0) :
    (tangentCofactor u A).IsPositive := by
  have hp : (LinearMap.trace ℝ Space A.toLinearMap • ContinuousLinearMap.id ℝ Space - A).IsPositive :=
    positive_trace_id_sub hA.toLinearMap
  have h := tangent_compression_isPositive u hp
  have he := tangent_compression_eq u (-A)
    (by simp only [neg_apply, hAn, neg_zero]) (fun v => by simp only [neg_apply, inner_neg_right, hAt, neg_zero])
    (LinearMap.trace ℝ Space A.toLinearMap) 0
  have hz : (0 : ℝ) • normalProjection (u : Space) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, zero_smul, zero_apply]
  rw [hz, add_zero] at he
  simpa only [sub_eq_add_neg, he, tangentCofactor] using h

theorem sphereCurvature_sub_det_tangent_isPositive {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) :
    (sphereCurvature K u - curvatureDet K u • tangentProjection u).IsPositive := by
  have hp : (augmentedCurvature K u - curvatureDet K u • ContinuousLinearMap.id ℝ Space).IsPositive :=
    positiveContraction_sub_det_id (augmentedCurvature_isPositive hKL u).toLinearMap
      (augmentedCurvature_complement_isPositive hKL u).toLinearMap
  have h := tangent_compression_isPositive u hp
  have he := tangent_compression_eq u (sphereCurvature K u)
    (sphereCurvature_apply_normal K u) (sphereCurvature_apply_tangent hKL u) (-curvatureDet K u) 1
  have hmid : augmentedCurvature K u - curvatureDet K u • ContinuousLinearMap.id ℝ Space =
      (-curvatureDet K u) • ContinuousLinearMap.id ℝ Space + sphereCurvature K u +
        (1 : ℝ) • normalProjection u := by
    unfold augmentedCurvature
    module
  rw [hmid, he] at h
  convert h using 1
  module

theorem tangentProjection_comp_eq (u : UnitSphere) (A : Space →L[ℝ] Space)
    (hAt : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0) : (tangentProjection u).comp A = A := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, tangentProjection_apply, hAt, zero_smul, sub_zero]

theorem tangentCofactor_apply_tangent (u : UnitSphere) (A : Space →L[ℝ] Space)
    (hAt : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0) (v : Space) :
    ⟪(u : Space), tangentCofactor u A v⟫_ℝ = 0 := by
  simp only [tangentCofactor, sub_apply, smul_apply, inner_sub_right, inner_smul_right,
    tangentProjection_apply, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    u.norm_eq_one, one_pow, mul_one, sub_self, mul_zero, hAt]

theorem trace_tangentCofactor (u : UnitSphere) (A : Space →L[ℝ] Space) :
    LinearMap.trace ℝ Space (tangentCofactor u A).toLinearMap =
      LinearMap.trace ℝ Space A.toLinearMap := by
  change LinearMap.trace ℝ Space (LinearMap.trace ℝ Space A.toLinearMap •
    (tangentProjection u).toLinearMap - A.toLinearMap) = _
  rw [map_sub, map_smul, trace_tangentProjection, smul_eq_mul]
  ring

end BlaschkeLebesgue
