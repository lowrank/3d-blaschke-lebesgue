module

public import BlaschkeLebesgue.SpectralBounds
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Measurable curvature trace and determinant

Adding the normal projection replaces the zero normal eigenvalue by one.
Its ambient determinant is therefore the tangent determinant, expressed without
a choice of moving frame. Positivity and complementarity give its bounds and
integrability for spherical area measure.
-/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem continuous_normalProjection : Continuous normalProjection :=
  isBoundedBilinearMap_smulRight.continuous.comp
    ((innerSL ℝ).continuous.prodMk continuous_id)

@[expose] def augmentedCurvature (K : ConvexBody Space) (u : UnitSphere) : Space →L[ℝ] Space :=
  sphereCurvature K u + normalProjection u

theorem measurable_augmentedCurvature (K : ConvexBody Space) :
    Measurable (augmentedCurvature K) :=
  (measurable_sphereCurvature K).add
    (continuous_normalProjection.measurable.comp measurable_subtype_coe)

theorem augmentedCurvature_isPositive {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) : (augmentedCurvature K u).IsPositive :=
  (sphereCurvature_isPositive hKL u).add (normalProjection_isPositive u)

theorem augmentedCurvature_complement_isPositive {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) :
    (ContinuousLinearMap.id ℝ Space - augmentedCurvature K u).IsPositive := by
  have he : ContinuousLinearMap.id ℝ Space - augmentedCurvature K u =
      tangentProjection u - sphereCurvature K u := by
    unfold augmentedCurvature tangentProjection normalProjection
    abel
  rw [he]
  exact sphereCurvature_le_tangentProjection hKL u

theorem augmentedCurvature_apply_normal (K : ConvexBody Space) (u : UnitSphere) :
    augmentedCurvature K u u = u := by
  simp only [augmentedCurvature, add_apply, sphereCurvature_apply_normal,
    normalProjection_apply, real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow, one_smul, zero_add]

/-- The tangent determinant, calculated intrinsically using the ambient normal projection. -/
@[expose] def curvatureDet (K : ConvexBody Space) (u : UnitSphere) : ℝ :=
  (augmentedCurvature K u).det

theorem measurable_curvatureDet (K : ConvexBody Space) : Measurable (curvatureDet K) :=
  ContinuousLinearMap.continuous_det.measurable.comp (measurable_augmentedCurvature K)

theorem curvatureDet_bounds {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) :
    0 ≤ curvatureDet K u ∧ curvatureDet K u ≤ 1 :=
  positiveContraction_det_bounds (augmentedCurvature_isPositive hKL u).toLinearMap
    (augmentedCurvature_complement_isPositive hKL u).toLinearMap

theorem trace_augmentedCurvature (K : ConvexBody Space) (u : UnitSphere) :
    LinearMap.trace ℝ Space (augmentedCurvature K u).toLinearMap = curvatureTrace K u + 1 := by
  change LinearMap.trace ℝ Space ((sphereCurvature K u).toLinearMap +
    (innerSL ℝ (u : Space)).toLinearMap.smulRight (u : Space)) = _
  rw [map_add, LinearMap.trace_smulRight]
  change curvatureTrace K u + ⟪(u : Space), (u : Space)⟫_ℝ = curvatureTrace K u + 1
  rw [real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow]

theorem curvatureTrace_sub_one_le_det {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) :
    curvatureTrace K u - 1 ≤ curvatureDet K u := by
  have h := positiveContraction_trace_le_two_add_det
    (augmentedCurvature_isPositive hKL u).toLinearMap
    (augmentedCurvature_complement_isPositive hKL u).toLinearMap u.ne_zero
    (augmentedCurvature_apply_normal K u)
  rw [trace_augmentedCurvature] at h
  change curvatureTrace K u + 1 ≤ 2 + curvatureDet K u at h
  linarith only [h]

theorem measurable_curvatureTrace (K : ConvexBody Space) : Measurable (curvatureTrace K) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  change Measurable (fun u : UnitSphere => LinearMap.trace ℝ Space (sphereCurvature K u).toLinearMap)
  simp_rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.measurable_sum
  intro i hi
  exact ((innerSL ℝ (b i)).continuous.measurable.comp
    ((ContinuousLinearMap.apply ℝ Space (b i)).continuous.measurable.comp
      (measurable_sphereCurvature K)))

theorem integrable_curvatureDet {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) : Integrable (curvatureDet K) sphereMeasure := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_curvatureDet K).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (curvatureDet_bounds hKL u).1]
    exact (curvatureDet_bounds hKL u).2

theorem integrable_curvatureTrace {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) : Integrable (curvatureTrace K) sphereMeasure := by
  apply (integrable_const (2 : ℝ)).mono' (measurable_curvatureTrace K).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (curvatureTrace_bounds hKL u).1]
    exact (curvatureTrace_bounds hKL u).2

end BlaschkeLebesgue
