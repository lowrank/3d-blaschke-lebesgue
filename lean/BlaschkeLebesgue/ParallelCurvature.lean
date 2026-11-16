module

public import BlaschkeLebesgue.TangentDeterminant
public import BlaschkeLebesgue.SupportVolumeFormula

/-!
# Parallel-volume coefficients as curvature integrals

The parallel Jacobian is `(h + t) (det Q + t tr Q + t²)` on one common
full-measure subset of the sphere. Integrating this polynomial identifies the
linear and quadratic coefficients of the actual parallel volume.
-/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem inner_tangentProjection (u : UnitSphere) (v : Space) :
    ⟪(u : Space), tangentProjection u v⟫_ℝ = 0 := by
  rw [tangentProjection_apply, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow, mul_one, sub_self]

theorem parallelJacobian_eq_curvature_ae {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, ∀ t : ℝ,
      parallelJacobian K t u = (support K u + t) *
        (curvatureDet K u + t * curvatureTrace K u + t ^ 2) := by
  filter_upwards [normalSupport_sphere_ae_differentiable hKL] with u hu
  intro t
  have hdf := (hasFDerivAt_homogeneousSupport_of_normal u.norm_eq_one hu.hasFDerivAt).fderiv
  change fderiv ℝ (homogeneousSupport K) (u : Space) = sphereCurvature K u +
    (innerSL ℝ (u : Space)).smulRight (normalSupport K u) at hdf
  rw [parallelJacobian, hdf]
  have he : sphereCurvature K u + (innerSL ℝ (u : Space)).smulRight (normalSupport K u) +
      t • ContinuousLinearMap.id ℝ Space =
      sphereCurvature K u + t • tangentProjection u +
        (innerSL ℝ (u : Space)).smulRight (normalSupport K u + t • (u : Space)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      smul_apply, ContinuousLinearMap.id_apply, tangentProjection_apply]
    module
  rw [he, det_tangent_add_normal u.norm_eq_one]
  · rw [curvature_tangent_det_shift hKL u, inner_add_right, inner_smul_right,
      inner_normalSupport, real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow, mul_one]
  · intro v
    simp only [add_apply, smul_apply, inner_add_right, inner_smul_right,
      sphereCurvature_apply_tangent hKL u, inner_tangentProjection, mul_zero, add_zero]

theorem integrable_support_mul_curvatureTrace {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    Integrable (fun u : UnitSphere => support K u * curvatureTrace K u) sphereMeasure := by
  have hi : Integrable (fun u : UnitSphere => support K u) sphereMeasure :=
    (continuous_support_sphere hKL).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply hi.mul_bdd (measurable_curvatureTrace K).aestronglyMeasurable (c := 2)
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (curvatureTrace_bounds hKL u).1]
    exact (curvatureTrace_bounds hKL u).2

theorem integrable_curvatureLinearIntegrand {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    Integrable (fun u : UnitSphere => curvatureDet K u + support K u * curvatureTrace K u)
      sphereMeasure :=
  (integrable_curvatureDet hKL).add (integrable_support_mul_curvatureTrace hKL)

theorem integrable_curvatureQuadraticIntegrand {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    Integrable (fun u : UnitSphere => curvatureTrace K u + support K u) sphereMeasure :=
  (integrable_curvatureTrace hKL).add
    ((continuous_support_sphere hKL).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

theorem integral_parallelJacobian_sphere {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (t : ℝ) :
    (∫ u : UnitSphere, parallelJacobian K t u ∂sphereMeasure) =
      (∫ u : UnitSphere, support K u * curvatureDet K u ∂sphereMeasure) +
      t * (∫ u : UnitSphere, curvatureDet K u + support K u * curvatureTrace K u ∂sphereMeasure) +
      t ^ 2 * (∫ u : UnitSphere, curvatureTrace K u + support K u ∂sphereMeasure) +
      4 * Real.pi * t ^ 3 := by
  have he : (fun u : UnitSphere => parallelJacobian K t u) =ᵐ[sphereMeasure]
      fun u => support K u * curvatureDet K u +
        t * (curvatureDet K u + support K u * curvatureTrace K u) +
        t ^ 2 * (curvatureTrace K u + support K u) + t ^ 3 := by
    filter_upwards [parallelJacobian_eq_curvature_ae hKL] with u hu
    rw [hu t]
    ring
  rw [integral_congr_ae he]
  have h0 := integrable_support_mul_curvatureDet hKL
  have h1 := (integrable_curvatureLinearIntegrand hKL).const_mul t
  have h2 := (integrable_curvatureQuadraticIntegrand hKL).const_mul (t ^ 2)
  have h3 : Integrable (fun _ : UnitSphere => t ^ 3) sphereMeasure := integrable_const _
  have h01 : Integrable (fun u : UnitSphere => support K u * curvatureDet K u +
      t * (curvatureDet K u + support K u * curvatureTrace K u)) sphereMeasure := h0.add h1
  have h012 : Integrable (fun u : UnitSphere => support K u * curvatureDet K u +
      t * (curvatureDet K u + support K u * curvatureTrace K u) +
      t ^ 2 * (curvatureTrace K u + support K u)) sphereMeasure := h01.add h2
  rw [integral_add h012 h3, integral_add h01 h2,
    integral_add h0 h1, integral_const_mul, integral_const_mul, integral_const,
    sphereMeasure_real_univ, smul_eq_mul]

/-- Both identities concern the coefficients already proved to govern actual parallel volume. -/
theorem parallelCoefficients_eq_curvatureIntegrals {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    parallelLinear K = (∫ u : UnitSphere,
        curvatureDet K u + support K u * curvatureTrace K u ∂sphereMeasure) / 3 ∧
      parallelQuadratic K = (∫ u : UnitSphere,
        curvatureTrace K u + support K u ∂sphereMeasure) / 3 := by
  have hp := parallelPolynomial_eq_sphereIntegral hKL h0 (1 : ℝ)
  have hm := parallelPolynomial_eq_sphereIntegral hKL h0 (-1 : ℝ)
  rw [integral_parallelJacobian_sphere hKL, integral_support_curvatureDet hKL h0] at hp hm
  norm_num [parallelPolynomial, parallelConstant_eq_volume hKL h0, bodyVolume_unitBallBody] at hp hm
  constructor <;> linarith only [hp, hm]

end BlaschkeLebesgue
