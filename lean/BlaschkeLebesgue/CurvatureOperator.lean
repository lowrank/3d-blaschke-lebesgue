module

public import BlaschkeLebesgue.SphericalDifferentiation
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The actual measurable curvature operator

The ambient derivative of the normalized support map is the curvature operator:
it vanishes in the normal direction and acts on the tangent plane. At exceptional
directions `fderiv` is zero. Every operator is a positive contraction, and the
complement identity holds almost everywhere for spherical area measure.
-/

public noncomputable section

open MeasureTheory Set NormedSpace
open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def normalProjection (u : Space) : Space →L[ℝ] Space :=
  (innerSL ℝ u).smulRight u

theorem normalProjection_apply (u v : Space) : normalProjection u v = ⟪u, v⟫_ℝ • u := rfl

theorem normalProjection_isPositive (u : Space) : (normalProjection u).IsPositive := by
  constructor
  · intro v w
    change ⟪normalProjection u v, w⟫_ℝ = ⟪v, normalProjection u w⟫_ℝ
    simp only [normalProjection_apply, real_inner_smul_left, inner_smul_right]
    rw [real_inner_comm v u, mul_comm]
  · intro v
    change 0 ≤ ⟪normalProjection u v, v⟫_ℝ
    simp only [normalProjection_apply, real_inner_smul_left]
    exact mul_self_nonneg _

theorem tangentProjection_isPositive {u : Space} (hu : ‖u‖ = 1) :
    (tangentProjection u).IsPositive := by
  constructor
  · exact ContinuousLinearMap.isPositive_id.isSymmetric.sub
      (normalProjection_isPositive u).isSymmetric
  · intro v
    change 0 ≤ ⟪tangentProjection u v, v⟫_ℝ
    simp only [tangentProjection_apply, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have h := norm_inner_le_norm (𝕜 := ℝ) u v
    rw [hu, one_mul, Real.norm_eq_abs] at h
    have hs := (sq_le_sq₀ (abs_nonneg ⟪u, v⟫_ℝ) (norm_nonneg v)).2 h
    nlinarith only [hs, sq_abs ⟪u, v⟫_ℝ]

theorem normalSupport_derivative_isPositive {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {x : Space} (hx : x ≠ 0)
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (normalSupport K) A x) : A.IsPositive := by
  constructor
  · intro v w
    exact (normalSupport_derivative_symmetric hKL hx hd v w).trans (real_inner_comm _ _)
  · exact normalSupport_derivative_nonneg hd

/-- The derivative is used itself, with the standard zero value at nondifferentiable points. -/
@[expose] def sphereCurvature (K : ConvexBody Space) (u : UnitSphere) : Space →L[ℝ] Space :=
  fderiv ℝ (normalSupport K) (u : Space)

theorem measurable_sphereCurvature (K : ConvexBody Space) : Measurable (sphereCurvature K) :=
  (measurable_fderiv ℝ (normalSupport K)).comp measurable_subtype_coe

theorem sphereCurvature_isPositive {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) : (sphereCurvature K u).IsPositive := by
  by_cases hd : DifferentiableAt ℝ (normalSupport K) (u : Space)
  · exact normalSupport_derivative_isPositive hKL u.ne_zero hd.hasFDerivAt
  · simp only [sphereCurvature, fderiv_zero_of_not_differentiableAt hd]
    exact ContinuousLinearMap.isPositive_zero

theorem sphereCurvature_apply_normal (K : ConvexBody Space) (u : UnitSphere) :
    sphereCurvature K u u = 0 := by
  by_cases hd : DifferentiableAt ℝ (normalSupport K) (u : Space)
  · exact normalSupport_derivative_radial hd.hasFDerivAt
  · simp only [sphereCurvature, fderiv_zero_of_not_differentiableAt hd, zero_apply]

theorem sphereCurvature_apply_tangent {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) (v : Space) :
    ⟪(u : Space), sphereCurvature K u v⟫_ℝ = 0 := by
  have h := (sphereCurvature_isPositive hKL u).isSymmetric (u : Space) v
  change ⟪sphereCurvature K u u, v⟫_ℝ = ⟪(u : Space), sphereCurvature K u v⟫_ℝ at h
  rw [sphereCurvature_apply_normal, inner_zero_left] at h
  exact h.symm

theorem sphereCurvature_le_tangentProjection {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) :
    sphereCurvature K u ≤ tangentProjection u := by
  by_cases hd : DifferentiableAt ℝ (normalSupport K) (u : Space)
  · exact normalSupport_derivative_isPositive (K := L) (L := K)
      (by simpa only [add_comm L K] using hKL)
      u.ne_zero (normalSupport_complement_derivative hKL u.norm_eq_one hd.hasFDerivAt)
  · simp only [sphereCurvature, fderiv_zero_of_not_differentiableAt hd,
      ContinuousLinearMap.nonneg_iff_isPositive]
    exact tangentProjection_isPositive u.norm_eq_one

/-- Complementary bodies have complementary tangent curvature operators almost everywhere. -/
theorem sphereCurvature_complement_ae {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure,
      sphereCurvature L u = tangentProjection u - sphereCurvature K u := by
  filter_upwards [normalSupport_sphere_ae_differentiable hKL] with u hu
  exact (normalSupport_complement_derivative hKL u.norm_eq_one hu.hasFDerivAt).fderiv

theorem trace_tangentProjection (u : UnitSphere) :
    LinearMap.trace ℝ Space (tangentProjection u).toLinearMap = 2 := by
  change LinearMap.trace ℝ Space
    (LinearMap.id - (innerSL ℝ (u : Space)).toLinearMap.smulRight (u : Space)) = _
  rw [map_sub, LinearMap.trace_id, LinearMap.trace_smulRight]
  norm_num [Space, u.norm_eq_one]

@[expose] def curvatureTrace (K : ConvexBody Space) (u : UnitSphere) : ℝ :=
  LinearMap.trace ℝ Space (sphereCurvature K u).toLinearMap

theorem curvatureTrace_bounds {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) :
    0 ≤ curvatureTrace K u ∧ curvatureTrace K u ≤ 2 := by
  refine ⟨(sphereCurvature_isPositive hKL u).toLinearMap.trace_nonneg, ?_⟩
  have h := (sphereCurvature_le_tangentProjection hKL u).toLinearMap.trace_nonneg
  change 0 ≤ LinearMap.trace ℝ Space
    ((tangentProjection u).toLinearMap - (sphereCurvature K u).toLinearMap) at h
  rw [map_sub, trace_tangentProjection] at h
  exact (sub_nonneg.1 h)

end BlaschkeLebesgue
