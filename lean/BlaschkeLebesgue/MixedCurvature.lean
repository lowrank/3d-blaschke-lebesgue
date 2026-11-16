module

public import BlaschkeLebesgue.MixedTangentDeterminant

/-!
# Measurability and integrability of mixed curvature

The midpoint of two positive contractions is again a positive contraction.
The quadratic determinant identity consequently bounds its mixed coefficient,
which is enough for all integrability statements used in volume variation.
-/

public noncomputable section

open MeasureTheory Set Filter

namespace BlaschkeLebesgue

theorem mixedCurvature_bounds {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (u : UnitSphere) :
    -1 ≤ mixedCurvature D K u ∧ mixedCurvature D K u ≤ 2 := by
  let A := (1 / 2 : ℝ) • sphereCurvature D u + (1 / 2 : ℝ) • sphereCurvature K u +
    normalProjection u
  have he : A = (1 / 2 : ℝ) • augmentedCurvature D u +
      (1 / 2 : ℝ) • augmentedCurvature K u := by
    unfold A augmentedCurvature
    module
  have hA : A.IsPositive := by
    rw [he]
    exact ((augmentedCurvature_isPositive hD u).smul_of_nonneg (by norm_num)).add
      ((augmentedCurvature_isPositive hK u).smul_of_nonneg (by norm_num))
  have hI : (ContinuousLinearMap.id ℝ Space - A).IsPositive := by
    have hi : ContinuousLinearMap.id ℝ Space - A =
        (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ Space - augmentedCurvature D u) +
        (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ Space - augmentedCurvature K u) := by
      rw [he]
      module
    rw [hi]
    exact ((augmentedCurvature_complement_isPositive hD u).smul_of_nonneg (by norm_num)).add
      ((augmentedCurvature_complement_isPositive hK u).smul_of_nonneg (by norm_num))
  obtain ⟨hlo, hhi⟩ := positiveContraction_det_bounds hA.toLinearMap hI.toLinearMap
  have hpoly := curvature_det_combination hD hK u (1 / 2) (1 / 2)
  change A.det = _ at hpoly
  change 0 ≤ A.det at hlo
  change A.det ≤ 1 at hhi
  obtain ⟨hd0, hd1⟩ := curvatureDet_bounds hD u
  obtain ⟨hk0, hk1⟩ := curvatureDet_bounds hK u
  constructor <;> nlinarith only [hpoly, hlo, hhi, hd0, hd1, hk0, hk1]

theorem measurable_mixedCurvature (D K : ConvexBody Space) : Measurable (mixedCurvature D K) := by
  have hsum : Measurable (fun u : UnitSphere =>
      sphereCurvature D u + sphereCurvature K u + normalProjection u) :=
    ((measurable_sphereCurvature D).add (measurable_sphereCurvature K)).add
      (continuous_normalProjection.measurable.comp measurable_subtype_coe)
  exact (((ContinuousLinearMap.continuous_det.measurable.comp hsum).sub
    (measurable_curvatureDet D)).sub (measurable_curvatureDet K)).div_const 2

theorem integrable_mixedCurvature {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) :
    Integrable (mixedCurvature D K) sphereMeasure := by
  apply (integrable_const (2 : ℝ)).mono' (measurable_mixedCurvature D K).aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨hlo, hhi⟩ := mixedCurvature_bounds hD hK u
    exact ⟨by linarith only [hlo], hhi⟩

end BlaschkeLebesgue
