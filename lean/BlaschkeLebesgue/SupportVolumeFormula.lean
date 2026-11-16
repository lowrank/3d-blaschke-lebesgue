module

public import BlaschkeLebesgue.HomogeneousDifferentiation
public import BlaschkeLebesgue.PolarHomogeneous
public import BlaschkeLebesgue.ParallelPolynomial

/-!
# The actual volume as a support-curvature integral

Degree-zero homogeneity converts the proved ambient Jacobian formula to a
spherical integral. The tangent determinant identity then proves the support
formula `3 V(K) = ∫ h_K det Q_K` for actual summands of the unit ball.
-/

public noncomputable section

open MeasureTheory Set NormedSpace
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem parallelPolynomial_eq_sphereIntegral {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) (t : ℝ) :
    parallelPolynomial K t =
      (∫ u : UnitSphere, parallelJacobian K t u ∂sphereMeasure) / 3 := by
  rw [parallelPolynomial_eq_integral hKL h0]
  exact integral_closedBall_homogeneous_zero _ fun r hr x => parallelJacobian_smul K t x hr

theorem continuous_support_sphere {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) : Continuous (fun u : UnitSphere => support K u) := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (hasFDerivAt_support hKL u.ne_zero).continuousAt.comp
    continuous_subtype_val.continuousAt

theorem integrable_support_mul_curvatureDet {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    Integrable (fun u : UnitSphere => support K u * curvatureDet K u) sphereMeasure := by
  have hi : Integrable (fun u : UnitSphere => support K u) sphereMeasure :=
    (continuous_support_sphere hKL).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  apply hi.mono
    ((continuous_support_sphere hKL).aestronglyMeasurable.mul
      (measurable_curvatureDet K).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun u => by
    change ‖support K u * curvatureDet K u‖ ≤ ‖support K u‖
    rw [norm_mul, Real.norm_eq_abs (curvatureDet K u),
      abs_of_nonneg (curvatureDet_bounds hKL u).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (curvatureDet_bounds hKL u).2

/-- The volume formula for actual, possibly nonsmooth, summands of the unit ball. -/
theorem bodyVolume_eq_integral_support_curvature {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    bodyVolume K = (∫ u : UnitSphere, support K u * curvatureDet K u ∂sphereMeasure) / 3 := by
  calc
    bodyVolume K = parallelPolynomial K 0 := by
      simp only [parallelPolynomial, zero_mul, zero_pow (by omega : 2 ≠ 0),
        zero_pow (by omega : 3 ≠ 0), add_zero, parallelConstant_eq_volume hKL h0]
    _ = (∫ u : UnitSphere, parallelJacobian K 0 u ∂sphereMeasure) / 3 :=
      parallelPolynomial_eq_sphereIntegral hKL h0 0
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [homogeneousSupport_det_eq_curvature_ae hKL] with u hu
      change (fderiv ℝ (homogeneousSupport K) (u : Space) +
        (0 : ℝ) • ContinuousLinearMap.id ℝ Space).det = _
      rw [zero_smul ℝ (ContinuousLinearMap.id ℝ Space), add_zero]
      exact hu

theorem integral_support_curvatureDet {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    (∫ u : UnitSphere, support K u * curvatureDet K u ∂sphereMeasure) = 3 * bodyVolume K := by
  rw [bodyVolume_eq_integral_support_curvature hKL h0]
  ring

end BlaschkeLebesgue
