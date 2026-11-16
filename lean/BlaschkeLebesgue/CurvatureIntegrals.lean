module

public import BlaschkeLebesgue.BallCurvature

/-!
# Area and mean coefficient as curvature and support integrals

Variation from an actual inner ball identifies the mean coefficient with the
integral of the support function. Area variation then supplies the integration
identity needed to identify surface area with the integral of tangent curvature.
-/

public noncomputable section

open MeasureTheory Set Filter

namespace BlaschkeLebesgue

theorem integrable_support_sphere {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) : Integrable (fun u : UnitSphere => support K u) sphereMeasure :=
  (continuous_support_sphere hKL).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem parallelQuadratic_eq_integral_support {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    parallelQuadratic K = ∫ u : UnitSphere, support K u ∂sphereMeasure := by
  obtain ⟨r, hr, hr1, hsub⟩ := exists_inner_scaledBall h0
  have h := mean_coefficient_variation (scaledBall_complement hr.le hr1) hKL hsub
    (scaledBall_zero_mem_interior hr)
  rw [(scaledBall_parallelCoefficients hr hr1).2] at h
  have he : supportGap (r • unitBallBody) K = fun u : UnitSphere => support K u - r := by
    funext u
    rw [supportGap, support_scaledBall hr.le u.norm_eq_one]
  rw [he, integral_sub (integrable_support_sphere hKL) (integrable_const r), integral_const,
    sphereMeasure_real_univ, smul_eq_mul] at h
  linarith only [h]

theorem integral_curvatureTrace {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    (∫ u : UnitSphere, curvatureTrace K u ∂sphereMeasure) = 2 * parallelQuadratic K := by
  have h := (parallelCoefficients_eq_curvatureIntegrals hKL h0).2
  rw [integral_add (integrable_curvatureTrace hKL) (integrable_support_sphere hKL),
    ← parallelQuadratic_eq_integral_support hKL h0] at h
  linarith only [h]

theorem integral_support_curvatureTrace {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    (∫ u : UnitSphere, support K u * curvatureTrace K u ∂sphereMeasure) = 2 * parallelLinear K := by
  obtain ⟨r, hr, hr1, hsub⟩ := exists_inner_scaledBall h0
  have h := area_variation (scaledBall_complement hr.le hr1) hKL hsub
    (scaledBall_zero_mem_interior hr)
  rw [(scaledBall_parallelCoefficients hr hr1).1] at h
  have he : variationAreaIntegrand (r • unitBallBody) K = fun u : UnitSphere =>
      support K u * curvatureTrace K u + (2 * r) * support K u -
        r * curvatureTrace K u - 2 * r ^ 2 := by
    funext u
    rw [variationAreaIntegrand, supportGap, support_scaledBall hr.le u.norm_eq_one,
      curvatureTrace_scaledBall hr.le hr1]
    ring
  have hq := integrable_support_mul_curvatureTrace hKL
  have hh := (integrable_support_sphere hKL).const_mul (2 * r)
  have ht := (integrable_curvatureTrace hKL).const_mul r
  have hconst : Integrable (fun _ : UnitSphere => 2 * r ^ 2) sphereMeasure := integrable_const _
  have hsum : Integrable (fun u : UnitSphere => support K u * curvatureTrace K u +
      (2 * r) * support K u) sphereMeasure := hq.add hh
  have hsub' : Integrable (fun u : UnitSphere => support K u * curvatureTrace K u +
      (2 * r) * support K u - r * curvatureTrace K u) sphereMeasure := hsum.sub ht
  rw [he, integral_sub hsub' hconst, integral_sub hsum ht, integral_add hq hh,
    integral_const_mul, integral_const_mul, integral_const, sphereMeasure_real_univ, smul_eq_mul,
    ← parallelQuadratic_eq_integral_support hKL h0, integral_curvatureTrace hKL h0] at h
  nlinarith only [h]

/-- The actual linear parallel-volume coefficient equals total tangent curvature density. -/
theorem parallelLinear_eq_integral_curvatureDet {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    parallelLinear K = ∫ u : UnitSphere, curvatureDet K u ∂sphereMeasure := by
  have h := (parallelCoefficients_eq_curvatureIntegrals hKL h0).1
  rw [integral_add (integrable_curvatureDet hKL) (integrable_support_mul_curvatureTrace hKL),
    integral_support_curvatureTrace hKL h0] at h
  linarith only [h]

end BlaschkeLebesgue
