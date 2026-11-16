module

public import BlaschkeLebesgue.ShellPolynomial

/-!
# The spherical shell integral is polynomial in the rounding parameters

All coefficients are integrable: the curvature densities are bounded and the
support gap is continuous on the compact sphere. This permits exact integration
of the polynomial and passage to zero rounding by ordinary continuity.
-/

public noncomputable section

open MeasureTheory Set Filter

namespace BlaschkeLebesgue

theorem integrable_continuous_sphere_mul {f g : UnitSphere → ℝ}
    (hf : Continuous f) (hg : Integrable g sphereMeasure) :
    Integrable (fun u => f u * g u) sphereMeasure := by
  obtain ⟨R, _, hR⟩ := (isCompact_range hf).isBounded.exists_pos_norm_le
  exact hg.bdd_mul hf.aestronglyMeasurable
    (Eventually.of_forall fun u => hR (f u) (mem_range_self u))

@[expose] def supportGap (D K : ConvexBody Space) (u : UnitSphere) : ℝ :=
  support K u - support D u

theorem continuous_supportGap {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) :
    Continuous (supportGap D K) :=
  (continuous_support_sphere hK).sub (continuous_support_sphere hD)

theorem integrable_supportGap {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) :
    Integrable (supportGap D K) sphereMeasure :=
  (continuous_supportGap hD hK).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

@[expose] def shellBase (D K : ConvexBody Space) (ε : ℝ) (u : UnitSphere) : ℝ :=
  (curvatureDet D u + mixedCurvature D K u + curvatureDet K u) / 3 +
    ε * (curvatureTrace D u + curvatureTrace K u) / 2 + ε ^ 2

@[expose] def shellSlope (D K : ConvexBody Space) (ε : ℝ) (u : UnitSphere) : ℝ :=
  (curvatureTrace D u + 2 * curvatureTrace K u) / 6 + ε

theorem integrable_shellBase {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (ε : ℝ) :
    Integrable (shellBase D K ε) sphereMeasure :=
  (((((integrable_curvatureDet hD).add (integrable_mixedCurvature hD hK)).add
    (integrable_curvatureDet hK)).div_const 3).add
    (((integrable_curvatureTrace hD).add (integrable_curvatureTrace hK)).const_mul ε |>.div_const 2)).add
    (integrable_const (ε ^ 2))

theorem integrable_shellSlope {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (ε : ℝ) :
    Integrable (shellSlope D K ε) sphereMeasure :=
  (((integrable_curvatureTrace hD).add ((integrable_curvatureTrace hK).const_mul 2)).div_const 6).add
    (integrable_const ε)

theorem integratedShellDensity_delta_polynomial (D K : ConvexBody Space) (ε δ : ℝ)
    (u : UnitSphere) :
    integratedShellDensity D K ε δ u =
      supportGap D K u * shellBase D K ε u +
      δ * (shellBase D K ε u + supportGap D K u * shellSlope D K ε u) +
      δ ^ 2 * (shellSlope D K ε u + supportGap D K u / 3) + δ ^ 3 / 3 := by
  unfold integratedShellDensity supportGap shellBase shellSlope
  ring

theorem integral_integratedShellDensity_delta {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (ε δ : ℝ) :
    (∫ u : UnitSphere, integratedShellDensity D K ε δ u ∂sphereMeasure) =
      (∫ u : UnitSphere, supportGap D K u * shellBase D K ε u ∂sphereMeasure) +
      δ * (∫ u : UnitSphere, shellBase D K ε u + supportGap D K u * shellSlope D K ε u
        ∂sphereMeasure) +
      δ ^ 2 * (∫ u : UnitSphere, shellSlope D K ε u + supportGap D K u / 3 ∂sphereMeasure) +
      (4 * Real.pi) * (δ ^ 3 / 3) := by
  have hgap := continuous_supportGap hD hK
  have h0 := integrable_continuous_sphere_mul hgap (integrable_shellBase hD hK ε)
  have h1 := ((integrable_shellBase hD hK ε).add
    (integrable_continuous_sphere_mul hgap (integrable_shellSlope hD hK ε))).const_mul δ
  have h2 := ((integrable_shellSlope hD hK ε).add ((integrable_supportGap hD hK).div_const 3)).const_mul
    (δ ^ 2)
  have h3 : Integrable (fun _ : UnitSphere => δ ^ 3 / 3) sphereMeasure := integrable_const _
  simp only [Pi.add_apply] at h1 h2
  have h01 : Integrable (fun u : UnitSphere => supportGap D K u * shellBase D K ε u +
      δ * (shellBase D K ε u + supportGap D K u * shellSlope D K ε u)) sphereMeasure := h0.add h1
  have h012 : Integrable (fun u : UnitSphere => supportGap D K u * shellBase D K ε u +
      δ * (shellBase D K ε u + supportGap D K u * shellSlope D K ε u) +
      δ ^ 2 * (shellSlope D K ε u + supportGap D K u / 3)) sphereMeasure := h01.add h2
  simp_rw [integratedShellDensity_delta_polynomial]
  rw [integral_add h012 h3, integral_add h01 h2,
    integral_add h0 h1, integral_const_mul, integral_const_mul, integral_const,
    sphereMeasure_real_univ, smul_eq_mul]

theorem continuous_integratedShellDensity_integral_delta {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (ε : ℝ) :
    Continuous (fun δ => ∫ u : UnitSphere, integratedShellDensity D K ε δ u ∂sphereMeasure) := by
  simp_rw [integral_integratedShellDensity_delta hD hK ε]
  fun_prop

@[expose] def variationVolumeIntegrand (D K : ConvexBody Space) (u : UnitSphere) : ℝ :=
  supportGap D K u * (curvatureDet D u + mixedCurvature D K u + curvatureDet K u)

@[expose] def variationAreaIntegrand (D K : ConvexBody Space) (u : UnitSphere) : ℝ :=
  supportGap D K u * (curvatureTrace D u + curvatureTrace K u)

theorem integrable_variationVolumeIntegrand {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) :
    Integrable (variationVolumeIntegrand D K) sphereMeasure :=
  integrable_continuous_sphere_mul (continuous_supportGap hD hK)
    (((integrable_curvatureDet hD).add (integrable_mixedCurvature hD hK)).add (integrable_curvatureDet hK))

theorem integrable_variationAreaIntegrand {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) :
    Integrable (variationAreaIntegrand D K) sphereMeasure :=
  integrable_continuous_sphere_mul (continuous_supportGap hD hK)
    ((integrable_curvatureTrace hD).add (integrable_curvatureTrace hK))

theorem integral_integratedShellDensity_zero {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (ε : ℝ) :
    (∫ u : UnitSphere, integratedShellDensity D K ε 0 u ∂sphereMeasure) =
      (∫ u : UnitSphere, variationVolumeIntegrand D K u ∂sphereMeasure) / 3 +
      ε * (∫ u : UnitSphere, variationAreaIntegrand D K u ∂sphereMeasure) / 2 +
      ε ^ 2 * (∫ u : UnitSphere, supportGap D K u ∂sphereMeasure) := by
  have he : integratedShellDensity D K ε 0 = fun u =>
      variationVolumeIntegrand D K u / 3 + ε * variationAreaIntegrand D K u / 2 +
      ε ^ 2 * supportGap D K u := by
    funext u
    unfold integratedShellDensity variationVolumeIntegrand variationAreaIntegrand supportGap
    ring
  have h0 := (integrable_variationVolumeIntegrand hD hK).div_const 3
  have h1 := ((integrable_variationAreaIntegrand hD hK).const_mul ε).div_const 2
  have h2 := (integrable_supportGap hD hK).const_mul (ε ^ 2)
  have h01 : Integrable (fun u : UnitSphere => variationVolumeIntegrand D K u / 3 +
      ε * variationAreaIntegrand D K u / 2) sphereMeasure := h0.add h1
  rw [he, integral_add h01 h2, integral_add h0 h1,
    integral_div, integral_div, integral_const_mul, integral_const_mul]

theorem continuous_integratedShellDensity_integral_zero {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) :
    Continuous (fun ε => ∫ u : UnitSphere, integratedShellDensity D K ε 0 u ∂sphereMeasure) := by
  simp_rw [integral_integratedShellDensity_zero hD hK]
  fun_prop

end BlaschkeLebesgue
