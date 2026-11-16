module

public import BlaschkeLebesgue.ShellIntegralPolynomial

/-!
# Nonsmooth volume, area, and mean-coefficient variation

The two positive rounding parameters in the proved shell-volume formula can
be removed by continuity of explicit polynomials. Comparing their coefficients
gives the variation identities for actual nested summands of the unit ball.
-/

public noncomputable section

open MeasureTheory Set Filter Topology

namespace BlaschkeLebesgue

theorem parallelPolynomial_sub_eq_shellIntegral_zero {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) {ε : ℝ} (hε : 0 < ε) :
    parallelPolynomial K ε - parallelPolynomial D ε =
      ∫ u : UnitSphere, integratedShellDensity D K ε 0 u ∂sphereMeasure := by
  have hK0 := interior_mono hDK hD0
  have he : EqOn (fun δ : ℝ => parallelPolynomial K (ε + δ) - parallelPolynomial D ε)
      (fun δ => ∫ u : UnitSphere, integratedShellDensity D K ε δ u ∂sphereMeasure) (Ioi 0) := by
    intro δ hδ
    dsimp only
    rw [parallelPolynomial_eq_volume_pos hK hK0 (add_pos hε hδ),
      parallelPolynomial_eq_volume_pos hD hD0 hε]
    exact (shellVolume_polynomial_integral hD hK hDK hε hδ).2
  have hleft : Continuous (fun δ : ℝ => parallelPolynomial K (ε + δ) - parallelPolynomial D ε) :=
    ((continuous_parallelPolynomial K).comp (continuous_const.add continuous_id)).sub continuous_const
  have hz := he.closure hleft (continuous_integratedShellDensity_integral_delta hD hK ε)
    (show (0 : ℝ) ∈ closure (Ioi 0) by simp [closure_Ioi])
  simpa only [add_zero] using hz

/-- The same polynomial identity holds at zero rounding, with integrable actual curvature densities. -/
theorem variation_polynomial {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) {ε : ℝ} (hε : 0 ≤ ε) :
    parallelPolynomial K ε - parallelPolynomial D ε =
      (∫ u : UnitSphere, variationVolumeIntegrand D K u ∂sphereMeasure) / 3 +
      ε * (∫ u : UnitSphere, variationAreaIntegrand D K u ∂sphereMeasure) / 2 +
      ε ^ 2 * (∫ u : UnitSphere, supportGap D K u ∂sphereMeasure) := by
  have he : EqOn (fun ε : ℝ => parallelPolynomial K ε - parallelPolynomial D ε)
      (fun ε => ∫ u : UnitSphere, integratedShellDensity D K ε 0 u ∂sphereMeasure) (Ioi 0) :=
    fun _ hε => parallelPolynomial_sub_eq_shellIntegral_zero hD hK hDK hD0 hε
  have h := he.closure ((continuous_parallelPolynomial K).sub (continuous_parallelPolynomial D))
    (continuous_integratedShellDensity_integral_zero hD hK)
    (show ε ∈ closure (Ioi 0) by simpa only [closure_Ioi, mem_Ici] using hε)
  dsimp only at h
  rw [integral_integratedShellDensity_zero hD hK] at h
  exact h

/-- All three quantities on the left are the already established actual volume coefficients. -/
theorem nested_volume_area_mean_variations {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) :
    3 * (bodyVolume K - bodyVolume D) =
        (∫ u : UnitSphere, variationVolumeIntegrand D K u ∂sphereMeasure) ∧
      2 * (parallelLinear K - parallelLinear D) =
        (∫ u : UnitSphere, variationAreaIntegrand D K u ∂sphereMeasure) ∧
      parallelQuadratic K - parallelQuadratic D =
        (∫ u : UnitSphere, supportGap D K u ∂sphereMeasure) := by
  have hK0 := interior_mono hDK hD0
  have h0 := variation_polynomial hD hK hDK hD0 (ε := 0) le_rfl
  have h1 := variation_polynomial hD hK hDK hD0 (ε := 1) (by norm_num)
  have h2 := variation_polynomial hD hK hDK hD0 (ε := 2) (by norm_num)
  norm_num only [parallelPolynomial, parallelConstant_eq_volume hD hD0,
    parallelConstant_eq_volume hK hK0, zero_mul, one_mul, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), one_pow, add_zero] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [h0, h1, h2]

theorem volume_variation {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) :
    3 * (bodyVolume K - bodyVolume D) =
      ∫ u : UnitSphere, variationVolumeIntegrand D K u ∂sphereMeasure :=
  (nested_volume_area_mean_variations hD hK hDK hD0).1

theorem area_variation {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) :
    2 * (parallelLinear K - parallelLinear D) =
      ∫ u : UnitSphere, variationAreaIntegrand D K u ∂sphereMeasure :=
  (nested_volume_area_mean_variations hD hK hDK hD0).2.1

theorem mean_coefficient_variation {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) :
    parallelQuadratic K - parallelQuadratic D =
      ∫ u : UnitSphere, supportGap D K u ∂sphereMeasure :=
  (nested_volume_area_mean_variations hD hK hDK hD0).2.2

end BlaschkeLebesgue
