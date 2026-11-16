module

public import BlaschkeLebesgue.MixedCurvatureBound
public import BlaschkeLebesgue.CompletionAlgebra
public import BlaschkeLebesgue.VolumeVariation

/-!
# The completion weight for actual curvature operators

The mixed determinant lower bound reduces the orientation-independent matrix
inequality to the proved scalar contraction estimate. Multiplying by the
nonnegative support gap gives the integrand inequality used in completion.
-/

public noncomputable section

open MeasureTheory Set Filter

namespace BlaschkeLebesgue

theorem curvature_weight_lower_actual {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (u : UnitSphere) :
    Completion.psi (curvatureDet D u) - 1 / 16 ≤
      curvatureDet D u + mixedCurvature D K u + curvatureDet K u -
        (curvatureTrace D u + curvatureTrace K u) / 32 := by
  obtain ⟨hd0, hd1⟩ := curvatureDet_bounds hD u
  have h := Completion.curvature_weight_lower (a₁ := curvatureDet D u) (a₂ := 1)
    (u := 0) (v := curvatureTrace K u) (d := curvatureDet K u)
    hd0 hd1 le_rfl le_rfl (curvatureTrace_bounds hK u).1 (curvatureDet_bounds hK u).1
    (by simpa only [zero_add] using curvatureTrace_sub_one_le_det hK u)
  simp only [mul_one, mul_zero, add_zero] at h
  have hm := mixedCurvature_lower hD hK u
  have ht := curvatureTrace_sub_one_le_det hD u
  nlinarith only [h, hm, ht]

theorem completion_integrand_lower {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) (u : UnitSphere) :
    supportGap D K u * (Completion.psi (curvatureDet D u) - 1 / 16) ≤
      variationVolumeIntegrand D K u - variationAreaIntegrand D K u / 32 := by
  have h := mul_le_mul_of_nonneg_left (curvature_weight_lower_actual hD hK u)
    (sub_nonneg.2 (support_mono_of_subset hDK u))
  change supportGap D K u * (Completion.psi (curvatureDet D u) - 1 / 16) ≤ _ at h
  unfold variationVolumeIntegrand variationAreaIntegrand
  unfold supportGap at h ⊢
  convert h using 1
  ring

theorem continuous_completion_psi : Continuous Completion.psi := by
  unfold Completion.psi
  fun_prop

theorem completion_psi_bounds {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 ≤ Completion.psi s ∧ Completion.psi s ≤ 1 := by
  have hlo := Completion.psi_monotone h0
  have hhi := Completion.psi_monotone h1
  norm_num [Completion.psi] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem integrable_completion_weight {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) :
    Integrable (fun u : UnitSphere => supportGap D K u * Completion.psi (curvatureDet D u))
      sphereMeasure := by
  have hw : Integrable (fun u : UnitSphere => Completion.psi (curvatureDet D u)) sphereMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
      (continuous_completion_psi.measurable.comp (measurable_curvatureDet D)).aestronglyMeasurable
    apply Eventually.of_forall
    intro u
    obtain ⟨h0, h1⟩ := completion_psi_bounds (curvatureDet_bounds hD u).1 (curvatureDet_bounds hD u).2
    change ‖Completion.psi (curvatureDet D u)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  exact integrable_continuous_sphere_mul (continuous_supportGap hD hK) hw

/-- The integrated completion estimate, before pairing antipodal directions. -/
theorem completion_integral_lower {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) :
    (∫ u : UnitSphere, supportGap D K u * Completion.psi (curvatureDet D u) ∂sphereMeasure) -
      (∫ u : UnitSphere, supportGap D K u ∂sphereMeasure) / 16 ≤
      3 * (bodyVolume K - bodyVolume D) - (parallelLinear K - parallelLinear D) / 16 := by
  have hleft : Integrable (fun u : UnitSphere =>
      supportGap D K u * Completion.psi (curvatureDet D u) - supportGap D K u / 16) sphereMeasure :=
    (integrable_completion_weight hD hK).sub ((integrable_supportGap hD hK).div_const 16)
  have hright : Integrable (fun u : UnitSphere =>
      variationVolumeIntegrand D K u - variationAreaIntegrand D K u / 32) sphereMeasure :=
    (integrable_variationVolumeIntegrand hD hK).sub
    ((integrable_variationAreaIntegrand hD hK).div_const 32)
  have h := integral_mono hleft hright (fun u => by
    have hi := completion_integrand_lower hD hK hDK u
    nlinarith only [hi])
  rw [integral_sub (integrable_completion_weight hD hK) ((integrable_supportGap hD hK).div_const 16),
    integral_sub (integrable_variationVolumeIntegrand hD hK)
      ((integrable_variationAreaIntegrand hD hK).div_const 32),
    integral_div, integral_div, ← volume_variation hD hK hDK hD0,
    ← area_variation hD hK hDK hD0] at h
  linarith only [h]

end BlaschkeLebesgue
