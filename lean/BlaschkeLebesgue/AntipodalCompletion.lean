module

public import BlaschkeLebesgue.AntipodalIntegration
public import BlaschkeLebesgue.CurvatureWeight

/-!
# Pairing the completion weight at opposite normals

Constant width expresses the missing width as the sum of the two opposite
support gaps. The smaller of the two curvature determinants gives an even
weight, so antipodal invariance replaces the unknown distribution of those
gaps by the total missing width.
-/

public noncomputable section

open MeasureTheory Set Filter

namespace BlaschkeLebesgue

@[expose] def missingWidth (D : ConvexBody Space) (u : UnitSphere) : ℝ :=
  1 - support D u - support D (sphereAntipode u)

@[expose] def antipodalCurvatureMin (D : ConvexBody Space) (u : UnitSphere) : ℝ :=
  min (curvatureDet D u) (curvatureDet D (sphereAntipode u))

@[expose] def antipodalCompletionWeight (D : ConvexBody Space) (u : UnitSphere) : ℝ :=
  Completion.psi (antipodalCurvatureMin D u)

theorem missingWidth_eq_supportGap_pair {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (D : ConvexBody Space) (u : UnitSphere) :
    missingWidth D u = supportGap D K u + supportGap D K (sphereAntipode u) := by
  have h := hK (u : Space) u.norm_eq_one
  unfold missingWidth supportGap
  rw [sphereAntipode_val]
  linarith only [h]

theorem continuous_missingWidth {D D' : ConvexBody Space} (hD : D + D' = unitBallBody) :
    Continuous (missingWidth D) :=
  (continuous_const.sub (continuous_support_sphere hD)).sub
    ((continuous_support_sphere hD).comp sphereAntipode.continuous)

theorem missingWidth_nonneg {D K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) (u : UnitSphere) : 0 ≤ missingWidth D u := by
  rw [missingWidth_eq_supportGap_pair hK D]
  exact add_nonneg (sub_nonneg.2 (support_mono_of_subset hDK u))
    (sub_nonneg.2 (support_mono_of_subset hDK (sphereAntipode u)))

theorem antipodalCompletionWeight_even (D : ConvexBody Space) (u : UnitSphere) :
    antipodalCompletionWeight D (sphereAntipode u) = antipodalCompletionWeight D u := by
  simp only [antipodalCompletionWeight, antipodalCurvatureMin, sphereAntipode_involutive,
    min_comm (curvatureDet D (sphereAntipode u)) (curvatureDet D u)]

theorem antipodalCompletionWeight_le (D : ConvexBody Space) (u : UnitSphere) :
    antipodalCompletionWeight D u ≤ Completion.psi (curvatureDet D u) :=
  Completion.psi_monotone (min_le_left _ _)

theorem measurable_antipodalCompletionWeight (D : ConvexBody Space) :
    Measurable (antipodalCompletionWeight D) :=
  continuous_completion_psi.measurable.comp
    ((measurable_curvatureDet D).min ((measurable_curvatureDet D).comp sphereAntipode.measurable))

theorem antipodalCompletionWeight_bounds {D D' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (u : UnitSphere) :
    0 ≤ antipodalCompletionWeight D u ∧ antipodalCompletionWeight D u ≤ 1 :=
  completion_psi_bounds (le_min (curvatureDet_bounds hD u).1 (curvatureDet_bounds hD (sphereAntipode u)).1)
    ((min_le_left _ _).trans (curvatureDet_bounds hD u).2)

theorem integrable_antipodalCompletionWeight {D D' : ConvexBody Space}
    (hD : D + D' = unitBallBody) : Integrable (antipodalCompletionWeight D) sphereMeasure := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_antipodalCompletionWeight D).aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (antipodalCompletionWeight_bounds hD u).1]
    exact (antipodalCompletionWeight_bounds hD u).2

theorem integrable_gap_antipodalWeight {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) :
    Integrable (fun u => supportGap D K u * antipodalCompletionWeight D u) sphereMeasure :=
  integrable_continuous_sphere_mul (continuous_supportGap hD hK) (integrable_antipodalCompletionWeight hD)

theorem integrable_missingWidth_weight {D D' : ConvexBody Space} (hD : D + D' = unitBallBody) :
    Integrable (fun u => missingWidth D u * antipodalCompletionWeight D u) sphereMeasure :=
  integrable_continuous_sphere_mul (continuous_missingWidth hD) (integrable_antipodalCompletionWeight hD)

theorem integral_missingWidth {D D' K : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : HasConstantWidth K 1) :
    (∫ u : UnitSphere, missingWidth D u ∂sphereMeasure) =
      2 * (∫ u : UnitSphere, supportGap D K u ∂sphereMeasure) := by
  simp_rw [missingWidth_eq_supportGap_pair hK D]
  exact integral_antipodal_pair (supportGap D K) (integrable_supportGap hD hK.add_reflectBody)

theorem integral_missingWidth_weight {D D' K : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : HasConstantWidth K 1) :
    (∫ u : UnitSphere, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure) =
      2 * (∫ u : UnitSphere, supportGap D K u * antipodalCompletionWeight D u ∂sphereMeasure) := by
  have he : (fun u : UnitSphere => missingWidth D u * antipodalCompletionWeight D u) =
      (fun u => supportGap D K u * antipodalCompletionWeight D u +
        supportGap D K (sphereAntipode u) * antipodalCompletionWeight D (sphereAntipode u)) := by
    funext u
    rw [missingWidth_eq_supportGap_pair hK D, antipodalCompletionWeight_even, add_mul]
  rw [he]
  exact integral_antipodal_pair (fun u => supportGap D K u * antipodalCompletionWeight D u)
    (integrable_gap_antipodalWeight hD hK.add_reflectBody)

theorem completion_antipodal_integral_lower {D D' K : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : HasConstantWidth K 1)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) :
    (∫ u : UnitSphere, missingWidth D u * antipodalCompletionWeight D u ∂sphereMeasure) / 2 -
      (∫ u : UnitSphere, missingWidth D u ∂sphereMeasure) / 32 ≤
      3 * (bodyVolume K - bodyVolume D) - (parallelLinear K - parallelLinear D) / 16 := by
  have hweight := integral_mono (integrable_gap_antipodalWeight hD hK.add_reflectBody)
    (integrable_completion_weight hD hK.add_reflectBody) (fun u =>
      mul_le_mul_of_nonneg_left (antipodalCompletionWeight_le D u)
        (sub_nonneg.2 (support_mono_of_subset hDK u)))
  have h := completion_integral_lower hD hK.add_reflectBody hDK hD0
  rw [integral_missingWidth_weight hD hK, integral_missingWidth hD hK]
  linarith only [hweight, h]

end BlaschkeLebesgue
