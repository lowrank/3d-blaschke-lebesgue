module

public import BlaschkeLebesgue.ShellVolume
public import BlaschkeLebesgue.MixedCurvature

/-!
# Exact integration along the shell interpolation

The tangent determinant is a quadratic in interpolation time. Integrating that
quadratic gives an explicit polynomial in the two rounding parameters.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem shellTangent_det_polynomial {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (ε δ t : ℝ) (u : UnitSphere) :
    (shellTangent D K ε δ t u + normalProjection u).det =
      (1 - t) ^ 2 * curvatureDet D u + 2 * (1 - t) * t * mixedCurvature D K u +
      t ^ 2 * curvatureDet K u +
      (ε + t * δ) * ((1 - t) * curvatureTrace D u + t * curvatureTrace K u) +
      (ε + t * δ) ^ 2 := by
  let A := (1 - t) • sphereCurvature D u + t • sphereCurvature K u
  have hn : A u = 0 := by
    simp only [A, add_apply, smul_apply, sphereCurvature_apply_normal, smul_zero, add_zero]
  have ht : ∀ v, ⟪(u : Space), A v⟫_ℝ = 0 := by
    intro v
    simp only [A, add_apply, smul_apply, inner_add_right, inner_smul_right,
      sphereCurvature_apply_tangent hD, sphereCurvature_apply_tangent hK, mul_zero, add_zero]
  have htrace : LinearMap.trace ℝ Space A.toLinearMap =
      (1 - t) * curvatureTrace D u + t * curvatureTrace K u := by
    change LinearMap.trace ℝ Space ((1 - t) • (sphereCurvature D u).toLinearMap +
      t • (sphereCurvature K u).toLinearMap) = _
    rw [map_add, map_smul, map_smul]
    rfl
  have he := det_tangent_smul_shift u A hn ht 1 (ε + t * δ)
  simp only [one_smul, one_pow, one_mul, htrace] at he
  change (A + (ε + t * δ) • tangentProjection u + normalProjection u).det = _
  rw [he, show (A + normalProjection u).det =
    (1 - t) ^ 2 * curvatureDet D u + 2 * (1 - t) * t * mixedCurvature D K u +
      t ^ 2 * curvatureDet K u from curvature_det_combination hD hK u (1 - t) t]

theorem integral_quadratic_zero_one (a b c : ℝ) :
    (∫ t in (0 : ℝ)..1, a + b * t + c * t ^ 2) = a + b / 2 + c / 3 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => a) volume 0 1 := intervalIntegrable_const
  have h1 : IntervalIntegrable (fun t : ℝ => b * t) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => c * t ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_id, intervalIntegral.integral_const]
  norm_num
  ring

@[expose] def integratedShellDensity (D K : ConvexBody Space) (ε δ : ℝ) (u : UnitSphere) : ℝ :=
  (support K u - support D u + δ) *
    ((curvatureDet D u + mixedCurvature D K u + curvatureDet K u) / 3 +
      ε * (curvatureTrace D u + curvatureTrace K u) / 2 +
      δ * (curvatureTrace D u + 2 * curvatureTrace K u) / 6 +
      ε ^ 2 + ε * δ + δ ^ 2 / 3)

theorem integral_shellDensity {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (ε δ : ℝ) (u : UnitSphere) :
    (∫ t in (0 : ℝ)..1, shellDensity D K ε δ t u) = integratedShellDensity D K ε δ u := by
  simp_rw [shellDensity, shellTangent_det_polynomial hD hK]
  rw [intervalIntegral.integral_const_mul]
  let a := curvatureDet D u + ε * curvatureTrace D u + ε ^ 2
  let b := -2 * curvatureDet D u + 2 * mixedCurvature D K u +
    ε * (curvatureTrace K u - curvatureTrace D u) + δ * curvatureTrace D u + 2 * ε * δ
  let c := curvatureDet D u - 2 * mixedCurvature D K u + curvatureDet K u +
    δ * (curvatureTrace K u - curvatureTrace D u) + δ ^ 2
  have he : (fun t : ℝ =>
      (1 - t) ^ 2 * curvatureDet D u + 2 * (1 - t) * t * mixedCurvature D K u +
      t ^ 2 * curvatureDet K u +
      (ε + t * δ) * ((1 - t) * curvatureTrace D u + t * curvatureTrace K u) +
      (ε + t * δ) ^ 2) = (fun t => a + b * t + c * t ^ 2) := by
    funext t
    dsimp only [a, b, c]
    ring
  rw [he, integral_quadratic_zero_one]
  unfold integratedShellDensity
  dsimp only [a, b, c]
  ring

theorem shellVolume_polynomial_integral {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (integratedShellDensity D K ε δ) sphereMeasure ∧
      bodyVolume (parallelBody K (ε + δ)) - bodyVolume (parallelBody D ε) =
        ∫ u : UnitSphere, integratedShellDensity D K ε δ u ∂sphereMeasure := by
  have h := shellVolume_integral hD hK hDK hε hδ
  simpa only [integral_shellDensity hD hK] using h

end BlaschkeLebesgue
