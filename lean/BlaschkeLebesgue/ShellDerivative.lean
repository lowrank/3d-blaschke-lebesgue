module

public import BlaschkeLebesgue.ShellLipschitz
public import BlaschkeLebesgue.ParallelCurvature

/-!
# The derivative of the shell parametrization

The derivative separates into a tangent operator and a rank-one normal term.
This calculation uses only the almost-everywhere derivatives of the actual
support maps, with no smoothness hypothesis on the convex bodies.
-/

public noncomputable section

open MeasureTheory Set NormedSpace Filter
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem hasFDerivAt_normalize {x : Space} (hx : x ≠ 0) :
    HasFDerivAt (normalize : Space → Space)
      (‖x‖⁻¹ • tangentProjection (normalize x)) x := by
  have hd : HasFDerivAt (normalize : Space → Space) (tangentProjection (normalize x))
      (‖x‖⁻¹ • x) := hasFDerivAt_normalize_unit (norm_normalize hx)
  have h := hd.comp x ((hasFDerivAt_id x).const_smul ‖x‖⁻¹)
  simpa only [Function.comp_def, normalize_smul_of_pos (inv_pos.2 (norm_pos_iff.2 hx)),
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using h

theorem shellMap_eq (D K : ConvexBody Space) (ε δ : ℝ) (x : Space) :
    shellMap D K ε δ x =
      (1 - (‖x‖ - 1)) • normalSupport D x + (‖x‖ - 1) • normalSupport K x +
        (ε + (‖x‖ - 1) * δ) • normalize x := by
  simp only [shellMap, shellPoint, normalSupport_normalize]

theorem shellMap_ae_differentiable {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (ε δ : ℝ) :
    ∀ᵐ x ∂(volume : Measure Space), DifferentiableAt ℝ (shellMap D K ε δ) x := by
  have hne : ∀ᵐ x ∂(volume : Measure Space), x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [normalSupport_ae_differentiable hD,
    normalSupport_ae_differentiable hK, hne] with x hd hk hx
  have hn := (hasFDerivAt_space_norm hx).differentiableAt
  have ht := hn.sub_const 1
  have he : shellMap D K ε δ = fun y =>
      (1 - (‖y‖ - 1)) • normalSupport D y + (‖y‖ - 1) • normalSupport K y +
        (ε + (‖y‖ - 1) * δ) • normalize y := funext (shellMap_eq D K ε δ)
  rw [he]
  exact (((ht.const_sub 1).smul hd).add (ht.smul hk)).add
    (((ht.mul_const δ).const_add ε).smul (hasFDerivAt_normalize hx).differentiableAt)

@[expose] def shellTangent (D K : ConvexBody Space) (ε δ t : ℝ) (u : UnitSphere) :
    Space →L[ℝ] Space :=
  (1 - t) • sphereCurvature D u + t • sphereCurvature K u +
    (ε + t * δ) • tangentProjection u

@[expose] def shellIncrement (D K : ConvexBody Space) (δ : ℝ) (u : UnitSphere) : Space :=
  normalSupport K u - normalSupport D u + δ • (u : Space)

theorem shellTangent_apply_normal (D K : ConvexBody Space) (ε δ t : ℝ) (u : UnitSphere) :
    shellTangent D K ε δ t u u = 0 := by
  simp only [shellTangent, add_apply, smul_apply, sphereCurvature_apply_normal,
    tangentProjection_apply, real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow,
    one_smul, sub_self, smul_zero, add_zero]

theorem shellTangent_apply_tangent {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (ε δ t : ℝ) (u : UnitSphere) (v : Space) :
    ⟪(u : Space), shellTangent D K ε δ t u v⟫_ℝ = 0 := by
  simp only [shellTangent, add_apply, smul_apply, inner_add_right, inner_smul_right,
    sphereCurvature_apply_tangent hD, sphereCurvature_apply_tangent hK,
    inner_tangentProjection, mul_zero, add_zero]

theorem inner_shellIncrement (D K : ConvexBody Space) (δ : ℝ) (u : UnitSphere) :
    ⟪(u : Space), shellIncrement D K δ u⟫_ℝ = support K u - support D u + δ := by
  simp only [shellIncrement, inner_add_right, inner_sub_right, inner_smul_right,
    inner_normalSupport, real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow, mul_one]

theorem hasFDerivAt_shellMap_polar {D K : ConvexBody Space} (ε δ : ℝ) (u : UnitSphere)
    (hd : DifferentiableAt ℝ (normalSupport D) (u : Space))
    (hk : DifferentiableAt ℝ (normalSupport K) (u : Space)) {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (shellMap D K ε δ)
      (r⁻¹ • shellTangent D K ε δ (r - 1) u +
        (innerSL ℝ (u : Space)).smulRight (shellIncrement D K δ u)) (r • (u : Space)) := by
  have hnrm : ‖r • (u : Space)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, u.norm_eq_one, mul_one]
  have hdir : normalize (r • (u : Space)) = (u : Space) := by
    rw [normalize_smul_of_pos hr, normalize_eq_self_of_norm_eq_one u.norm_eq_one]
  have hx : r • (u : Space) ≠ 0 := smul_ne_zero hr.ne' u.ne_zero
  have hn : HasFDerivAt (fun x : Space => ‖x‖) (innerSL ℝ (u : Space)) (r • (u : Space)) := by
    simpa only [hdir] using hasFDerivAt_space_norm hx
  have hnormalize : HasFDerivAt (normalize : Space → Space)
      (r⁻¹ • tangentProjection u) (r • (u : Space)) := by
    simpa only [hnrm, hdir] using hasFDerivAt_normalize hx
  have hD := normalSupport_hasFDerivAt_smul hd.hasFDerivAt hr
  have hK := normalSupport_hasFDerivAt_smul hk.hasFDerivAt hr
  have ht := hn.sub_const 1
  have h := (((ht.const_sub 1).smul hD).add (ht.smul hK)).add
    (((ht.mul_const δ).const_add ε).smul hnormalize)
  have he : shellMap D K ε δ = fun x =>
      (1 - (‖x‖ - 1)) • normalSupport D x + (‖x‖ - 1) • normalSupport K x +
        (ε + (‖x‖ - 1) * δ) • normalize x := funext (shellMap_eq D K ε δ)
  rw [he]
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [shellTangent, shellIncrement, sphereCurvature, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, neg_apply,
    smul_eq_mul, hnrm, hdir, normalSupport_smul D hr,
    normalSupport_smul K hr]
  module

end BlaschkeLebesgue
