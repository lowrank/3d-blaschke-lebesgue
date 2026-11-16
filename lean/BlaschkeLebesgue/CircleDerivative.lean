module

public import BlaschkeLebesgue.CircleSupport
public import BlaschkeLebesgue.ShellDerivative

/-! # Differentiating the actual contact-circle candidate -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space)

@[expose] def circlePlaneProjection (n : Space) : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space - normalProjection (firstAxis c) -
    normalProjection (circleDirection c n)

@[expose] def circleCurvature (n : Space) : Space →L[ℝ] Space :=
  (circleRadius c / ‖circleProjection c n‖) • circlePlaneProjection c n

theorem circleDirection_inner_axis (ha : edgeBudget c < 1) (n : Space) :
    ⟪circleDirection c n, firstAxis c⟫_ℝ = 0 := by
  simp only [circleDirection, NormedSpace.normalize, real_inner_smul_left,
    real_inner_comm (firstAxis c) (circleProjection c n), circleProjection_inner_axis c ha,
    mul_zero]

theorem circlePlaneProjection_eq_comp (ha : edgeBudget c < 1) (n : Space) :
    circlePlaneProjection c n =
      (tangentProjection (circleDirection c n)).comp (tangentProjection (firstAxis c)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [circlePlaneProjection, sub_apply, ContinuousLinearMap.id_apply,
    normalProjection_apply, ContinuousLinearMap.comp_apply, tangentProjection_apply,
    inner_sub_right, real_inner_smul_right, circleDirection_inner_axis c ha, mul_zero,
    sub_zero]

theorem hasFDerivAt_circleCandidate (ha : edgeBudget c < 1) {n : Space}
    (hp : circleProjection c n ≠ 0) :
    HasFDerivAt (circleCandidate c) (circleCurvature c n) n := by
  have hprojection : circleProjection c = tangentProjection (firstAxis c) := rfl
  have hp' : tangentProjection (firstAxis c) n ≠ 0 := hp
  have h := (hasFDerivAt_normalize hp').comp n (tangentProjection (firstAxis c)).hasFDerivAt
  have h' := (hasFDerivAt_const (firstMidpoint c) n).add (h.const_smul (circleRadius c))
  have hfun : ((fun _ : Space => firstMidpoint c) + circleRadius c •
      (NormedSpace.normalize ∘ tangentProjection (firstAxis c))) = circleCandidate c := by
    funext x
    rfl
  rw [hfun] at h'
  simpa only [circleDirection, hprojection, circleCurvature,
    circlePlaneProjection_eq_comp c ha, zero_add,
    ContinuousLinearMap.smul_comp, smul_smul, div_eq_mul_inv, Function.comp_def] using h'

theorem trace_circleCurvature (ha : edgeBudget c < 1) {n : Space} (hn : ‖n‖ = 1)
    (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2) :
    LinearMap.trace ℝ Space (circleCurvature c n).toLinearMap =
      circleRadius c / ‖circleProjection c n‖ := by
  have hk := firstAxis_norm c ha
  have hv := (circleDirection_frame c ha hn hcone).1
  change LinearMap.trace ℝ Space ((circleRadius c / ‖circleProjection c n‖) •
    (LinearMap.id - (innerSL ℝ (firstAxis c)).toLinearMap.smulRight (firstAxis c) -
      (innerSL ℝ (circleDirection c n)).toLinearMap.smulRight (circleDirection c n))) = _
  rw [map_smul, map_sub, map_sub, LinearMap.trace_id,
    LinearMap.trace_smulRight, LinearMap.trace_smulRight]
  change (circleRadius c / ‖circleProjection c n‖) *
    ((Module.finrank ℝ Space : ℝ) - ⟪firstAxis c, firstAxis c⟫_ℝ -
      ⟪circleDirection c n, circleDirection c n⟫_ℝ) = _
  norm_num [Space, hk, hv]

theorem circlePlaneProjection_apply_axis (ha : edgeBudget c < 1) (n : Space) :
    circlePlaneProjection c n (firstAxis c) = 0 := by
  simp only [circlePlaneProjection, sub_apply, ContinuousLinearMap.id_apply,
    normalProjection_apply, real_inner_self_eq_norm_sq, firstAxis_norm c ha,
    circleDirection_inner_axis c ha, one_pow, one_smul, zero_smul, sub_self]

theorem circlePlaneProjection_apply_direction (ha : edgeBudget c < 1)
    {n : Space} (hn : ‖n‖ = 1) (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2) :
    circlePlaneProjection c n (circleDirection c n) = 0 := by
  have hv := (circleDirection_frame c ha hn hcone).1
  have hkv : ⟪firstAxis c, circleDirection c n⟫_ℝ = 0 := by
    rw [real_inner_comm (circleDirection c n), circleDirection_inner_axis c ha]
  simp only [circlePlaneProjection, sub_apply, ContinuousLinearMap.id_apply,
    normalProjection_apply, real_inner_self_eq_norm_sq, hv, hkv, one_pow,
    one_smul, zero_smul, sub_zero, sub_self]

theorem circlePlaneProjection_apply_normal (ha : edgeBudget c < 1)
    {n : Space} (hn : ‖n‖ = 1) (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2) :
    circlePlaneProjection c n n = 0 := by
  have hid : n = ⟪firstAxis c, n⟫_ℝ • firstAxis c +
      ‖circleProjection c n‖ • circleDirection c n := by
    rw [circleDirection, NormedSpace.norm_smul_normalize]
    dsimp only [circleProjection]
    module
  calc
    _ = circlePlaneProjection c n (⟪firstAxis c, n⟫_ℝ • firstAxis c +
        ‖circleProjection c n‖ • circleDirection c n) := congrArg (circlePlaneProjection c n) hid
    _ = 0 := by
      rw [map_add, map_smul, map_smul, circlePlaneProjection_apply_axis c ha,
        circlePlaneProjection_apply_direction c ha hn hcone, smul_zero, smul_zero, add_zero]

theorem circleCurvature_augmented_det (ha : edgeBudget c < 1)
    {n : Space} (hn : ‖n‖ = 1) (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2) :
    (circleCurvature c n + normalProjection n).det = 0 := by
  let t := firstAxis c - ⟪firstAxis c, n⟫_ℝ • n
  have ht : t ≠ 0 := by
    have ht2 : ‖t‖ ^ 2 = ‖circleProjection c n‖ ^ 2 := by
      rw [circleProjection_norm_sq c ha hn]
      simp only [t, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        firstAxis_norm c ha, hn, real_inner_smul_right]
      ring
    have hp := circleProjection_norm_pos c ha hn hcone
    intro hh
    rw [hh, norm_zero] at ht2
    nlinarith
  have hzero : (circleCurvature c n + normalProjection n) t = 0 := by
    have hnt : ⟪n, t⟫_ℝ = 0 := by
      simp only [t, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        hn, real_inner_comm (firstAxis c) n]
      ring
    rw [add_apply, normalProjection_apply, hnt, zero_smul, add_zero]
    simp only [circleCurvature, smul_apply, t, map_sub, map_smul,
      circlePlaneProjection_apply_axis c ha, circlePlaneProjection_apply_normal c ha hn hcone,
      smul_zero, sub_self]
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.2
  intro hbot
  have hm : t ∈ LinearMap.ker (circleCurvature c n + normalProjection n).toLinearMap := hzero
  rw [hbot, Submodule.mem_bot] at hm
  exact ht hm

end BlaschkeLebesgue.BalancedContacts.Opposite
