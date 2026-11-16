module

public import BlaschkeLebesgue.ClippingCircleSupport

/-! # Curvature of the actual support map on an enclosing-sphere edge -/

public noncomputable section

open Set Metric Filter Topology
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem axisProjection_smul (k : Space) (r : ℝ) (x : Space) :
    axisProjection k (r • x) = r • axisProjection k x := by
  simp only [axisProjection, real_inner_smul_right]
  module

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)

@[expose] def clippingCirclePlaneProjection (i : Fin 4) (u : Space) : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space - normalProjection (c.clippingCircleAxis i) -
    normalProjection (NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u))

@[expose] def clippingCircleCurvature (i : Fin 4) (u : Space) : Space →L[ℝ] Space :=
  (ClippingCircle.radius c.radius / ‖axisProjection (c.clippingCircleAxis i) u‖) •
    c.clippingCirclePlaneProjection i u

theorem clippingCirclePlaneProjection_eq_comp (hR : 0 < c.radius) (i : Fin 4) (u : Space) :
    c.clippingCirclePlaneProjection i u =
      (tangentProjection (NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u))).comp
        (tangentProjection (c.clippingCircleAxis i)) := by
  have hp : ⟪NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u),
      c.clippingCircleAxis i⟫_ℝ = 0 := by
    rw [real_inner_comm]
    simp only [NormedSpace.normalize, real_inner_smul_right,
      axisProjection_inner_axis (c.clippingCircleAxis_norm hR i), mul_zero]
  apply ContinuousLinearMap.ext
  intro x
  simp only [clippingCirclePlaneProjection, sub_apply, ContinuousLinearMap.id_apply,
    normalProjection_apply, ContinuousLinearMap.comp_apply, tangentProjection_apply,
    inner_sub_right, real_inner_smul_right, hp, mul_zero, sub_zero]

theorem hasFDerivAt_clippingCircleCandidate (hR : 0 < c.radius) (i : Fin 4) {u : Space}
    (hp : axisProjection (c.clippingCircleAxis i) u ≠ 0) :
    HasFDerivAt (c.clippingCircleCandidate i) (c.clippingCircleCurvature i u) u := by
  have hp' : tangentProjection (c.clippingCircleAxis i) u ≠ 0 := hp
  have hpmap : axisProjection (c.clippingCircleAxis i) = tangentProjection (c.clippingCircleAxis i) := rfl
  have h := (hasFDerivAt_normalize hp').comp u (tangentProjection (c.clippingCircleAxis i)).hasFDerivAt
  have h' := (hasFDerivAt_const
    (ClippingCircle.height c.radius • c.clippingCircleAxis i) u).add
    (h.const_smul (ClippingCircle.radius c.radius))
  have he : ((fun _ : Space ↦ ClippingCircle.height c.radius • c.clippingCircleAxis i) +
      ClippingCircle.radius c.radius •
        (NormedSpace.normalize ∘ tangentProjection (c.clippingCircleAxis i))) =
      c.clippingCircleCandidate i := by funext x; rfl
  rw [he] at h'
  simpa only [clippingCircleCurvature, c.clippingCirclePlaneProjection_eq_comp hR, hpmap,
    zero_add, ContinuousLinearMap.smul_comp, smul_smul, div_eq_mul_inv, Function.comp_def] using h'

theorem trace_clippingCircleCurvature (hR : 0 < c.radius) (i : Fin 4) {u : Space}
    (hp : axisProjection (c.clippingCircleAxis i) u ≠ 0) :
    LinearMap.trace ℝ Space (c.clippingCircleCurvature i u).toLinearMap =
      ClippingCircle.radius c.radius / ‖axisProjection (c.clippingCircleAxis i) u‖ := by
  have hk := c.clippingCircleAxis_norm hR i
  have hv := NormedSpace.norm_normalize hp
  change LinearMap.trace ℝ Space
    ((ClippingCircle.radius c.radius / ‖axisProjection (c.clippingCircleAxis i) u‖) •
      (LinearMap.id - (innerSL ℝ (c.clippingCircleAxis i)).toLinearMap.smulRight (c.clippingCircleAxis i) -
        (innerSL ℝ (NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u))).toLinearMap.smulRight
          (NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u)))) = _
  rw [map_smul, map_sub, map_sub, LinearMap.trace_id,
    LinearMap.trace_smulRight, LinearMap.trace_smulRight]
  change (ClippingCircle.radius c.radius / ‖axisProjection (c.clippingCircleAxis i) u‖) *
    ((Module.finrank ℝ Space : ℝ) - ⟪c.clippingCircleAxis i, c.clippingCircleAxis i⟫_ℝ -
      ⟪NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u),
        NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u)⟫_ℝ) = _
  norm_num [Space, hk, hv]

theorem clippingCircleCandidate_smul (i : Fin 4) {r : ℝ} (hr : 0 < r) (x : Space) :
    c.clippingCircleCandidate i (r • x) = c.clippingCircleCandidate i x := by
  simp only [clippingCircleCandidate, axisProjection_smul, NormedSpace.normalize_smul_of_pos hr]

theorem clippingCircleCandidate_normalize (i : Fin 4) {x : Space} (hx : x ≠ 0) :
    c.clippingCircleCandidate i (NormedSpace.normalize x) = c.clippingCircleCandidate i x :=
  c.clippingCircleCandidate_smul i (inv_pos.2 (norm_pos_iff.2 hx)) x

theorem normalSupport_clipped_eventually_clippingCircle
    {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    (hR : 1 / 2 < c.radius) (i : Fin 4) (u : UnitSphere)
    (hlo : -(1 / (2 * c.radius)) < ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)
    (hhi : ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ < 1 - 1 / (2 * c.radius ^ 2))
    (hother : ∀ j, j ≠ i → ‖c.clippingCircleCandidate i u - c.point j‖ < 1) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) =ᶠ[𝓝 (u : Space)]
      c.clippingCircleCandidate i := by
  have hR0 : 0 < c.radius := by linarith
  have hp := c.clippingCircleProjection_ne_zero hR u i hlo.le hhi.le
  have hc := (c.hasFDerivAt_clippingCircleCandidate hR0 i hp).continuousAt
  have hn := (hasFDerivAt_normalize u.ne_zero).continuousAt
  have hl : ∀ᶠ x in 𝓝 (u : Space), -(1 / (2 * c.radius)) <
      ⟪c.clippingCircleAxis i, NormedSpace.normalize x⟫_ℝ := by
    apply Filter.Tendsto.eventually_const_lt
      (show -(1 / (2 * c.radius)) < ⟪c.clippingCircleAxis i, NormedSpace.normalize (u : Space)⟫_ℝ by
        simpa only [NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one] using hlo)
    exact continuousAt_const.inner hn
  have hh : ∀ᶠ x in 𝓝 (u : Space), ⟪c.clippingCircleAxis i, NormedSpace.normalize x⟫_ℝ <
      1 - 1 / (2 * c.radius ^ 2) := by
    apply Filter.Tendsto.eventually_lt_const
      (show ⟪c.clippingCircleAxis i, NormedSpace.normalize (u : Space)⟫_ℝ <
          1 - 1 / (2 * c.radius ^ 2) by
        simpa only [NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one] using hhi)
    exact continuousAt_const.inner hn
  have ho : ∀ᶠ x in 𝓝 (u : Space), ∀ j, j ≠ i →
      ‖c.clippingCircleCandidate i x - c.point j‖ < 1 := by
    apply eventually_all.2
    intro j
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ h ↦ (h hji).elim
    · exact (Filter.Tendsto.eventually_lt_const (hother j hji)
        (hc.sub continuousAt_const).norm).mono fun _ h _ ↦ h
  filter_upwards [isOpen_ne.mem_nhds u.ne_zero, hl, hh, ho] with x hx hxl hxh hxo
  let v : UnitSphere := ⟨NormedSpace.normalize x, by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩
  have hpv := c.clippingCircleProjection_ne_zero hR v i hxl.le hxh.le
  have hf := c.clippingCircleDirection_frame hR0 i hpv
  have hs := c.clippingCirclePoint_mem_spheres hR hf.1 hf.2
  have hm : c.clippingCircleCandidate i v ∈ clippedOuter c.radius (range c.point) := by
    rw [c.mem_clippedOuter_range_iff]
    refine ⟨?_, ?_⟩
    · exact le_of_eq (by simpa only [mem_sphere, dist_zero_right, clippingCircleCandidate] using hs.1)
    · intro j
      by_cases hji : j = i
      · subst j
        exact le_of_eq (by simpa only [mem_sphere, dist_eq_norm, clippingCircleCandidate] using hs.2)
      · simpa only [v, c.clippingCircleCandidate_normalize i hx] using (hxo j hji).le
  have he := c.normalSupport_clipped_clippingCircleCandidate (hne := hne) hR i v hxl.le hxh.le hm
  simpa only [v, normalSupport_normalize, c.clippingCircleCandidate_normalize i hx] using he

theorem hasFDerivAt_normalSupport_clipped_clippingCircle
    {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    (hR : 1 / 2 < c.radius) (i : Fin 4) (u : UnitSphere)
    (hlo : -(1 / (2 * c.radius)) < ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)
    (hhi : ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ < 1 - 1 / (2 * c.radius ^ 2))
    (hother : ∀ j, j ≠ i → ‖c.clippingCircleCandidate i u - c.point j‖ < 1) :
    HasFDerivAt (normalSupport (clippedOuterBody c.radius (range c.point) hne))
      (c.clippingCircleCurvature i u) (u : Space) :=
  (c.hasFDerivAt_clippingCircleCandidate (by linarith : 0 < c.radius) i
    (c.clippingCircleProjection_ne_zero hR u i hlo.le hhi.le)).congr_of_eventuallyEq
      (c.normalSupport_clipped_eventually_clippingCircle hR i u hlo hhi hother)

theorem clipped_clippingCircle_curvatureTrace
    {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    (hR : 1 / 2 < c.radius) (i : Fin 4) (u : UnitSphere)
    (hlo : -(1 / (2 * c.radius)) < ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)
    (hhi : ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ < 1 - 1 / (2 * c.radius ^ 2))
    (hother : ∀ j, j ≠ i → ‖c.clippingCircleCandidate i u - c.point j‖ < 1) :
    curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u =
      ClippingCircle.radius c.radius / Real.sqrt (1 - ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ^ 2) := by
  have he : sphereCurvature (clippedOuterBody c.radius (range c.point) hne) u =
      c.clippingCircleCurvature i u :=
    (c.hasFDerivAt_normalSupport_clipped_clippingCircle hR i u hlo hhi hother).fderiv
  have hn : ‖axisProjection (c.clippingCircleAxis i) (u : Space)‖ =
      Real.sqrt (1 - ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ^ 2) := by
    rw [← axisProjection_norm_sq (c.clippingCircleAxis_norm (by linarith : 0 < c.radius) i)
      u.norm_eq_one, Real.sqrt_sq (norm_nonneg _)]
  unfold curvatureTrace
  rw [he, c.trace_clippingCircleCurvature (by linarith : 0 < c.radius) i
    (c.clippingCircleProjection_ne_zero hR u i hlo.le hhi.le), hn]

end BalancedContacts
end BlaschkeLebesgue
