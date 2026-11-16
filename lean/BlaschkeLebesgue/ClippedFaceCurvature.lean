module

public import BlaschkeLebesgue.ActiveBallCurvature
public import BlaschkeLebesgue.ShellLipschitz
public import BlaschkeLebesgue.ClippedFaceBoundaries

/-! # The actual curvature on the interiors of the spherical faces -/

public noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem det_smul_tangentProjection_add_normalProjection (u : UnitSphere) (r : ℝ) :
    (r • tangentProjection u + normalProjection u).det = r ^ 2 := by
  have h := det_tangent_smul_shift u 0 (by simp) (by simp) 0 r
  have he : (0 : ℝ) • (0 : Space →L[ℝ] Space) + r • tangentProjection u + normalProjection u =
      r • tangentProjection u + normalProjection u := by module
  rw [he] at h
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] using h

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)
  {hne : (clippedOuter c.radius (range c.point)).Nonempty}

theorem normalSupport_clipped_eventually_unitFace (i : Fin 4) (u : UnitSphere)
    (hR : ‖c.point i + (u : Space)‖ < c.radius)
    (hj : ∀ j, j ≠ i → ‖c.point i + (u : Space) - c.point j‖ < 1) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) =ᶠ[𝓝 (u : Space)]
      fun x ↦ c.point i + NormedSpace.normalize x := by
  have hc := (hasFDerivAt_normalize_unit u.norm_eq_one).continuousAt.const_add (c.point i)
  have hRc : ∀ᶠ x in 𝓝 (u : Space), ‖c.point i + NormedSpace.normalize x‖ < c.radius :=
    Filter.Tendsto.eventually_lt_const
      (by simpa only [NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one] using hR) hc.norm
  have hjc : ∀ᶠ x in 𝓝 (u : Space),
      ∀ j, j ≠ i → ‖c.point i + NormedSpace.normalize x - c.point j‖ < 1 := by
    apply Filter.eventually_all.2
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h ↦ False.elim (h hji))
    · have h := Filter.Tendsto.eventually_lt_const
        (show ‖c.point i + NormedSpace.normalize (u : Space) - c.point j‖ < 1 by
          simpa only [NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one] using hj j hji)
        (hc.sub continuousAt_const).norm
      exact h.mono (fun _ hx _ ↦ hx)
  filter_upwards [isOpen_ne.mem_nhds u.ne_zero, hRc, hjc] with x hx hRx hjx
  let v : UnitSphere := ⟨NormedSpace.normalize x, by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩
  have hv : v ∈ c.unitFaceNormals i := by
    apply (c.mem_clippedOuter_range_iff _).2
    refine ⟨hRx.le, ?_⟩
    intro j
    by_cases hji : j = i
    · subst j
      simp only [add_sub_cancel_left, v.norm_eq_one, le_refl]
    · exact (hjx j hji).le
  have he := c.normalSupport_unitFaceNormals (hne := hne) i hv
  simpa only [v, normalSupport_normalize] using he

theorem hasFDerivAt_normalSupport_clipped_unitFace (i : Fin 4) (u : UnitSphere)
    (hR : ‖c.point i + (u : Space)‖ < c.radius)
    (hj : ∀ j, j ≠ i → ‖c.point i + (u : Space) - c.point j‖ < 1) :
    HasFDerivAt (normalSupport (clippedOuterBody c.radius (range c.point) hne))
      (tangentProjection u) (u : Space) :=
  ((hasFDerivAt_normalize_unit u.norm_eq_one).const_add (c.point i)).congr_of_eventuallyEq
    (c.normalSupport_clipped_eventually_unitFace i u hR hj)

theorem normalSupport_clipped_eventually_radiusFace (hR : 0 < c.radius) (u : UnitSphere)
    (hj : ∀ j, ‖c.radius • (u : Space) - c.point j‖ < 1) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) =ᶠ[𝓝 (u : Space)]
      fun x ↦ c.radius • NormedSpace.normalize x := by
  have hc := (hasFDerivAt_normalize_unit u.norm_eq_one).continuousAt.const_smul c.radius
  have hjc : ∀ᶠ x in 𝓝 (u : Space), ∀ j, ‖c.radius • NormedSpace.normalize x - c.point j‖ < 1 := by
    apply Filter.eventually_all.2
    intro j
    exact Filter.Tendsto.eventually_lt_const
      (by simpa only [Pi.sub_apply, Pi.smul_apply,
        NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one] using hj j)
      (hc.sub continuousAt_const).norm
  filter_upwards [isOpen_ne.mem_nhds u.ne_zero, hjc] with x hx hjx
  let v : UnitSphere := ⟨NormedSpace.normalize x, by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩
  have hv : v ∈ c.radiusFaceNormals := by
    apply (c.mem_clippedOuter_range_iff _).2
    refine ⟨?_, fun j ↦ (hjx j).le⟩
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, v.norm_eq_one, mul_one, le_refl]
  have he := c.normalSupport_radiusFaceNormals (hne := hne) hv
  simpa only [v, normalSupport_normalize] using he

theorem hasFDerivAt_normalSupport_clipped_radiusFace (hR : 0 < c.radius) (u : UnitSphere)
    (hj : ∀ j, ‖c.radius • (u : Space) - c.point j‖ < 1) :
    HasFDerivAt (normalSupport (clippedOuterBody c.radius (range c.point) hne))
      (c.radius • tangentProjection u) (u : Space) :=
  ((hasFDerivAt_normalize_unit u.norm_eq_one).const_smul c.radius).congr_of_eventuallyEq
    (c.normalSupport_clipped_eventually_radiusFace hR u hj)

theorem clipped_unitFace_curvature (i : Fin 4) (u : UnitSphere)
    (hR : ‖c.point i + (u : Space)‖ < c.radius)
    (hj : ∀ j, j ≠ i → ‖c.point i + (u : Space) - c.point j‖ < 1) :
    curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u = 2 ∧
      curvatureDet (clippedOuterBody c.radius (range c.point) hne) u = 1 := by
  have hd := (c.hasFDerivAt_normalSupport_clipped_unitFace (hne := hne) i u hR hj).fderiv
  constructor
  · simpa only [curvatureTrace, sphereCurvature, hd] using trace_tangentProjection u
  · change (sphereCurvature _ u + normalProjection u).det = _
    rw [sphereCurvature, hd]
    simpa only [one_smul, one_pow] using det_smul_tangentProjection_add_normalProjection u 1

theorem clipped_radiusFace_curvature (hR : 0 < c.radius) (u : UnitSphere)
    (hj : ∀ j, ‖c.radius • (u : Space) - c.point j‖ < 1) :
    curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u = 2 * c.radius ∧
      curvatureDet (clippedOuterBody c.radius (range c.point) hne) u = c.radius ^ 2 := by
  have hd := (c.hasFDerivAt_normalSupport_clipped_radiusFace (hne := hne) hR u hj).fderiv
  constructor
  · rw [curvatureTrace, sphereCurvature, hd]
    change LinearMap.trace ℝ Space (c.radius • (tangentProjection u).toLinearMap) = _
    rw [map_smul, trace_tangentProjection, smul_eq_mul, mul_comm]
  · change (sphereCurvature _ u + normalProjection u).det = _
    rw [sphereCurvature, hd]
    exact det_smul_tangentProjection_add_normalProjection u c.radius

theorem clipped_unitFace_curvature_ae (hA : c.totalDeficit ≤ 2 / 25) (hR : 0 < c.radius)
    (i : Fin 4) : ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.unitFaceNormals i →
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u = 2 ∧
        curvatureDet (clippedOuterBody c.radius (range c.point) hne) u = 1 := by
  filter_upwards [c.unitFaceNormals_ae_strict hA hR i] with u hu hmem
  exact c.clipped_unitFace_curvature i u (hu hmem).1 (hu hmem).2

theorem clipped_radiusFace_curvature_ae (hR : 0 < c.radius) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.radiusFaceNormals →
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u = 2 * c.radius ∧
        curvatureDet (clippedOuterBody c.radius (range c.point) hne) u = c.radius ^ 2 := by
  filter_upwards [c.radiusFaceNormals_ae_strict hR] with u hu hmem
  exact c.clipped_radiusFace_curvature hR u (hu hmem)

/-- The actual area density is supported on the five spherical face regions. -/
theorem curvatureDet_clipped_eq_faceIndicators_ae (hA : c.totalDeficit ≤ 2 / 25)
    (hR : 1 / 2 < c.radius) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure,
      curvatureDet (clippedOuterBody c.radius (range c.point) hne) u =
        c.radiusFaceNormals.indicator (fun _ ↦ c.radius ^ 2) u +
          ∑ i, (c.unitFaceNormals i).indicator (fun _ ↦ (1 : ℝ)) u := by
  classical
  have hR0 : 0 < c.radius := by linarith
  have hunit : ∀ᵐ u : UnitSphere ∂sphereMeasure, ∀ i, u ∈ c.unitFaceNormals i →
      curvatureDet (clippedOuterBody c.radius (range c.point) hne) u = 1 := by
    apply Filter.eventually_all.2
    intro i
    exact (c.clipped_unitFace_curvature_ae hA hR0 i).mono (fun _ h hm ↦ (h hm).2)
  filter_upwards [hunit, c.clipped_radiusFace_curvature_ae (hne := hne) hR0] with u hui huR
  by_cases hmemR : u ∈ c.radiusFaceNormals
  · rw [(huR hmemR).2, indicator_of_mem hmemR]
    have hs : ∑ i, (c.unitFaceNormals i).indicator (fun _ ↦ (1 : ℝ)) u = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun hi ↦
        Set.disjoint_left.1 (c.radiusFaceNormals_disjoint_unitFaceNormals hR (hne := hne) i) hmemR hi) _
    rw [hs, add_zero]
  · rw [indicator_of_notMem hmemR, zero_add]
    by_cases hex : ∃ i, u ∈ c.unitFaceNormals i
    · obtain ⟨i, hi⟩ := hex
      rw [hui i hi, Finset.sum_eq_single i, indicator_of_mem hi]
      · intro j _ hji
        exact indicator_of_notMem (fun hj ↦
          Set.disjoint_left.1 (c.unitFaceNormals_pairwise_disjoint hA (hne := hne) hji) hj hi) _
      · simp
    · have hall : ∀ i, u ∉ c.unitFaceNormals i := fun i hi ↦ hex ⟨i, hi⟩
      rw [c.curvatureDet_clipped_zero_off_faces hR0 u hmemR hall]
      symm
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (hall i) _

end BalancedContacts
end BlaschkeLebesgue
