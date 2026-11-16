module

public import BlaschkeLebesgue.ClippedNormalRegions

/-! # Global decomposition of the actual clipped body's curvature trace -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

variable (c : BalancedContacts 4 Space)
  {hne : (clippedOuter c.radius (range c.point)).Nonempty}

theorem mem_facePatch_of_one_active (u : UnitSphere) (i : Option (Fin 4))
    (hother : ∀ j, j ≠ i →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) -
        c.clippedBallCenter j‖ < c.clippedBallRadius j) :
    u ∈ c.patchNormalRegion (.inl i) := by
  have hx := normalSupport_mem (clippedOuterBody c.radius (range c.point) hne) (u : Space)
  rw [c.normalSupport_clipped_eq_face_of_one_active u i hother] at hx
  cases i with
  | none =>
    change c.radius • (u : Space) ∈ clippedOuterBody c.radius (range c.point) hne
    simpa only [clippedBallCenter, clippedBallRadius, zero_add] using hx
  | some i =>
    change c.point i + (u : Space) ∈ clippedOuterBody c.radius (range c.point) hne
    simpa only [clippedBallCenter, clippedBallRadius, one_smul] using hx

theorem mem_radiusCircleNormals_of_two_active (hR : 1 / 2 < c.radius) (u : UnitSphere) (i : Fin 4)
    (hx : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ = c.radius)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hother : ∀ j, j ≠ i →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ < 1) :
    u ∈ c.radiusCircleNormals i := by
  have hc := c.active_radius_pair_normal_bounds hR u i hx hi hother
  have he := c.normalSupport_eq_clippingCircleCandidate_of_two_active hR u i hx hi hother
  refine ⟨hc, ?_⟩
  intro j
  rw [← he]
  exact ((c.mem_clippedOuter_range_iff _).1
    (normalSupport_mem (clippedOuterBody c.radius (range c.point) hne) (u : Space))).2 j

theorem exists_unitEdgeNormals_of_two_active_ordered (hA : c.totalDeficit ≤ 2 / 25)
    (u : UnitSphere) {i j : Fin 4} (hij : i < j)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hj : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ = 1)
    (hR : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ < c.radius)
    (hother : ∀ k, k ≠ i → k ≠ j →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point k‖ < 1) :
    ∃ k : Fin 6, u ∈ c.unitEdgeNormals k := by
  obtain ⟨k, he₀, he₁⟩ := exists_contactEdgePermutation i j hij
  let e := contactEdgePermutation k
  let d := c.relabel e
  have hAd : d.totalDeficit ≤ 2 / 25 := by simpa only [d, c.totalDeficit_relabel] using hA
  have ha := Opposite.edgeBudget_lt_one_of_small_deficit d hAd
  have hne' : (clippedOuter d.radius (range d.point)).Nonempty := by
    simpa only [d, c.clippedOuter_relabel e] using hne
  let C := clippedOuterBody d.radius (range d.point) hne'
  have hC : C = clippedOuterBody c.radius (range c.point) hne := c.clippedOuterBody_relabel e hne' hne
  have h₀ : ‖normalSupport C (u : Space) - d.point 0‖ = 1 := by
    rw [hC]
    simpa only [d, relabel, e, he₀] using hi
  have h₁ : ‖normalSupport C (u : Space) - d.point 1‖ = 1 := by
    rw [hC]
    simpa only [d, relabel, e, he₁] using hj
  have hR' : ‖normalSupport C (u : Space)‖ < d.radius := by rw [hC]; exact hR
  have ho : ∀ l, l ≠ 0 → l ≠ 1 → ‖normalSupport C (u : Space) - d.point l‖ < 1 := by
    intro l hl₀ hl₁
    rw [hC]
    apply hother (e l)
    · intro h
      apply hl₀
      apply e.injective
      exact h.trans he₀.symm
    · intro h
      apply hl₁
      apply e.injective
      exact h.trans he₁.symm
  have hb := Opposite.active_unit_pair_normal_bounds d ha u h₀ h₁ hR' ho
  have he := Opposite.normalSupport_eq_circleCandidate_of_two_active d ha u h₀ h₁ hR' ho
  refine ⟨k, hb, ?_⟩
  change ‖Opposite.circleCandidate d u‖ ≤ d.radius
  rw [← he]
  exact hR'.le

theorem exists_unitEdgeNormals_of_two_active (hA : c.totalDeficit ≤ 2 / 25)
    (u : UnitSphere) {i j : Fin 4} (hij : i ≠ j)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hj : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ = 1)
    (hR : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ < c.radius)
    (hother : ∀ k, k ≠ i → k ≠ j →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point k‖ < 1) :
    ∃ k : Fin 6, u ∈ c.unitEdgeNormals k := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact c.exists_unitEdgeNormals_of_two_active_ordered hA u hij hi hj hR hother
  · exact c.exists_unitEdgeNormals_of_two_active_ordered hA u hji hj hi hR
      (fun k hk₀ hk₁ ↦ hother k hk₁ hk₀)

theorem curvatureTrace_clipped_zero_off_patches (hA : c.totalDeficit ≤ 2 / 25) (u : UnitSphere)
    (hu : ∀ p : ClippedNormalPatch, u ∉ c.patchNormalRegion p) :
    curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u = 0 := by
  let C := clippedOuterBody c.radius (range c.point) hne
  let x := normalSupport C (u : Space)
  have hx := (c.mem_clippedOuter_range_iff x).1 (normalSupport_mem C (u : Space))
  by_cases hR : ‖x‖ = c.radius
  · by_cases hi : ∃ i, ‖x - c.point i‖ = 1
    · obtain ⟨i, hi⟩ := hi
      by_cases hj : ∃ j, j ≠ i ∧ ‖x - c.point j‖ = 1
      · obtain ⟨j, hji, hj⟩ := hj
        exact c.curvatureTrace_clipped_zero_two_unit_radius hA u hji.symm hR hi hj
      · have ho : ∀ j, j ≠ i → ‖x - c.point j‖ < 1 := by
          intro j hji
          exact lt_of_le_of_ne (hx.2 j) (fun h ↦ hj ⟨j, hji, h⟩)
        exact (hu (.inr (.inr i)) (c.mem_radiusCircleNormals_of_two_active
          (Opposite.radius_gt_half_of_small_deficit c hA) u i hR hi ho)).elim
    · have ho : ∀ j, ‖x - c.point j‖ < 1 := fun j ↦
        lt_of_le_of_ne (hx.2 j) (fun h ↦ hi ⟨j, h⟩)
      apply (hu (.inl none) (c.mem_facePatch_of_one_active (hne := hne) u none ?_)).elim
      intro j hj
      cases j with
      | none => exact (hj rfl).elim
      | some j => exact ho j
  · have hR' : ‖x‖ < c.radius := lt_of_le_of_ne hx.1 hR
    obtain ⟨i, hi⟩ := (c.normalSupport_clipped_has_active_ball (hne := hne) u).resolve_left hR
    by_cases hj : ∃ j, j ≠ i ∧ ‖x - c.point j‖ = 1
    · obtain ⟨j, hji, hj⟩ := hj
      by_cases hk : ∃ k, k ≠ i ∧ k ≠ j ∧ ‖x - c.point k‖ = 1
      · obtain ⟨k, hki, hkj, hk⟩ := hk
        exact c.curvatureTrace_clipped_zero_three_unit hA u hji.symm hki.symm hkj.symm hi hj hk
      · have ho : ∀ k, k ≠ i → k ≠ j → ‖x - c.point k‖ < 1 := by
          intro k hki hkj
          exact lt_of_le_of_ne (hx.2 k) (fun h ↦ hk ⟨k, hki, hkj, h⟩)
        obtain ⟨k, hk⟩ := c.exists_unitEdgeNormals_of_two_active hA u hji.symm hi hj hR' ho
        exact (hu (.inr (.inl k)) hk).elim
    · have ho : ∀ j, j ≠ i → ‖x - c.point j‖ < 1 := fun j hji ↦
        lt_of_le_of_ne (hx.2 j) (fun h ↦ hj ⟨j, hji, h⟩)
      apply (hu (.inl (some i)) (c.mem_facePatch_of_one_active (hne := hne) u (some i) ?_)).elim
      intro j hj
      cases j with
      | none => simpa only [clippedBallCenter, clippedBallRadius, sub_zero] using hR'
      | some j => exact ho j (fun h ↦ hj (congrArg some h))

theorem curvatureTrace_clipped_eq_patch_indicators (hA : c.totalDeficit ≤ 2 / 25) :
    (fun u ↦ curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u) =ᵐ[sphereMeasure]
      fun u ↦ ∑ p : ClippedNormalPatch, (c.patchNormalRegion p).indicator
        (curvatureTrace (clippedOuterBody c.radius (range c.point) hne)) u := by
  classical
  filter_upwards [c.patchNormalRegions_ae_pairwise_disjoint (hne := hne) hA] with u hu
  by_cases hm : ∃ p, u ∈ c.patchNormalRegion p
  · obtain ⟨p, hp⟩ := hm
    rw [Finset.sum_eq_single p, indicator_of_mem hp]
    · intro q _ hqp
      exact indicator_of_notMem (fun hq ↦ hu hqp ⟨hq, hp⟩) _
    · simp
  · have hnone : ∀ p, u ∉ c.patchNormalRegion p := fun p hp ↦ hm ⟨p, hp⟩
    rw [c.curvatureTrace_clipped_zero_off_patches hA u hnone]
    symm
    apply Finset.sum_eq_zero
    intro p _
    exact indicator_of_notMem (hnone p) _

theorem integral_curvatureTrace_clipped_eq_patch_sum (hA : c.totalDeficit ≤ 2 / 25) :
    (∫ u : UnitSphere, curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      ∑ p : ClippedNormalPatch, ∫ u in c.patchNormalRegion p,
        curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure := by
  have hR1 : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  have hi := integrable_curvatureTrace (clippedBodies_complement c.radius (range c.point) hne hR1)
  rw [integral_congr_ae (c.curvatureTrace_clipped_eq_patch_indicators hA),
    integral_finsetSum _ (fun p _ ↦ hi.indicator (c.measurableSet_patchNormalRegion hA p))]
  apply Finset.sum_congr rfl
  intro p _
  exact integral_indicator (c.measurableSet_patchNormalRegion hA p)

end BlaschkeLebesgue.BalancedContacts
