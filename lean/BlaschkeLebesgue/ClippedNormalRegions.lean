module

public import BlaschkeLebesgue.UnitEdgeCurvatureIntegral
public import BlaschkeLebesgue.RadiusEdgeCurvatureIntegral
public import BlaschkeLebesgue.ThreeActiveCurvature
public import BlaschkeLebesgue.ClippedSurfaceIntegrals

/-! # The five face and ten edge normal regions of the clipped body -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue

abbrev ClippedNormalPatch := Option (Fin 4) ⊕ (Fin 6 ⊕ Fin 4)

namespace BalancedContacts

@[expose] def contactEdgePermutation : Fin 6 → Equiv.Perm (Fin 4)
  | 0 => Equiv.refl _
  | 1 => Equiv.swap 1 2
  | 2 => Equiv.swap 1 3
  | 3 => (Equiv.swap 1 2).trans (Equiv.swap 0 1)
  | 4 => (Equiv.swap 1 3).trans (Equiv.swap 0 1)
  | 5 => (Equiv.swap 0 2).trans (Equiv.swap 1 3)

theorem contactEdgePermutation_order (k : Fin 6) :
    contactEdgePermutation k 0 < contactEdgePermutation k 1 := by
  have h : ∀ k : Fin 6, contactEdgePermutation k 0 < contactEdgePermutation k 1 := by decide +kernel
  exact h k

theorem exists_contactEdgePermutation (i j : Fin 4) (hij : i < j) :
    ∃ k : Fin 6, contactEdgePermutation k 0 = i ∧ contactEdgePermutation k 1 = j := by
  have h : ∀ i j : Fin 4, i < j →
      ∃ k : Fin 6, contactEdgePermutation k 0 = i ∧ contactEdgePermutation k 1 = j := by decide +kernel
  exact h i j hij

@[expose] def patchActiveIndices : ClippedNormalPatch → Finset (Option (Fin 4))
  | .inl i => {i}
  | .inr (.inl k) => {some (contactEdgePermutation k 0), some (contactEdgePermutation k 1)}
  | .inr (.inr i) => {none, some i}

theorem patchActiveIndices_injective : Function.Injective patchActiveIndices := by decide +kernel

variable (c : BalancedContacts 4 Space)

@[expose] def activeBallSet (x : Space) : Set (Option (Fin 4)) :=
  {i | ‖x - c.clippedBallCenter i‖ = c.clippedBallRadius i}

@[expose] def unitEdgeNormals (k : Fin 6) : Set UnitSphere :=
  Opposite.unitCircleNormals (c.relabel (contactEdgePermutation k))

@[expose] def patchNormalRegion : ClippedNormalPatch → Set UnitSphere
  | .inl none => c.radiusFaceNormals
  | .inl (some i) => c.unitFaceNormals i
  | .inr (.inl k) => c.unitEdgeNormals k
  | .inr (.inr i) => c.radiusCircleNormals i

theorem activeBallSet_eq_singleton {x : Space} (i : Option (Fin 4))
    (hi : ‖x - c.clippedBallCenter i‖ = c.clippedBallRadius i)
    (hother : ∀ j, j ≠ i → ‖x - c.clippedBallCenter j‖ < c.clippedBallRadius j) :
    c.activeBallSet x = {i} := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [activeBallSet, mem_ofPred_eq, hi, mem_singleton_iff]
  · simp only [activeBallSet, mem_ofPred_eq, (hother j hji).ne, mem_singleton_iff, hji]

theorem activeBallSet_eq_pair {x : Space} (i j : Option (Fin 4))
    (hi : ‖x - c.clippedBallCenter i‖ = c.clippedBallRadius i)
    (hj : ‖x - c.clippedBallCenter j‖ = c.clippedBallRadius j)
    (hother : ∀ k, k ≠ i → k ≠ j → ‖x - c.clippedBallCenter k‖ < c.clippedBallRadius k) :
    c.activeBallSet x = {i, j} := by
  ext k
  by_cases hki : k = i
  · subst k
    simp only [activeBallSet, mem_ofPred_eq, hi, mem_insert_iff, true_or]
  by_cases hkj : k = j
  · subst k
    simp only [activeBallSet, mem_ofPred_eq, hj, mem_insert_iff, mem_singleton_iff, or_true]
  simp only [activeBallSet, mem_ofPred_eq, (hother k hki hkj).ne,
    mem_insert_iff, mem_singleton_iff, hki, hkj, or_self]

variable {hne : (clippedOuter c.radius (range c.point)).Nonempty}

theorem normalSupport_unitEdgeNormals (hA : c.totalDeficit ≤ 2 / 25) (k : Fin 6) {u : UnitSphere}
    (hu : u ∈ c.unitEdgeNormals k) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      Opposite.circleCandidate (c.relabel (contactEdgePermutation k)) u := by
  let e := contactEdgePermutation k
  have hne' : (clippedOuter (c.relabel e).radius (range (c.relabel e).point)).Nonempty := by
    simpa only [c.clippedOuter_relabel e] using hne
  have h := Opposite.normalSupport_unitCircleNormals (c.relabel e)
    (by simpa only [c.totalDeficit_relabel] using hA) (hne := hne') hu
  simpa only [c.clippedOuterBody_relabel e hne' hne, e] using h

theorem measurableSet_unitEdgeNormals (hA : c.totalDeficit ≤ 2 / 25) (k : Fin 6) :
    MeasurableSet (c.unitEdgeNormals k) :=
  Opposite.measurableSet_unitCircleNormals (c.relabel (contactEdgePermutation k))
    (by simpa only [c.totalDeficit_relabel] using hA)

theorem measurableSet_patchNormalRegion (hA : c.totalDeficit ≤ 2 / 25) (p : ClippedNormalPatch) :
    MeasurableSet (c.patchNormalRegion p) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  rcases p with (_ | i) | (k | i)
  · exact c.measurableSet_radiusFaceNormals (by linarith)
  · exact c.measurableSet_unitFaceNormals i
  · exact c.measurableSet_unitEdgeNormals hA k
  · exact c.measurableSet_radiusCircleNormals hR i

theorem unitFaceNormals_ae_activeBallSet (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.unitFaceNormals i →
      c.activeBallSet (normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)) =
        {some i} := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  filter_upwards [c.unitFaceNormals_ae_strict hA (by linarith : 0 < c.radius) i] with u hu huS
  rw [c.normalSupport_unitFaceNormals (hne := hne) i huS]
  apply c.activeBallSet_eq_singleton (some i)
  · change ‖c.point i + (u : Space) - c.point i‖ = 1
    rw [add_sub_cancel_left, u.norm_eq_one]
  · intro j hji
    cases j with
    | none => simpa only [clippedBallCenter, clippedBallRadius, sub_zero] using (hu huS).1
    | some j => exact (hu huS).2 j (fun h ↦ hji (congrArg some h))

theorem radiusFaceNormals_ae_activeBallSet (hA : c.totalDeficit ≤ 2 / 25) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.radiusFaceNormals →
      c.activeBallSet (normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)) =
        {none} := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  have hR0 : 0 < c.radius := by linarith
  filter_upwards [c.radiusFaceNormals_ae_strict hR0] with u hu huS
  rw [c.normalSupport_radiusFaceNormals (hne := hne) huS]
  apply c.activeBallSet_eq_singleton none
  · simp only [clippedBallCenter, clippedBallRadius, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR0, u.norm_eq_one, mul_one]
  · intro j hji
    cases j with
    | none => exact (hji rfl).elim
    | some j => exact hu huS j

theorem unitEdgeNormals_ae_activeBallSet (hA : c.totalDeficit ≤ 2 / 25) (k : Fin 6) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.unitEdgeNormals k →
      c.activeBallSet (normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)) =
        {some (contactEdgePermutation k 0), some (contactEdgePermutation k 1)} := by
  let e := contactEdgePermutation k
  let d := c.relabel e
  have hAd : d.totalDeficit ≤ 2 / 25 := by simpa only [d, c.totalDeficit_relabel] using hA
  have ha := Opposite.edgeBudget_lt_one_of_small_deficit d hAd
  filter_upwards [Opposite.unitCircleNormals_ae_strict d hAd] with u hu huS
  have hu' := hu huS
  have hf := Opposite.circleDirection_frame d ha u.norm_eq_one hu'.1.le
  have hs := Opposite.circlePoint_mem_unit_spheres d hf.1 hf.2.1
  rw [c.normalSupport_unitEdgeNormals hA k huS]
  apply c.activeBallSet_eq_pair (some (e 0)) (some (e 1))
  · simpa only [mem_sphere, dist_eq_norm, Opposite.circleCandidate,
      d, e, relabel, clippedBallCenter, clippedBallRadius] using hs.1
  · simpa only [mem_sphere, dist_eq_norm, Opposite.circleCandidate,
      d, e, relabel, clippedBallCenter, clippedBallRadius] using hs.2
  · intro j hj₀ hj₁
    cases j with
    | none => simpa only [clippedBallCenter, clippedBallRadius, sub_zero, d, e, relabel] using hu'.2
    | some j =>
      have h₀ : e.symm j ≠ 0 := by
        intro h
        exact hj₀ (congrArg some (by simpa only [e.apply_symm_apply] using congrArg e h))
      have h₁ : e.symm j ≠ 1 := by
        intro h
        exact hj₁ (congrArg some (by simpa only [e.apply_symm_apply] using congrArg e h))
      have h := Opposite.circlePoint_mem_other_openBall d hAd hf.1 hf.2.1 hu'.2
        (e.symm j) h₀ h₁
      change ‖Opposite.circlePoint d (Opposite.circleDirection d u) - c.point j‖ < 1
      simpa only [show d.point (e.symm j) = c.point j by
        simp only [d, relabel, e.apply_symm_apply]] using h

theorem radiusCircleNormals_ae_activeBallSet (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.radiusCircleNormals i →
      c.activeBallSet (normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)) =
        {none, some i} := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  filter_upwards [c.radiusCircleNormals_ae_strict hA i] with u hu huS
  have hp := c.clippingCircleProjection_ne_zero hR u i huS.1.1 huS.1.2
  have hf := c.clippingCircleDirection_frame (by linarith : 0 < c.radius) i hp
  have hs := c.clippingCirclePoint_mem_spheres hR hf.1 hf.2
  rw [c.normalSupport_radiusCircleNormals (hne := hne) hR i huS]
  apply c.activeBallSet_eq_pair none (some i)
  · simpa only [mem_sphere, dist_eq_norm, clippingCircleCandidate,
      clippedBallCenter, clippedBallRadius] using hs.1
  · simpa only [mem_sphere, dist_eq_norm, clippingCircleCandidate,
      clippedBallCenter, clippedBallRadius] using hs.2
  · intro j hj₀ hj₁
    cases j with
    | none => exact (hj₀ rfl).elim
    | some j => exact (hu huS).2.2 j (fun h ↦ hj₁ (congrArg some h))

theorem patchNormalRegion_ae_activeBallSet (hA : c.totalDeficit ≤ 2 / 25) (p : ClippedNormalPatch) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.patchNormalRegion p →
      c.activeBallSet (normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)) =
        (patchActiveIndices p : Set (Option (Fin 4))) := by
  rcases p with (_ | i) | (k | i)
  · simpa only [patchNormalRegion, patchActiveIndices, Finset.coe_singleton] using
      c.radiusFaceNormals_ae_activeBallSet (hne := hne) hA
  · simpa only [patchNormalRegion, patchActiveIndices, Finset.coe_singleton] using
      c.unitFaceNormals_ae_activeBallSet (hne := hne) hA i
  · simpa only [patchNormalRegion, patchActiveIndices, Finset.coe_insert, Finset.coe_singleton] using
      c.unitEdgeNormals_ae_activeBallSet (hne := hne) hA k
  · simpa only [patchNormalRegion, patchActiveIndices, Finset.coe_insert, Finset.coe_singleton] using
      c.radiusCircleNormals_ae_activeBallSet (hne := hne) hA i

theorem patchNormalRegions_ae_pairwise_disjoint
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} (hA : c.totalDeficit ≤ 2 / 25) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, Pairwise (fun p q : ClippedNormalPatch ↦
      ¬ (u ∈ c.patchNormalRegion p ∧ u ∈ c.patchNormalRegion q)) := by
  filter_upwards [Filter.eventually_all.2 (c.patchNormalRegion_ae_activeBallSet (hne := hne) hA)] with u hu
  intro p q hpq hpqu
  apply hpq
  apply patchActiveIndices_injective
  apply Finset.coe_injective
  exact (hu p hpqu.1).symm.trans (hu q hpqu.2)

end BalancedContacts
end BlaschkeLebesgue
