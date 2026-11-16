module

public import BlaschkeLebesgue.CapBoundaries
public import BlaschkeLebesgue.ClippedCapSeparation
public import BlaschkeLebesgue.CircleSupport
public import BlaschkeLebesgue.FourSetInclusion

/-!
# The actual spherical faces as cap regions

The parameters in these sets are the outward unit normals to the contact
spheres or the enclosing sphere. Membership is proved equivalent to membership
of the corresponding point in the actual clipped body.
-/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

variable (c : BalancedContacts 4 Space)

@[expose] def unitFaceCap (i : Fin 4) : Set UnitSphere := sphereCap (-c.point i) (1 / 2)

@[expose] def unitNeighborCap (i j : Fin 4) : Set UnitSphere :=
  sphereCap (c.point j - c.point i) (‖c.point j - c.point i‖ ^ 2 / 2)

@[expose] def unitRemovedCap (i j : Fin 4) : Set UnitSphere :=
  c.unitFaceCap i \ c.unitNeighborCap i j

@[expose] def radiusExcludedCap (i : Fin 4) : Set UnitSphere :=
  openSphereCap (-c.point i) ((1 - 2 * c.radius ^ 2) / (2 * c.radius))

@[expose] def unitFaceNormals (i : Fin 4) : Set UnitSphere :=
  {u | c.point i + (u : Space) ∈ clippedOuter c.radius (range c.point)}

@[expose] def radiusFaceNormals : Set UnitSphere :=
  {u | c.radius • (u : Space) ∈ clippedOuter c.radius (range c.point)}

theorem mem_clippedOuter_range_iff (x : Space) :
    x ∈ clippedOuter c.radius (range c.point) ↔
      ‖x‖ ≤ c.radius ∧ ∀ i, ‖x - c.point i‖ ≤ 1 := by
  simp only [clippedOuter, mem_inter_iff, mem_closedBall, dist_zero_right,
    ballTransform, mem_ofPred_eq, forall_mem_range]

theorem mem_unitFaceCap_iff (i : Fin 4) (u : UnitSphere) :
    u ∈ c.unitFaceCap i ↔ ‖c.point i + (u : Space)‖ ≤ c.radius := by
  have hR : 0 ≤ c.radius := by rw [← c.on_sphere i]; exact norm_nonneg _
  have hs := norm_add_sq_real (c.point i) (u : Space)
  rw [c.on_sphere i, u.norm_eq_one] at hs
  change (1 / 2 : ℝ) ≤ ⟪-c.point i, (u : Space)⟫_ℝ ↔ _
  rw [inner_neg_left]
  constructor <;> intro h <;> nlinarith [norm_nonneg (c.point i + (u : Space))]

theorem mem_unitNeighborCap_iff (i j : Fin 4) (u : UnitSphere) :
    u ∈ c.unitNeighborCap i j ↔ ‖c.point i + (u : Space) - c.point j‖ ≤ 1 := by
  have he : c.point i + (u : Space) - c.point j = (u : Space) - (c.point j - c.point i) := by abel
  have hs := norm_sub_sq_real (u : Space) (c.point j - c.point i)
  rw [u.norm_eq_one, real_inner_comm] at hs
  change ‖c.point j - c.point i‖ ^ 2 / 2 ≤ ⟪c.point j - c.point i, (u : Space)⟫_ℝ ↔ _
  rw [he]
  constructor <;> intro h <;> nlinarith [norm_nonneg ((u : Space) - (c.point j - c.point i))]

theorem mem_unitRemovedCap_iff (i j : Fin 4) (u : UnitSphere) :
    u ∈ c.unitRemovedCap i j ↔
      ‖c.point i + (u : Space)‖ ≤ c.radius ∧ 1 < ‖c.point i + (u : Space) - c.point j‖ := by
  simp only [unitRemovedCap, Set.mem_sdiff, c.mem_unitFaceCap_iff,
    c.mem_unitNeighborCap_iff, not_le]

theorem unitRemovedCap_self (i : Fin 4) : c.unitRemovedCap i i = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro u hu
  have h := ((c.mem_unitRemovedCap_iff i i u).1 hu).2
  simp only [add_sub_cancel_left, u.norm_eq_one, lt_self_iff_false] at h

theorem mem_radiusExcludedCap_iff (hR : 0 < c.radius) (i : Fin 4) (u : UnitSphere) :
    u ∈ c.radiusExcludedCap i ↔ 1 < ‖c.radius • (u : Space) - c.point i‖ := by
  have hs := norm_sub_sq_real (c.radius • (u : Space)) (c.point i)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, u.norm_eq_one, mul_one,
    c.on_sphere i, real_inner_smul_left, real_inner_comm (c.point i) (u : Space)] at hs
  change (1 - 2 * c.radius ^ 2) / (2 * c.radius) < ⟪-c.point i, (u : Space)⟫_ℝ ↔ _
  rw [inner_neg_left, div_lt_iff₀ (by positivity : 0 < 2 * c.radius)]
  constructor <;> intro h <;> nlinarith [norm_nonneg (c.radius • (u : Space) - c.point i)]

theorem unitFaceNormals_eq_caps (i : Fin 4) :
    c.unitFaceNormals i = c.unitFaceCap i ∩ ⋂ j, c.unitNeighborCap i j := by
  ext u
  simp only [unitFaceNormals, mem_ofPred_eq, c.mem_clippedOuter_range_iff,
    mem_inter_iff, mem_iInter, c.mem_unitFaceCap_iff, c.mem_unitNeighborCap_iff]

theorem unitFaceNormals_eq_sdiff (i : Fin 4) :
    c.unitFaceNormals i = c.unitFaceCap i \ ⋃ j, c.unitRemovedCap i j := by
  rw [c.unitFaceNormals_eq_caps]
  ext u
  simp only [unitRemovedCap, mem_inter_iff, mem_iInter, Set.mem_sdiff, mem_iUnion,
    not_exists, not_and, not_not]
  exact ⟨fun h ↦ ⟨h.1, fun j _ ↦ h.2 j⟩, fun h ↦ ⟨h.1, fun j ↦ h.2 j h.1⟩⟩

theorem radiusFaceNormals_eq_compl (hR : 0 < c.radius) :
    c.radiusFaceNormals = (⋃ i, c.radiusExcludedCap i)ᶜ := by
  ext u
  simp only [radiusFaceNormals, mem_ofPred_eq, c.mem_clippedOuter_range_iff,
    norm_smul, Real.norm_eq_abs, abs_of_pos hR, u.norm_eq_one, mul_one, le_refl, true_and,
    mem_compl_iff, mem_iUnion, c.mem_radiusExcludedCap_iff hR, not_exists, not_lt]

theorem measurableSet_unitFaceCap (i : Fin 4) : MeasurableSet (c.unitFaceCap i) :=
  measurableSet_sphereCap _ _

theorem measurableSet_unitNeighborCap (i j : Fin 4) : MeasurableSet (c.unitNeighborCap i j) :=
  measurableSet_sphereCap _ _

theorem measurableSet_unitRemovedCap (i j : Fin 4) : MeasurableSet (c.unitRemovedCap i j) :=
  (c.measurableSet_unitFaceCap i).diff (c.measurableSet_unitNeighborCap i j)

theorem measurableSet_radiusExcludedCap (i : Fin 4) : MeasurableSet (c.radiusExcludedCap i) :=
  measurableSet_openSphereCap _ _

theorem measurableSet_unitFaceNormals (i : Fin 4) : MeasurableSet (c.unitFaceNormals i) := by
  rw [c.unitFaceNormals_eq_caps]
  exact (c.measurableSet_unitFaceCap i).inter (MeasurableSet.iInter (c.measurableSet_unitNeighborCap i))

theorem measurableSet_radiusFaceNormals (hR : 0 < c.radius) :
    MeasurableSet c.radiusFaceNormals := by
  rw [c.radiusFaceNormals_eq_compl hR]
  exact (MeasurableSet.iUnion c.measurableSet_radiusExcludedCap).compl

private theorem missing_contact {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ l : Fin 4, i ≠ l ∧ ∀ r, r ≠ l → r = i ∨ r = j ∨ r = k := by
  have h : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      ∃ l : Fin 4, i ≠ l ∧ ∀ r, r ≠ l → r = i ∨ r = j ∨ r = k := by decide +kernel
  exact h i j k hij hik hjk

theorem radius_lt_norm_of_three_distances (hA : c.totalDeficit ≤ 2 / 25)
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {x : Space}
    (hi : 1 < ‖x - c.point i‖) (hj : 1 ≤ ‖x - c.point j‖)
    (hk : 1 ≤ ‖x - c.point k‖) : c.radius < ‖x‖ := by
  obtain ⟨l, hil, hcover⟩ := missing_contact hij hik hjk
  apply c.radius_lt_norm_of_strict_unit_constraints l _ hil
    (lt_of_lt_of_le (by norm_num) (c.weight_ge_eleven_fiftieths hA i)) hi
  intro r hr
  rcases hcover r hr with rfl | rfl | rfl
  · exact hi.le
  · exact hj
  · exact hk

/-- The three pieces removed from a contact face are disjoint as actual sets. -/
theorem unitRemovedCap_pairwise_disjoint (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    Pairwise (fun j k ↦ Disjoint (c.unitRemovedCap i j) (c.unitRemovedCap i k)) := by
  intro j k hjk
  by_cases hji : j = i
  · simp [hji, c.unitRemovedCap_self]
  by_cases hki : k = i
  · simp [hki, c.unitRemovedCap_self]
  apply Set.disjoint_left.2
  intro u hu hv
  obtain ⟨hR, hj⟩ := (c.mem_unitRemovedCap_iff i j u).1 hu
  have hk := ((c.mem_unitRemovedCap_iff i k u).1 hv).2
  have hi : ‖c.point i + (u : Space) - c.point i‖ = 1 := by
    simp only [add_sub_cancel_left, u.norm_eq_one]
  exact (not_lt_of_ge hR)
    (c.radius_lt_norm_of_three_distances hA hji hjk (Ne.symm hki) hj hi.ge hk.le)

/-- No three strict exclusions overlap on the enclosing sphere. -/
theorem radiusExcludedCap_triple_empty (hA : c.totalDeficit ≤ 2 / 25) (hR : 0 < c.radius)
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    c.radiusExcludedCap i ∩ c.radiusExcludedCap j ∩ c.radiusExcludedCap k = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  rintro u ⟨⟨hi, hj⟩, hk⟩
  have h := c.radius_lt_norm_of_three_distances hA hij hik hjk
    ((c.mem_radiusExcludedCap_iff hR i u).1 hi)
    ((c.mem_radiusExcludedCap_iff hR j u).1 hj).le
    ((c.mem_radiusExcludedCap_iff hR k u).1 hk).le
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, u.norm_eq_one, mul_one,
    lt_self_iff_false] at h

theorem sphereMeasure_real_unitFaceNormals (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    sphereMeasure.real (c.unitFaceNormals i) = sphereMeasure.real (c.unitFaceCap i) -
      ∑ j, sphereMeasure.real (c.unitRemovedCap i j) := by
  have hs : (⋃ j, c.unitRemovedCap i j) ⊆ c.unitFaceCap i := by
    intro u hu
    obtain ⟨j, hj⟩ := mem_iUnion.1 hu
    exact hj.1
  rw [c.unitFaceNormals_eq_sdiff, measureReal_sdiff hs
    (MeasurableSet.iUnion (c.measurableSet_unitRemovedCap i)),
    measureReal_iUnion_fintype (c.unitRemovedCap_pairwise_disjoint hA i)
      (c.measurableSet_unitRemovedCap i)]

theorem sphereMeasure_real_unitRemovedCap (i j : Fin 4) :
    sphereMeasure.real (c.unitRemovedCap i j) = sphereMeasure.real (c.unitFaceCap i) -
      sphereMeasure.real (c.unitFaceCap i ∩ c.unitNeighborCap i j) := by
  have h := measureReal_sdiff_add_inter (μ := sphereMeasure) (s := c.unitFaceCap i)
    (c.measurableSet_unitNeighborCap i j)
  change sphereMeasure.real (c.unitFaceCap i \ c.unitNeighborCap i j) = _
  linarith

theorem sphereMeasure_real_unitFaceCap (hR : 1 / 2 ≤ c.radius) (i : Fin 4) :
    sphereMeasure.real (c.unitFaceCap i) = 2 * Real.pi * (1 - 1 / (2 * c.radius)) := by
  have hR0 : 0 < c.radius := by linarith
  have hn : ‖-c.point i‖ = c.radius := by rw [norm_neg, c.on_sphere]
  have hp : -c.point i ≠ 0 := norm_pos_iff.1 (hn.symm ▸ hR0)
  have hh : (1 / 2 : ℝ) / ‖-c.point i‖ = 1 / (2 * c.radius) := by rw [hn]; ring
  change sphereMeasure.real (sphereCap (-c.point i) (1 / 2)) = _
  rw [sphereMeasure_real_cap_normalized hp, hh]
  rw [hh]
  constructor
  · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (by positivity)
  · exact (div_le_one (by positivity : 0 < 2 * c.radius)).2 (by linarith)

theorem sphereMeasure_real_radiusExcludedCap (hR : 1 / 2 < c.radius) (i : Fin 4) :
    sphereMeasure.real (c.radiusExcludedCap i) =
      2 * Real.pi * (2 - 1 / (2 * c.radius ^ 2)) := by
  have hR0 : 0 < c.radius := by linarith
  have hn : ‖-c.point i‖ = c.radius := by rw [norm_neg, c.on_sphere]
  have hp : -c.point i ≠ 0 := norm_pos_iff.1 (hn.symm ▸ hR0)
  have hh : ((1 - 2 * c.radius ^ 2) / (2 * c.radius)) / ‖-c.point i‖ =
      1 / (2 * c.radius ^ 2) - 1 := by
    rw [hn]
    field_simp
  have hq : 1 / (2 * c.radius ^ 2) - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have : 0 < 1 / (2 * c.radius ^ 2) := by positivity
      linarith
    · have hs : 1 / (2 * c.radius ^ 2) < 2 := by
        apply (div_lt_iff₀ (by positivity : 0 < 2 * c.radius ^ 2)).2
        nlinarith
      linarith
  change sphereMeasure.real (openSphereCap (-c.point i) _) = _
  rw [sphereMeasure_real_openCap_normalized hp (hh.symm ▸ hq), hh]
  ring

theorem integral_unitFaceNormals (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4)
    {f : UnitSphere → ℝ} (hf : Integrable f sphereMeasure) :
    (∫ u in c.unitFaceNormals i, f u ∂sphereMeasure) =
      (∫ u in c.unitFaceCap i, f u ∂sphereMeasure) -
        ∑ j, ∫ u in c.unitRemovedCap i j, f u ∂sphereMeasure := by
  have hs : (⋃ j, c.unitRemovedCap i j) ⊆ c.unitFaceCap i := by
    intro u hu
    obtain ⟨j, hj⟩ := mem_iUnion.1 hu
    exact hj.1
  rw [c.unitFaceNormals_eq_sdiff, setIntegral_sdiff
    (MeasurableSet.iUnion (c.measurableSet_unitRemovedCap i)) hf.integrableOn hs,
    integral_iUnion_fintype (c.measurableSet_unitRemovedCap i)
      (c.unitRemovedCap_pairwise_disjoint hA i) (fun _ ↦ hf.integrableOn)]

theorem sphereMeasure_real_radiusFaceNormals (hA : c.totalDeficit ≤ 2 / 25)
    (hR : 1 / 2 < c.radius) :
    sphereMeasure.real c.radiusFaceNormals =
      4 * Real.pi - 8 * Real.pi * (2 - 1 / (2 * c.radius ^ 2)) +
        (sphereMeasure.real (c.radiusExcludedCap 0 ∩ c.radiusExcludedCap 1) +
          sphereMeasure.real (c.radiusExcludedCap 0 ∩ c.radiusExcludedCap 2) +
          sphereMeasure.real (c.radiusExcludedCap 0 ∩ c.radiusExcludedCap 3) +
          sphereMeasure.real (c.radiusExcludedCap 1 ∩ c.radiusExcludedCap 2) +
          sphereMeasure.real (c.radiusExcludedCap 1 ∩ c.radiusExcludedCap 3) +
          sphereMeasure.real (c.radiusExcludedCap 2 ∩ c.radiusExcludedCap 3)) := by
  have hR0 : 0 < c.radius := by linarith
  rw [c.radiusFaceNormals_eq_compl hR0,
    measureReal_compl (MeasurableSet.iUnion c.measurableSet_radiusExcludedCap),
    sphereMeasure_real_univ, measureReal_iUnion_four_of_no_triples c.radiusExcludedCap
      c.measurableSet_radiusExcludedCap (fun _ _ _ hij hik hjk ↦
        c.radiusExcludedCap_triple_empty hA hR0 hij hik hjk)]
  simp only [c.sphereMeasure_real_radiusExcludedCap hR, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem support_unitFaceNormals {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    (i : Fin 4) {u : UnitSphere} (hu : u ∈ c.unitFaceNormals i) :
    support (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      ⟪(u : Space), c.point i⟫_ℝ + 1 := by
  have hx : c.point i + (u : Space) ∈ clippedOuterBody c.radius (range c.point) hne := hu
  have he : ⟪(u : Space), c.point i + (u : Space)⟫_ℝ =
      ⟪(u : Space), c.point i⟫_ℝ + 1 := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow]
  apply le_antisymm
  · apply (support_le_iff _ _ _).2
    intro y hy
    have h := unitSphere_normal_supports_ball
      (show ‖c.point i + (u : Space) - c.point i‖ = 1 by simp only [add_sub_cancel_left, u.norm_eq_one])
      (hy.2 _ ⟨i, rfl⟩)
    rw [add_sub_cancel_left, inner_sub_right, he] at h
    linarith
  · rw [← he]
    exact inner_le_support _ _ hx

theorem support_radiusFaceNormals {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    {u : UnitSphere} (hu : u ∈ c.radiusFaceNormals) :
    support (clippedOuterBody c.radius (range c.point) hne) (u : Space) = c.radius := by
  apply le_antisymm (support_le_of_norm_le (fun _ hy ↦ clippedOuterBody_norm_le hy) u.norm_eq_one)
  have h := inner_le_support (clippedOuterBody c.radius (range c.point) hne) (u : Space) hu
  simpa only [real_inner_smul_right, real_inner_self_eq_norm_sq, u.norm_eq_one, one_pow,
    mul_one] using h

theorem normalSupport_unitFaceNormals {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    (i : Fin 4) {u : UnitSphere} (hu : u ∈ c.unitFaceNormals i) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      c.point i + (u : Space) := by
  have hR : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  have he := supportPoint_unique_of_ball_sum (clippedBodies_complement c.radius (range c.point) hne hR)
    u.norm_eq_one hu (by
      rw [c.support_unitFaceNormals i hu, inner_add_right, real_inner_self_eq_norm_sq,
        u.norm_eq_one, one_pow])
  simpa only [normalSupport, NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one] using he.symm

theorem normalSupport_radiusFaceNormals {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    {u : UnitSphere} (hu : u ∈ c.radiusFaceNormals) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      c.radius • (u : Space) := by
  have hR : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  have he := supportPoint_unique_of_ball_sum (clippedBodies_complement c.radius (range c.point) hne hR)
    u.norm_eq_one hu (by
      rw [c.support_radiusFaceNormals hu, real_inner_smul_right, real_inner_self_eq_norm_sq,
        u.norm_eq_one, one_pow, mul_one])
  simpa only [normalSupport, NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one] using he.symm

end BlaschkeLebesgue.BalancedContacts
