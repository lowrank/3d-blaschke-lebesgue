module

public import BlaschkeLebesgue.CapIntegration
public import BlaschkeLebesgue.Certificates.PositiveCaps

/-!
# Spherical integrals of the exact radial certificates

The rational annulus sums are lower bounds for the actual tangent-deficit
integral of the centered body. This step uses the proved cap area, propagation,
and separation theorems, rather than an assumed integration interface.
-/

public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BlaschkeLebesgue.Certificates.RadialArithmetic

theorem cosine_pos {k : ℕ} (hk : k < gridSize) : 0 < cosine k := by
  have hk' : (k : ℚ) < gridSize := by exact_mod_cast hk
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  have hn : (0 : ℚ) < gridSize := by norm_num [gridSize]
  apply div_pos
  · nlinarith only [mul_pos (sub_pos.2 hk') (add_pos_of_pos_of_nonneg hn hk0)]
  · positivity

@[expose] def gridAnnulus (u : Space) (j : ℕ) : Set UnitSphere :=
  sphereAnnulus u (cosine (j + 1)) (cosine j)

theorem measurableSet_gridAnnulus (u : Space) (j : ℕ) :
    MeasurableSet (gridAnnulus u j) := measurableSet_sphereAnnulus _ _ _

theorem gridCap_monotone (u : Space) : Monotone (fun j ↦ sphereCap u (cosine j : ℝ)) := by
  intro j k hjk
  exact sphereCap_antitone u (by exact_mod_cast cosine_antitone hjk)

theorem gridAnnulus_subset_cap (u : Space) {j n : ℕ} (h : j + 1 ≤ n) :
    gridAnnulus u j ⊆ sphereCap u (cosine n : ℝ) :=
  sdiff_subset.trans (gridCap_monotone u h)

theorem gridAnnulus_disjoint_of_lt (u : Space) {j k : ℕ} (h : j < k) :
    Disjoint (gridAnnulus u j) (gridAnnulus u k) := by
  apply Set.disjoint_left.2
  intro x hx hy
  exact hy.2 (gridAnnulus_subset_cap u (by omega) hx)

theorem gridAnnulus_pairwise (u : Space) : Pairwise (fun j k ↦
    Disjoint (gridAnnulus u j) (gridAnnulus u k)) := by
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact gridAnnulus_disjoint_of_lt u h
  · exact (gridAnnulus_disjoint_of_lt u h).symm

theorem gridAnnulus_family_pairwise {ι : Type*} (u : ι → Space) (n : ℕ)
    (hd : Pairwise (fun i j ↦ Disjoint (sphereCap (u i) (cosine n : ℝ))
      (sphereCap (u j) (cosine n : ℝ)))) :
    Pairwise (fun a b : ι × Fin n ↦
      Disjoint (gridAnnulus (u a.1) a.2) (gridAnnulus (u b.1) b.2)) := by
  rintro ⟨a, j⟩ ⟨b, k⟩ hne
  by_cases hab : a = b
  · subst b
    apply gridAnnulus_pairwise
    intro hjk
    exact hne (Prod.ext rfl (Fin.ext hjk))
  · exact (hd hab).mono (gridAnnulus_subset_cap _ (by omega))
      (gridAnnulus_subset_cap _ (by omega))

theorem sphereCap_disjoint_of_sphericalCap {u v : Space} {a b : ℝ}
    (h : Disjoint (sphericalCap u a) (sphericalCap v b)) :
    Disjoint (sphereCap u a) (sphereCap v b) := by
  apply Set.disjoint_left.2
  intro x hx hy
  exact Set.disjoint_left.1 h (mem_sphereCap_iff.1 hx) (mem_sphereCap_iff.1 hy)

theorem gridAnnulus_real_measure {u : Space} (hu : ‖u‖ = 1) {j : ℕ}
    (hj : j + 1 < gridSize) :
    sphereMeasure.real (gridAnnulus u j) =
      2 * Real.pi * ((cosine j : ℝ) - (cosine (j + 1) : ℝ)) :=
  sphereMeasure_real_annulus hu (by exact_mod_cast cosine_pos hj)
    (by exact_mod_cast cosine_antitone (Nat.le_succ j))
    (by exact_mod_cast (cosine_bounds j).2)

theorem exactSum_eq_sum (p : Parameters) (k : ℕ) (xs : List ℕ) :
    exactSum p k xs = ∑ j : Fin xs.length, ringTerm p (k + j) xs[j] := by
  induction xs generalizing k with
  | nil => simp [exactSum]
  | cons x xs ih =>
    simp [exactSum, Fin.sum_univ_succ, ih, Nat.add_comm, Nat.add_left_comm]

theorem sum_gridAnnulus_contributions (p : Parameters) {u : Space} (hu : ‖u‖ = 1)
    (xs : List ℕ) (hlen : xs.length < gridSize) :
    (∑ j : Fin xs.length, sphereMeasure.real (gridAnnulus u j) *
      (tangentGap p ((xs[j] : ℚ) / candidateScale) : ℝ)) =
      2 * Real.pi * (exactSum p 1 xs : ℝ) := by
  rw [exactSum_eq_sum, Rat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [gridAnnulus_real_measure hu (by omega)]
  simp only [ringTerm, Nat.add_comm 1 j.val, Nat.add_sub_cancel,
    Rat.cast_mul, Rat.cast_sub]
  ring

/-- Both four-contact cap families give their full exact contribution to the
actual spherical tangent-deficit integral. -/
theorem checkRow_gap_integral_lower {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4)
    {p : Parameters} {positive negative : List ℕ} (h : checkRow p positive negative = true)
    (hRlo : (p.lo : ℝ) ≤ b.radius) (hRhi : b.radius ≤ (p.hi : ℝ)) :
    8 * Real.pi * ((exactSum p 1 positive : ℝ) + (exactSum p 1 negative : ℝ)) ≤
      ∫ u : UnitSphere, Radial.gap (parameterM p) p.tangentPoint
        (radialFunction b.centeredBody u) ∂sphereMeasure := by
  classical
  have hrow := h
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hp0 : 0 < positive.length := by tauto
  have hn0 : 0 < negative.length := by tauto
  have hplen : positive.length < gridSize := by tauto
  have hnlen : negative.length < gridSize := by tauto
  let jp : Fin positive.length := ⟨positive.length - 1, by omega⟩
  let jn : Fin negative.length := ⟨negative.length - 1, by omega⟩
  have hjp : (jp : ℕ) + 1 = positive.length := by dsimp [jp]; omega
  have hjn : (jn : ℕ) + 1 = negative.length := by dsimp [jn]; omega
  let v := c.toBalancedContacts.direction
  have hRc : 0 < c.toBalancedContacts.radius := by
    rw [c.radius_eq]
    linarith only [b.radius_ge_half hK]
  have hv : ∀ i, ‖v i‖ = 1 := c.toBalancedContacts.direction_norm hRc
  have hvn : ∀ i, ‖-v i‖ = 1 := fun i ↦ by rw [norm_neg, hv i]
  have hpc : Pairwise (fun a d ↦ Disjoint (sphereCap (v a) (cosine positive.length : ℝ))
      (sphereCap (v d) (cosine positive.length : ℝ))) := by
    intro a d had
    have hh := sphereCap_disjoint_of_sphericalCap
      (checkRow_positive_caps_disjoint h c.toBalancedContacts (c.radius_eq ▸ hRlo) jp a d had)
    simpa only [hjp] using hh
  have hnc : Pairwise (fun a d ↦ Disjoint (sphereCap (-v a) (cosine negative.length : ℝ))
      (sphereCap (-v d) (cosine negative.length : ℝ))) := by
    intro a d had
    have hh := sphereCap_disjoint_of_sphericalCap
      (checkRow_negative_caps_disjoint h c.toBalancedContacts (c.radius_eq ▸ hRlo) jn a d had)
    simpa only [hjn] using hh
  have hcross : ∀ a d, Disjoint (sphereCap (v a) (cosine positive.length : ℝ))
      (sphereCap (-v d) (cosine negative.length : ℝ)) := by
    intro a d
    have hh := sphereCap_disjoint_of_sphericalCap
      (checkRow_opposite_caps_disjoint hK b c h hRlo hRhi jp jn a d)
    simpa only [hjp, hjn] using hh
  let S : (Fin 4 × Fin positive.length) ⊕ (Fin 4 × Fin negative.length) → Set UnitSphere
    | .inl (i, j) => gridAnnulus (v i) j
    | .inr (i, j) => gridAnnulus (-v i) j
  let a : (Fin 4 × Fin positive.length) ⊕ (Fin 4 × Fin negative.length) → ℝ
    | .inl (_, j) => tangentGap p ((positive[j] : ℚ) / candidateScale)
    | .inr (_, j) => tangentGap p ((negative[j] : ℚ) / candidateScale)
  have hS : ∀ i, MeasurableSet (S i) := by
    rintro (i | i) <;> exact measurableSet_gridAnnulus _ _
  have hSd : Pairwise (fun i j ↦ Disjoint (S i) (S j)) := by
    rintro (i | i) (j | j) hij
    · exact gridAnnulus_family_pairwise v positive.length hpc
        (fun heq ↦ hij (congrArg Sum.inl heq))
    · exact (hcross i.1 j.1).mono (gridAnnulus_subset_cap _ (by omega))
        (gridAnnulus_subset_cap _ (by omega))
    · exact ((hcross j.1 i.1).mono (gridAnnulus_subset_cap _ (by omega))
        (gridAnnulus_subset_cap _ (by omega))).symm
    · exact gridAnnulus_family_pairwise (fun i ↦ -v i) negative.length hnc
        (fun heq ↦ hij (congrArg Sum.inr heq))
  have hbound : ∀ i u, u ∈ S i → a i ≤
      Radial.gap (parameterM p) p.tangentPoint (radialFunction b.centeredBody u) := by
    rintro (⟨i, j⟩ | ⟨i, j⟩) u hu
    · exact checkRow_positive_gap_lower hK b c h hRlo hRhi j i (mem_sphereCap_iff.1 hu.1)
    · exact checkRow_negative_gap_lower hK b c h hRlo j i (mem_sphereCap_iff.1 hu.1)
  have h0 := b.centeredBody_zero_mem_interior hK
  have hm : (0 : ℝ) < parameterM p := by exact_mod_cast (checkRow_parameters_pos h).1
  have ht : (0 : ℝ) ≤ p.tangentPoint := by exact_mod_cast (checkRow_parameters_pos h).2.le
  have hh := sum_piece_bounds_le_integral (integrable_radial_gap h0 hm _)
    (fun u ↦ Radial.gap_nonneg hm ht (radialFunction_pos h0 (UnitSphere.ne_zero u)).le)
    S a hS hSd hbound
  have heq : (∑ i, sphereMeasure.real (S i) * a i) =
      8 * Real.pi * ((exactSum p 1 positive : ℝ) + (exactSum p 1 negative : ℝ)) := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    dsimp only [S, a]
    simp_rw [sum_gridAnnulus_contributions p (hv _) positive hplen,
      sum_gridAnnulus_contributions p (hvn _) negative hnlen]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rwa [heq] at hh

/-- The actual integral also dominates the downward-rounded sum used by the checker. -/
theorem checkRow_rounded_gap_integral_lower {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4)
    {p : Parameters} {positive negative : List ℕ} (h : checkRow p positive negative = true)
    (hRlo : (p.lo : ℝ) ≤ b.radius) (hRhi : b.radius ≤ (p.hi : ℝ)) :
    8 * Real.pi *
        (((((roundedSum p 1 positive + roundedSum p 1 negative : ℤ) : ℚ) /
          roundingScale : ℚ) : ℝ)) ≤
      ∫ u : UnitSphere, Radial.gap (parameterM p) p.tangentPoint
        (radialFunction b.centeredBody u) ∂sphereMeasure := by
  have hsum : ((roundedSum p 1 positive + roundedSum p 1 negative : ℤ) : ℚ) /
      roundingScale ≤ exactSum p 1 positive + exactSum p 1 negative := by
    simpa only [Int.cast_add, add_div] using
      add_le_add (roundedSum_le p 1 positive) (roundedSum_le p 1 negative)
  have hsum' :
      (((((roundedSum p 1 positive + roundedSum p 1 negative : ℤ) : ℚ) /
          roundingScale : ℚ) : ℝ)) ≤
        (exactSum p 1 positive : ℝ) + (exactSum p 1 negative : ℝ) := by
    exact_mod_cast hsum
  exact (mul_le_mul_of_nonneg_left hsum' (by positivity)).trans
    (checkRow_gap_integral_lower hK b c h hRlo hRhi)

end BlaschkeLebesgue.Certificates.RadialArithmetic
