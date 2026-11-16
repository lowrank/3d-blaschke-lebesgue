module

public import BlaschkeLebesgue.CapArea
public import BlaschkeLebesgue.AntipodalIntegration
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Open caps and null cap boundaries

Continuity from below extends the cap-area formula to strict caps, including
hemispheres. Equal areas of open and closed caps then show that their boundary
circles have zero spherical measure.
-/

public noncomputable section

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace Topology

namespace BlaschkeLebesgue

@[expose] def openSphereCap (u : Space) (c : ℝ) : Set UnitSphere :=
  {v | c < ⟪u, (v : Space)⟫_ℝ}

theorem measurableSet_openSphereCap (u : Space) (c : ℝ) :
    MeasurableSet (openSphereCap u c) :=
  (isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)).measurableSet

private def capHeight (c : ℝ) (n : ℕ) : ℝ := c + (1 - c) / ((n : ℝ) + 1)

private theorem capHeight_gt {c : ℝ} (hc : c < 1) (n : ℕ) : c < capHeight c n := by
  unfold capHeight
  have : 0 < (1 - c) / ((n : ℝ) + 1) := by positivity
  linarith

private theorem capHeight_le_one {c : ℝ} (hc : c ≤ 1) (n : ℕ) :
    capHeight c n ≤ 1 := by
  unfold capHeight
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hh : (1 - c) / ((n : ℝ) + 1) ≤ 1 - c := by
    apply (div_le_iff₀ hn).2
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (Nat.cast_nonneg (α := ℝ) n)]
  linarith

private theorem capHeight_antitone {c : ℝ} (hc : c ≤ 1) : Antitone (capHeight c) := by
  intro m n hmn
  unfold capHeight
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (sub_nonneg.2 hc)
  · positivity
  · exact_mod_cast Nat.add_le_add_right hmn 1

private theorem capHeight_tendsto (c : ℝ) : Tendsto (capHeight c) atTop (𝓝 c) := by
  change Tendsto (fun n : ℕ ↦ c + (1 - c) / ((n : ℝ) + 1)) atTop (𝓝 c)
  have h := (tendsto_const_nhds (x := c)).add
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 - c))
  simpa only [mul_zero, add_zero, mul_one_div] using h

private theorem openSphereCap_eq_iUnion {u : Space} {c : ℝ} (hc : c < 1) :
    openSphereCap u c = ⋃ n : ℕ, sphereCap u (capHeight c n) := by
  ext v
  constructor
  · intro hv
    have he : ∀ᶠ n : ℕ in atTop, capHeight c n < ⟪u, (v : Space)⟫_ℝ :=
      (capHeight_tendsto c).eventually (eventually_lt_nhds hv)
    obtain ⟨n, hn⟩ := he.exists
    exact mem_iUnion.2 ⟨n, hn.le⟩
  · intro hv
    obtain ⟨n, hn⟩ := mem_iUnion.1 hv
    exact (capHeight_gt hc n).trans_le hn

/-- The exact area of a strict cap, with the open hemisphere as the endpoint. -/
theorem sphereMeasure_openCap {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) :
    sphereMeasure (openSphereCap u c) = ENNReal.ofReal (2 * Real.pi * (1 - c)) := by
  have hm : Monotone (fun n : ℕ ↦ sphereCap u (capHeight c n)) := by
    intro m n hmn v hv
    exact (capHeight_antitone hc1.le hmn).trans hv
  have hlim := tendsto_measure_iUnion_atTop (μ := sphereMeasure) hm
  have harea : (fun n : ℕ ↦ sphereMeasure (sphereCap u (capHeight c n))) =
      fun n ↦ ENNReal.ofReal (2 * Real.pi * (1 - capHeight c n)) := by
    funext n
    exact sphereMeasure_cap hu (hc.trans_lt (capHeight_gt hc1 n))
      (capHeight_le_one hc1.le n)
  change Tendsto (fun n : ℕ ↦ sphereMeasure (sphereCap u (capHeight c n))) _ _ at hlim
  rw [← openSphereCap_eq_iUnion hc1, harea] at hlim
  have hlim' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 * Real.pi * (1 - capHeight c n)))
      atTop (𝓝 (ENNReal.ofReal (2 * Real.pi * (1 - c)))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds.sub (capHeight_tendsto c)).const_mul (2 * Real.pi))
  exact tendsto_nhds_unique hlim hlim'

theorem sphereMeasure_real_openCap {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) :
    sphereMeasure.real (openSphereCap u c) = 2 * Real.pi * (1 - c) := by
  rw [measureReal_def, sphereMeasure_openCap hu hc hc1,
    ENNReal.toReal_ofReal (by positivity)]

theorem sphereCap_eq_compl_openCap_neg (u : Space) (c : ℝ) :
    sphereCap u c = (openSphereCap (-u) (-c))ᶜ := by
  ext v
  simp only [sphereCap, openSphereCap, mem_ofPred_eq, mem_compl_iff, inner_neg_left, not_lt]
  exact neg_le_neg_iff.symm

theorem openSphereCap_eq_compl_cap_neg (u : Space) (c : ℝ) :
    openSphereCap u c = (sphereCap (-u) (-c))ᶜ := by
  ext v
  simp only [sphereCap, openSphereCap, mem_ofPred_eq, mem_compl_iff, inner_neg_left, not_le]
  exact neg_lt_neg_iff.symm

theorem sphereMeasure_real_cap_nonneg {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    sphereMeasure.real (sphereCap u c) = 2 * Real.pi * (1 - c) := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [sphereCap_eq_compl_openCap_neg, measureReal_compl (measurableSet_openSphereCap _ _),
      sphereMeasure_real_univ, sphereMeasure_real_openCap (by simpa using hu) (by norm_num)
        (by norm_num)]
    ring
  · exact sphereMeasure_real_cap hu hc hc1

theorem openSphereCap_one {u : Space} (hu : ‖u‖ = 1) : openSphereCap u 1 = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro v hv
  have h := (abs_le.1 (abs_real_inner_le_norm u (v : Space))).2
  rw [hu, v.norm_eq_one, mul_one] at h
  exact (not_lt_of_ge h) hv

theorem sphereMeasure_real_openCap_nonneg {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    sphereMeasure.real (openSphereCap u c) = 2 * Real.pi * (1 - c) := by
  rcases hc1.lt_or_eq with hc1 | rfl
  · exact sphereMeasure_real_openCap hu hc hc1
  · simp [openSphereCap_one hu]

/-- Closed cap area for the complete range of heights, including both endpoints. -/
theorem sphereMeasure_real_cap_of_mem_Icc {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : c ∈ Icc (-1 : ℝ) 1) :
    sphereMeasure.real (sphereCap u c) = 2 * Real.pi * (1 - c) := by
  by_cases hc0 : 0 ≤ c
  · exact sphereMeasure_real_cap_nonneg hu hc0 hc.2
  · rw [sphereCap_eq_compl_openCap_neg, measureReal_compl (measurableSet_openSphereCap _ _),
      sphereMeasure_real_univ, sphereMeasure_real_openCap_nonneg (by simpa using hu)
        (by linarith) (by linarith [hc.1])]
    ring

/-- Strict and non-strict caps have the same area throughout the complete range. -/
theorem sphereMeasure_real_openCap_of_mem_Icc {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : c ∈ Icc (-1 : ℝ) 1) :
    sphereMeasure.real (openSphereCap u c) = 2 * Real.pi * (1 - c) := by
  rw [openSphereCap_eq_compl_cap_neg, measureReal_compl (measurableSet_sphereCap _ _),
    sphereMeasure_real_univ, sphereMeasure_real_cap_of_mem_Icc (by simpa using hu)
      (show -c ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hc.2], by linarith [hc.1]⟩)]
  ring

/-- Every latitude circle, pole, or empty level set has zero spherical measure. -/
theorem sphereMeasure_inner_level_unit {u : Space} (hu : ‖u‖ = 1) (c : ℝ) :
    sphereMeasure {v : UnitSphere | ⟪u, (v : Space)⟫_ℝ = c} = 0 := by
  by_cases hc : c ∈ Icc (-1 : ℝ) 1
  · have he : {v : UnitSphere | ⟪u, (v : Space)⟫_ℝ = c} =
        sphereCap u c \ openSphereCap u c := by
      ext v
      simp only [sphereCap, openSphereCap, mem_ofPred_eq, Set.mem_sdiff, not_lt]
      exact ⟨fun h ↦ ⟨h.ge, h.le⟩, fun h ↦ le_antisymm h.2 h.1⟩
    have hsub : openSphereCap u c ⊆ sphereCap u c := fun _ hv ↦
      (show c < ⟪u, _⟫_ℝ from hv).le
    apply (measureReal_eq_zero_iff).1
    rw [he, measureReal_sdiff hsub (measurableSet_openSphereCap u c),
      sphereMeasure_real_cap_of_mem_Icc hu hc, sphereMeasure_real_openCap_of_mem_Icc hu hc,
      sub_self]
  · have he : {v : UnitSphere | ⟪u, (v : Space)⟫_ℝ = c} = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro v hv
      have h := abs_real_inner_le_norm u (v : Space)
      rw [hu, v.norm_eq_one, mul_one, hv] at h
      exact hc (abs_le.1 h)
    rw [he, measure_empty]

/-- Intersecting the sphere with any affine plane produces a null set. -/
theorem sphereMeasure_inner_level {u : Space} (hu : u ≠ 0) (c : ℝ) :
    sphereMeasure {v : UnitSphere | ⟪u, (v : Space)⟫_ℝ = c} = 0 := by
  have hn : ‖‖u‖⁻¹ • u‖ = 1 := by simp [norm_smul, hu]
  have he : {v : UnitSphere | ⟪u, (v : Space)⟫_ℝ = c} =
      {v : UnitSphere | ⟪‖u‖⁻¹ • u, (v : Space)⟫_ℝ = c / ‖u‖} := by
    ext v
    simp only [mem_ofPred_eq, real_inner_smul_left, ← div_eq_inv_mul]
    exact (div_left_inj' (norm_ne_zero_iff.2 hu)).symm
  rw [he]
  exact sphereMeasure_inner_level_unit hn _

theorem sphereCap_ae_eq_openCap {u : Space} (hu : u ≠ 0) (c : ℝ) :
    sphereCap u c =ᵐ[sphereMeasure] openSphereCap u c := by
  have h : ∀ᵐ v : UnitSphere ∂sphereMeasure, ⟪u, (v : Space)⟫_ℝ ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using sphereMeasure_inner_level hu c
  filter_upwards [h] with v hv
  change (c ≤ ⟪u, (v : Space)⟫_ℝ) = (c < ⟪u, (v : Space)⟫_ℝ)
  exact propext (lt_iff_le_and_ne.trans (and_iff_left hv.symm)).symm

theorem sphereCap_normalize {u : Space} (hu : u ≠ 0) (c : ℝ) :
    sphereCap u c = sphereCap (‖u‖⁻¹ • u) (c / ‖u‖) := by
  ext v
  simp only [sphereCap, mem_ofPred_eq, real_inner_smul_left, ← div_eq_inv_mul]
  exact (div_le_div_iff_of_pos_right (norm_pos_iff.2 hu)).symm

theorem openSphereCap_normalize {u : Space} (hu : u ≠ 0) (c : ℝ) :
    openSphereCap u c = openSphereCap (‖u‖⁻¹ • u) (c / ‖u‖) := by
  ext v
  simp only [openSphereCap, mem_ofPred_eq, real_inner_smul_left, ← div_eq_inv_mul]
  exact (div_lt_div_iff_of_pos_right (norm_pos_iff.2 hu)).symm

theorem sphereMeasure_real_cap_normalized {u : Space} (hu : u ≠ 0) {c : ℝ}
    (hc : c / ‖u‖ ∈ Icc (-1 : ℝ) 1) :
    sphereMeasure.real (sphereCap u c) = 2 * Real.pi * (1 - c / ‖u‖) := by
  rw [sphereCap_normalize hu c]
  exact sphereMeasure_real_cap_of_mem_Icc (by simp [norm_smul, hu]) hc

theorem sphereMeasure_real_openCap_normalized {u : Space} (hu : u ≠ 0) {c : ℝ}
    (hc : c / ‖u‖ ∈ Icc (-1 : ℝ) 1) :
    sphereMeasure.real (openSphereCap u c) = 2 * Real.pi * (1 - c / ‖u‖) := by
  rw [openSphereCap_normalize hu c]
  exact sphereMeasure_real_openCap_of_mem_Icc (by simp [norm_smul, hu]) hc

theorem sphereCap_eq_univ_of_le_neg_one {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : c ≤ -1) : sphereCap u c = univ := by
  apply eq_univ_of_forall
  intro v
  have h := (abs_le.1 (abs_real_inner_le_norm u (v : Space))).1
  rw [hu, v.norm_eq_one, mul_one] at h
  exact hc.trans h

theorem sphereCap_eq_empty_of_one_lt {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : 1 < c) : sphereCap u c = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro v hv
  have h := (abs_le.1 (abs_real_inner_le_norm u (v : Space))).2
  rw [hu, v.norm_eq_one, mul_one] at h
  exact (not_le_of_gt hc) (hv.trans h)

end BlaschkeLebesgue
