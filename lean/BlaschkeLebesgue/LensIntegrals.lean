module

public import BlaschkeLebesgue.LensUpperHeight
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Closed forms of the actual cap-intersection latitude integrals -/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue

theorem integral_lensSlice_tail {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ c) :
    (∫ z in (lensUpperHeight b c)..1, 2 * Real.arccos (latitudeCapThreshold b c z)) =
      lensAreaExpression (lensUpperHeight b c) b c := by
  have ht := lensUpperHeight_mem_Ioo hb hc hbc
  have h : (∫ z in (lensUpperHeight b c)..1, 2 * Real.arccos (latitudeCapThreshold b c z)) =
      ∫ _ in (lensUpperHeight b c)..1, 2 * (if b < c then Real.pi else 0) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.2.le
    intro z hz
    dsimp only
    rw [arccos_latitudeCapThreshold_above hb hc hbc ⟨hz.1.le, hz.2⟩]
  rw [h, intervalIntegral.integral_const, smul_eq_mul, lensAreaExpression_upper hb hc hbc]
  split_ifs <;> ring

theorem intervalIntegrable_lensSlice_tail {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ c) :
    IntervalIntegrable (fun z ↦ 2 * Real.arccos (latitudeCapThreshold b c z))
      volume (lensUpperHeight b c) 1 := by
  have ht := lensUpperHeight_mem_Ioo hb hc hbc
  apply (intervalIntegrable_const (c := 2 * (if b < c then Real.pi else 0))).congr_uIoo
  intro z hz
  rw [uIoo_of_le ht.2.le] at hz
  dsimp only
  rw [arccos_latitudeCapThreshold_above hb hc hbc ⟨hz.1.le, hz.2⟩]

theorem integral_lensMomentSlice_tail {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ c) :
    (∫ z in (lensUpperHeight b c)..1, 2 * Real.arccos (latitudeCapThreshold b c z) * z) =
      lensMomentExpression (lensUpperHeight b c) b c := by
  have ht := lensUpperHeight_mem_Ioo hb hc hbc
  have h : (∫ z in (lensUpperHeight b c)..1, 2 * Real.arccos (latitudeCapThreshold b c z) * z) =
      ∫ z in (lensUpperHeight b c)..1, (2 * (if b < c then Real.pi else 0)) * z := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.2.le
    intro z hz
    dsimp only
    rw [arccos_latitudeCapThreshold_above hb hc hbc ⟨hz.1.le, hz.2⟩]
  rw [h, intervalIntegral.integral_const_mul, integral_id, lensMomentExpression_upper hb hc hbc]
  split_ifs <;> ring

theorem intervalIntegrable_lensMomentSlice_tail {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ c) :
    IntervalIntegrable (fun z ↦ 2 * Real.arccos (latitudeCapThreshold b c z) * z)
      volume (lensUpperHeight b c) 1 := by
  have ht := lensUpperHeight_mem_Ioo hb hc hbc
  have hi : IntervalIntegrable (fun z : ℝ ↦ (2 * (if b < c then Real.pi else 0)) * z)
      volume (lensUpperHeight b c) 1 := by
    have hcont : Continuous (fun z : ℝ ↦ (2 * (if b < c then Real.pi else 0)) * z) := by fun_prop
    exact hcont.intervalIntegrable _ _
  apply hi.congr_uIoo
  intro z hz
  rw [uIoo_of_le ht.2.le] at hz
  dsimp only
  rw [arccos_latitudeCapThreshold_above hb hc hbc ⟨hz.1.le, hz.2⟩]

theorem integral_lensSlice {a b c : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hbc : b ≠ c) (hD : 0 < lensGram a b c) :
    (∫ z in Icc a 1, 2 * Real.arccos (latitudeCapThreshold b c z)) = lensAreaExpression a b c := by
  let t := lensUpperHeight b c
  have ht : t ∈ Ioo (-1 : ℝ) 1 := lensUpperHeight_mem_Ioo hb hc hbc
  have hat : a < t := lt_lensUpperHeight hb hc hD
  have hz' : ∀ z ∈ Icc a t, z ∈ Ioo (-1 : ℝ) 1 := fun z hz ↦
    ⟨ha.1.trans_le hz.1, hz.2.trans_lt ht.2⟩
  have hcont : ContinuousOn (fun z ↦ lensAreaExpression z b c) (Icc a t) := by
    intro z hz
    exact (continuousAt_lensAreaExpression (hz' z hz) hb hc).continuousWithinAt
  have hi : IntervalIntegrable (fun z ↦ 2 * Real.arccos (latitudeCapThreshold b c z)) volume a t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hat.le]
    intro z hz
    exact (continuousAt_const.mul (Real.continuous_arccos.continuousAt.comp
      (continuousAt_latitudeCapThreshold hc (hz' z hz)))).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hat.le hcont
    (fun z hz ↦ hasDerivAt_lensAreaExpression (hz' z ⟨hz.1.le, hz.2.le⟩) hb hc
      (lensGram_pos_between hb hc hD ⟨hz.1.le, hz.2⟩)) hi.neg
  rw [intervalIntegral.integral_neg] at hFTC
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.2.le,
    ← intervalIntegral.integral_add_adjacent_intervals hi (intervalIntegrable_lensSlice_tail hb hc hbc),
    integral_lensSlice_tail hb hc hbc]
  linarith

theorem integral_lensMomentSlice {a b c : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hbc : b ≠ c) (hD : 0 < lensGram a b c) :
    (∫ z in Icc a 1, 2 * Real.arccos (latitudeCapThreshold b c z) * z) =
      lensMomentExpression a b c := by
  let t := lensUpperHeight b c
  have ht : t ∈ Ioo (-1 : ℝ) 1 := lensUpperHeight_mem_Ioo hb hc hbc
  have hat : a < t := lt_lensUpperHeight hb hc hD
  have hz' : ∀ z ∈ Icc a t, z ∈ Ioo (-1 : ℝ) 1 := fun z hz ↦
    ⟨ha.1.trans_le hz.1, hz.2.trans_lt ht.2⟩
  have hcont : ContinuousOn (fun z ↦ lensMomentExpression z b c) (Icc a t) := by
    intro z hz
    exact (continuousAt_lensMomentExpression (hz' z hz) hc).continuousWithinAt
  have hi : IntervalIntegrable (fun z ↦ 2 * Real.arccos (latitudeCapThreshold b c z) * z) volume a t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hat.le]
    intro z hz
    exact ((continuousAt_const.mul (Real.continuous_arccos.continuousAt.comp
      (continuousAt_latitudeCapThreshold hc (hz' z hz)))).mul continuousAt_id).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hat.le hcont
    (fun z hz ↦ hasDerivAt_lensMomentExpression (hz' z ⟨hz.1.le, hz.2.le⟩) hb hc
      (lensGram_pos_between hb hc hD ⟨hz.1.le, hz.2⟩)) hi.neg
  rw [intervalIntegral.integral_neg] at hFTC
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.2.le,
    ← intervalIntegral.integral_add_adjacent_intervals hi
      (intervalIntegrable_lensMomentSlice_tail hb hc hbc), integral_lensMomentSlice_tail hb hc hbc]
  linarith

end BlaschkeLebesgue
