module

public import BlaschkeLebesgue.LensScalar

/-! # The upper latitude where two cap boundary circles meet -/

public noncomputable section

open Set

namespace BlaschkeLebesgue

@[expose] def lensUpperHeight (b c : ℝ) : ℝ :=
  b * c + Real.sqrt ((1 - b ^ 2) * (1 - c ^ 2))

theorem lensGram_eq_square (a b c : ℝ) :
    lensGram a b c = (1 - b ^ 2) * (1 - c ^ 2) - (a - b * c) ^ 2 := by
  unfold lensGram
  ring

theorem lensUpperHeight_gram_zero {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) : lensGram (lensUpperHeight b c) b c = 0 := by
  rw [lensGram_eq_square, lensUpperHeight, add_sub_cancel_left,
    Real.sq_sqrt (mul_nonneg (one_sub_sq_pos_of_mem_unitInterval hb).le
      (one_sub_sq_pos_of_mem_unitInterval hc).le), sub_self]

theorem lensUpperHeight_mem_Ioo {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ c) : lensUpperHeight b c ∈ Ioo (-1 : ℝ) 1 := by
  have hb' := one_sub_sq_pos_of_mem_unitInterval hb
  have hc' := one_sub_sq_pos_of_mem_unitInterval hc
  have hprod := Real.sq_sqrt (mul_nonneg hb'.le hc'.le)
  have hn := Real.sqrt_nonneg ((1 - b ^ 2) * (1 - c ^ 2))
  have hlo : -1 < b * c := by nlinarith [sq_nonneg (b + c)]
  have hhi : b * c < 1 := by nlinarith [sq_nonneg (b - c)]
  have hs := sq_pos_of_ne_zero (sub_ne_zero.2 hbc)
  unfold lensUpperHeight
  constructor <;> nlinarith

theorem lt_lensUpperHeight {a b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram a b c) : a < lensUpperHeight b c := by
  rw [lensGram_eq_square] at hD
  have hs := Real.sq_sqrt (mul_nonneg (one_sub_sq_pos_of_mem_unitInterval hb).le
    (one_sub_sq_pos_of_mem_unitInterval hc).le)
  have hn := Real.sqrt_nonneg ((1 - b ^ 2) * (1 - c ^ 2))
  unfold lensUpperHeight
  nlinarith

theorem lensLowerHeight_lt {a b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram a b c) :
    b * c - Real.sqrt ((1 - b ^ 2) * (1 - c ^ 2)) < a := by
  rw [lensGram_eq_square] at hD
  have hs := Real.sq_sqrt (mul_nonneg (one_sub_sq_pos_of_mem_unitInterval hb).le
    (one_sub_sq_pos_of_mem_unitInterval hc).le)
  have hn := Real.sqrt_nonneg ((1 - b ^ 2) * (1 - c ^ 2))
  nlinarith

theorem lensGram_pos_between {a b c z : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram a b c)
    (hz : z ∈ Ico a (lensUpperHeight b c)) : 0 < lensGram z b c := by
  have hl := (lensLowerHeight_lt hb hc hD).trans_le hz.1
  have hs := Real.sq_sqrt (mul_nonneg (one_sub_sq_pos_of_mem_unitInterval hb).le
    (one_sub_sq_pos_of_mem_unitInterval hc).le)
  have hp := mul_pos (sub_pos.2 hz.2) (sub_pos.2 hl)
  rw [lensGram_eq_square]
  unfold lensUpperHeight at hp
  nlinarith

theorem lensGram_nonpos_above {b c z : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hz : lensUpperHeight b c ≤ z) : lensGram z b c ≤ 0 := by
  have hs := Real.sq_sqrt (mul_nonneg (one_sub_sq_pos_of_mem_unitInterval hb).le
    (one_sub_sq_pos_of_mem_unitInterval hc).le)
  have hn := Real.sqrt_nonneg ((1 - b ^ 2) * (1 - c ^ 2))
  rw [lensGram_eq_square]
  unfold lensUpperHeight at hz
  nlinarith

theorem latitudeCapThreshold_upper_other {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) : latitudeCapThreshold (lensUpperHeight b c) c b = 1 := by
  have hb0 := (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hb)).ne'
  have hc0 := (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hc)).ne'
  rw [latitudeCapThreshold, lensUpperHeight,
    Real.sqrt_mul (one_sub_sq_pos_of_mem_unitInterval hb).le]
  field_simp
  ring

theorem lensUpperHeight_symm (b c : ℝ) : lensUpperHeight b c = lensUpperHeight c b := by
  unfold lensUpperHeight
  rw [mul_comm b c, mul_comm (1 - b ^ 2)]

theorem lensUpperHeight_numerators {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hcb : c < b) :
    0 < b - c * lensUpperHeight b c ∧ c - b * lensUpperHeight b c < 0 := by
  let t := lensUpperHeight b c
  have ht : t ∈ Ioo (-1 : ℝ) 1 := lensUpperHeight_mem_Ioo hb hc (ne_of_gt hcb)
  have hz : lensGram t b c = 0 := lensUpperHeight_gram_zero hb hc
  have hd : 0 < Real.sqrt ((1 - b ^ 2) * (1 - c ^ 2)) :=
    Real.sqrt_pos.2 (mul_pos (one_sub_sq_pos_of_mem_unitInterval hb)
      (one_sub_sq_pos_of_mem_unitInterval hc))
  have hp : (b - c * t) * (c - b * t) < 0 := by
    have he : (b - c * t) * (c - b * t) = (b * c - t) * (1 - t ^ 2) := by
      unfold lensGram at hz
      linear_combination t * hz
    rw [he]
    exact mul_neg_of_neg_of_pos (by dsimp [t, lensUpperHeight]; linarith)
      (one_sub_sq_pos_of_mem_unitInterval ht)
  have hdif : 0 < (b - c * t) - (c - b * t) := by
    have h := mul_pos (sub_pos.2 hcb) (show 0 < 1 + t by linarith [ht.1])
    nlinarith
  rcases mul_neg_iff.1 hp with h | h
  · exact h
  · exfalso
    linarith [h.1, h.2]

theorem latitudeCapThreshold_upper_of_lt {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hcb : c < b) :
    latitudeCapThreshold b c (lensUpperHeight b c) = 1 := by
  have ht := lensUpperHeight_mem_Ioo hb hc (ne_of_gt hcb)
  have hs := lensGram_threshold_identity hc ht b
  rw [lensUpperHeight_gram_zero hb hc, zero_div] at hs
  have hp : 0 < latitudeCapThreshold b c (lensUpperHeight b c) := by
    exact div_pos (lensUpperHeight_numerators hb hc hcb).1
      (mul_pos (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hc))
        (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval ht)))
  nlinarith

theorem latitudeCapThreshold_upper_of_gt {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b < c) :
    latitudeCapThreshold b c (lensUpperHeight b c) = -1 := by
  have ht := lensUpperHeight_mem_Ioo hb hc (ne_of_lt hbc)
  have hs := lensGram_threshold_identity hc ht b
  rw [lensUpperHeight_gram_zero hb hc, zero_div] at hs
  have hn := (lensUpperHeight_numerators hc hb hbc).2
  rw [lensUpperHeight_symm c b] at hn
  have hp : latitudeCapThreshold b c (lensUpperHeight b c) < 0 := by
    exact div_neg_of_neg_of_pos hn
      (mul_pos (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hc))
        (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval ht)))
  nlinarith

theorem lensAreaExpression_upper {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ c) :
    lensAreaExpression (lensUpperHeight b c) b c =
      if b < c then 2 * Real.pi * (1 - lensUpperHeight b c) else 0 := by
  unfold lensAreaExpression
  rw [latitudeCapThreshold_upper_other hb hc, Real.arccos_one, mul_zero, sub_zero]
  rcases lt_or_gt_of_ne hbc with h | h
  · rw [ite_eq_left h, latitudeCapThreshold_upper_of_gt hb hc h, Real.arccos_neg_one,
      lensUpperHeight_symm b c, latitudeCapThreshold_upper_of_lt hc hb h, Real.arccos_one]
    ring
  · rw [ite_eq_right (not_lt_of_gt h), latitudeCapThreshold_upper_of_lt hb hc h, Real.arccos_one,
      lensUpperHeight_symm b c, latitudeCapThreshold_upper_of_gt hc hb h, Real.arccos_neg_one]
    ring

theorem lensMomentExpression_upper {b c : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ c) :
    lensMomentExpression (lensUpperHeight b c) b c =
      if b < c then Real.pi * (1 - (lensUpperHeight b c) ^ 2) else 0 := by
  unfold lensMomentExpression
  rw [latitudeCapThreshold_upper_other hb hc, Real.arccos_one, mul_zero, add_zero,
    lensUpperHeight_gram_zero hb hc, Real.sqrt_zero, mul_zero, sub_zero]
  rcases lt_or_gt_of_ne hbc with h | h
  · rw [ite_eq_left h, latitudeCapThreshold_upper_of_gt hb hc h, Real.arccos_neg_one]
    ring
  · rw [ite_eq_right (not_lt_of_gt h), latitudeCapThreshold_upper_of_lt hb hc h, Real.arccos_one, mul_zero]

theorem arccos_latitudeCapThreshold_above {b c z : ℝ} (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ c) (hz : z ∈ Ico (lensUpperHeight b c) 1) :
    Real.arccos (latitudeCapThreshold b c z) = if b < c then Real.pi else 0 := by
  have ht := lensUpperHeight_mem_Ioo hb hc hbc
  have hz' : z ∈ Ioo (-1 : ℝ) 1 := ⟨ht.1.trans_le hz.1, hz.2⟩
  have hdpos := mul_pos (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hc))
    (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hz'))
  have hs : 1 ≤ (latitudeCapThreshold b c z) ^ 2 := by
    have h := lensGram_threshold_identity hc hz' b
    have hn := div_nonpos_of_nonpos_of_nonneg (lensGram_nonpos_above hb hc hz.1)
      (mul_nonneg (one_sub_sq_pos_of_mem_unitInterval hc).le
        (one_sub_sq_pos_of_mem_unitInterval hz').le)
    linarith
  rcases lt_or_gt_of_ne hbc with h | h
  · rw [ite_eq_left h]
    apply Real.arccos_eq_pi.2
    have hnt := (lensUpperHeight_numerators hc hb h).2
    rw [lensUpperHeight_symm c b] at hnt
    have hn : b - c * z < 0 := by
      by_cases hc0 : 0 ≤ c
      · have hh := mul_le_mul_of_nonneg_left hz.1 hc0
        linarith
      · have hh := mul_le_mul_of_nonpos_left hz.2.le (le_of_not_ge hc0)
        linarith
    have hq : latitudeCapThreshold b c z < 0 := div_neg_of_neg_of_pos hn hdpos
    nlinarith
  · rw [ite_eq_right (not_lt_of_gt h)]
    apply Real.arccos_eq_zero.2
    have hnt := (lensUpperHeight_numerators hb hc h).1
    have hn : 0 < b - c * z := by
      by_cases hc0 : 0 ≤ c
      · have hh := mul_le_mul_of_nonneg_left hz.2.le hc0
        linarith
      · have hh := mul_le_mul_of_nonpos_left hz.1 (le_of_not_ge hc0)
        linarith
    have hq : 0 < latitudeCapThreshold b c z := div_pos hn hdpos
    nlinarith

end BlaschkeLebesgue
