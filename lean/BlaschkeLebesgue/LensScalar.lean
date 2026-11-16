module

public import BlaschkeLebesgue.CapLensSlices
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Scalar geometry and antiderivatives of spherical lenses -/

public noncomputable section

open Set

namespace BlaschkeLebesgue

@[expose] def lensGram (a b c : ℝ) : ℝ := 1 - a ^ 2 - b ^ 2 - c ^ 2 + 2 * a * b * c

@[expose] def lensAreaExpression (a b c : ℝ) : ℝ :=
  2 * Real.pi - 2 * Real.arccos (latitudeCapThreshold c b a) -
    2 * a * Real.arccos (latitudeCapThreshold b c a) -
    2 * b * Real.arccos (latitudeCapThreshold a c b)

@[expose] def lensMomentExpression (a b c : ℝ) : ℝ :=
  (1 - a ^ 2) * Real.arccos (latitudeCapThreshold b c a) +
    (1 - b ^ 2) * c * Real.arccos (latitudeCapThreshold a c b) - b * Real.sqrt (lensGram a b c)

theorem one_sub_sq_pos_of_mem_unitInterval {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  nlinarith [mul_pos (sub_pos.2 hx.2) (show 0 < x + 1 by linarith [hx.1])]

theorem lensGram_threshold_identity {c z : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (b : ℝ) :
    1 - (latitudeCapThreshold b c z) ^ 2 =
      lensGram z b c / ((1 - c ^ 2) * (1 - z ^ 2)) := by
  have hc' := one_sub_sq_pos_of_mem_unitInterval hc
  have hz' := one_sub_sq_pos_of_mem_unitInterval hz
  rw [latitudeCapThreshold, div_pow, mul_pow, Real.sq_sqrt hc'.le, Real.sq_sqrt hz'.le]
  unfold lensGram
  field_simp
  ring

theorem latitudeCapThreshold_mem_Ioo {c z b : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram z b c) :
    latitudeCapThreshold b c z ∈ Ioo (-1 : ℝ) 1 := by
  have h : 0 < 1 - (latitudeCapThreshold b c z) ^ 2 := by
    rw [lensGram_threshold_identity hc hz]
    exact div_pos hD (mul_pos (one_sub_sq_pos_of_mem_unitInterval hc)
      (one_sub_sq_pos_of_mem_unitInterval hz))
  constructor <;> nlinarith [sq_nonneg (latitudeCapThreshold b c z - 1),
    sq_nonneg (latitudeCapThreshold b c z + 1)]

theorem sqrt_lensGram_threshold {c z b : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram z b c) :
    Real.sqrt (1 - (latitudeCapThreshold b c z) ^ 2) =
      Real.sqrt (lensGram z b c) / (Real.sqrt (1 - c ^ 2) * Real.sqrt (1 - z ^ 2)) := by
  rw [lensGram_threshold_identity hc hz, Real.sqrt_div hD.le,
    Real.sqrt_mul (one_sub_sq_pos_of_mem_unitInterval hc).le]

theorem hasDerivAt_sqrt_one_sub_sq {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ Real.sqrt (1 - x ^ 2))
      (-z / Real.sqrt (1 - z ^ 2)) z := by
  have h := ((hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).pow 2)).sqrt
    (one_sub_sq_pos_of_mem_unitInterval hz).ne'
  change HasDerivAt (fun x : ℝ ↦ Real.sqrt (1 - x ^ 2))
    ((0 - 2 * z ^ (2 - 1) * 1) / (2 * Real.sqrt (1 - z ^ 2))) z at h
  convert h using 1
  ring

theorem hasDerivAt_lensAzimuth {c z b : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram z b c) :
    HasDerivAt (fun x : ℝ ↦ Real.arccos (latitudeCapThreshold b c x))
      ((c - b * z) / ((1 - z ^ 2) * Real.sqrt (lensGram z b c))) z := by
  have hc' := one_sub_sq_pos_of_mem_unitInterval hc
  have hz' := one_sub_sq_pos_of_mem_unitInterval hz
  have hc0 : Real.sqrt (1 - c ^ 2) ≠ 0 := (Real.sqrt_pos.2 hc').ne'
  have hz0 : Real.sqrt (1 - z ^ 2) ≠ 0 := (Real.sqrt_pos.2 hz').ne'
  have hD0 : Real.sqrt (lensGram z b c) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hq := ((hasDerivAt_const z b).sub ((hasDerivAt_id z).const_mul c)).div
    ((hasDerivAt_sqrt_one_sub_sq hz).const_mul (Real.sqrt (1 - c ^ 2))) (mul_ne_zero hc0 hz0)
  have hmem := latitudeCapThreshold_mem_Ioo hc hz hD
  have h := (Real.hasDerivAt_arccos (ne_of_gt hmem.1) (ne_of_lt hmem.2)).comp z hq
  change HasDerivAt (fun x : ℝ ↦ Real.arccos (latitudeCapThreshold b c x)) _ z at h
  convert h using 1
  simp only [Pi.sub_apply, id_eq, mul_one, zero_sub]
  rw [sqrt_lensGram_threshold hc hz hD]
  field_simp
  rw [Real.sq_sqrt hz'.le]
  ring

theorem lensGram_swap (a b c : ℝ) : lensGram b a c = lensGram a b c := by
  unfold lensGram
  ring

theorem lensGram_swap_last (a b c : ℝ) : lensGram a c b = lensGram a b c := by
  unfold lensGram
  ring

theorem hasDerivAt_lensOtherAzimuth {c z b : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram z b c) :
    HasDerivAt (fun x : ℝ ↦ Real.arccos (latitudeCapThreshold x c b))
      (-1 / Real.sqrt (lensGram z b c)) z := by
  have hc0 : Real.sqrt (1 - c ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hc)).ne'
  have hb0 : Real.sqrt (1 - b ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hb)).ne'
  have hD0 : Real.sqrt (lensGram z b c) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hD' : 0 < lensGram b z c := by rwa [lensGram_swap]
  have hmem := latitudeCapThreshold_mem_Ioo hc hb hD'
  have hq := ((hasDerivAt_id z).sub_const (c * b)).div_const
    (Real.sqrt (1 - c ^ 2) * Real.sqrt (1 - b ^ 2))
  have h := (Real.hasDerivAt_arccos (ne_of_gt hmem.1) (ne_of_lt hmem.2)).comp z hq
  change HasDerivAt (fun x : ℝ ↦ Real.arccos (latitudeCapThreshold x c b)) _ z at h
  convert h using 1
  rw [sqrt_lensGram_threshold hc hb hD', lensGram_swap]
  field_simp

theorem hasDerivAt_sqrt_lensGram {a b c : ℝ} (hD : 0 < lensGram a b c) :
    HasDerivAt (fun x : ℝ ↦ Real.sqrt (lensGram x b c))
      ((b * c - a) / Real.sqrt (lensGram a b c)) a := by
  have h : HasDerivAt (fun x : ℝ ↦ lensGram x b c) (2 * (b * c - a)) a := by
    have hh := ((((hasDerivAt_const a (1 : ℝ)).sub ((hasDerivAt_id a).pow 2)).sub_const
      (b ^ 2)).sub_const (c ^ 2)).add ((((hasDerivAt_id a).const_mul 2).mul_const b).mul_const c)
    convert hh using 1
    · ext x
      simp only [lensGram, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  convert h.sqrt hD.ne' using 1
  ring

theorem continuousAt_latitudeCapThreshold {b c z : ℝ}
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun x : ℝ ↦ latitudeCapThreshold b c x) z := by
  have hc0 := (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hc)).ne'
  have hz0 := (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval hz)).ne'
  unfold latitudeCapThreshold
  exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div
    (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.sub (continuousAt_id.pow 2)))) (mul_ne_zero hc0 hz0)

theorem continuous_lensOtherThreshold (b c : ℝ) :
    Continuous (fun x : ℝ ↦ latitudeCapThreshold x c b) := by
  unfold latitudeCapThreshold
  fun_prop

theorem continuousAt_lensAreaExpression {a b c : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) (hc : c ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun x : ℝ ↦ lensAreaExpression x b c) a := by
  have hα := Real.continuous_arccos.continuousAt.comp (continuousAt_latitudeCapThreshold hc ha (b := b))
  have hφ := Real.continuous_arccos.continuousAt.comp (continuousAt_latitudeCapThreshold hb ha (b := c))
  have hβ := (Real.continuous_arccos.comp (continuous_lensOtherThreshold b c)).continuousAt (x := a)
  unfold lensAreaExpression
  fun_prop

theorem continuousAt_lensMomentExpression {a b c : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun x : ℝ ↦ lensMomentExpression x b c) a := by
  have hα := Real.continuous_arccos.continuousAt.comp (continuousAt_latitudeCapThreshold hc ha (b := b))
  have hβ := (Real.continuous_arccos.comp (continuous_lensOtherThreshold b c)).continuousAt (x := a)
  unfold lensMomentExpression lensGram
  fun_prop

theorem hasDerivAt_lensAreaExpression {a b c : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) (hc : c ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram a b c) :
    HasDerivAt (fun x : ℝ ↦ lensAreaExpression x b c)
      (-(2 * Real.arccos (latitudeCapThreshold b c a))) a := by
  have hα := hasDerivAt_lensAzimuth hc ha hD
  have hβ := hasDerivAt_lensOtherAzimuth hc hb hD
  have hD' : 0 < lensGram a c b := by rwa [lensGram_swap_last]
  have hφ := hasDerivAt_lensAzimuth hb ha hD'
  rw [lensGram_swap_last] at hφ
  have h := (((hasDerivAt_const a (2 * Real.pi)).sub (hφ.const_mul 2)).sub
    (((hasDerivAt_id a).mul hα).const_mul 2)).sub (hβ.const_mul (2 * b))
  have ha0 := (one_sub_sq_pos_of_mem_unitInterval ha).ne'
  have hD0 := (Real.sqrt_pos.2 hD).ne'
  convert h using 1
  · ext x
    simp only [lensAreaExpression, Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq]
    field_simp
    ring

theorem hasDerivAt_lensMomentExpression {a b c : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) (hc : c ∈ Ioo (-1 : ℝ) 1) (hD : 0 < lensGram a b c) :
    HasDerivAt (fun x : ℝ ↦ lensMomentExpression x b c)
      (-(2 * Real.arccos (latitudeCapThreshold b c a) * a)) a := by
  have hα := hasDerivAt_lensAzimuth hc ha hD
  have hβ := hasDerivAt_lensOtherAzimuth hc hb hD
  have hΔ := hasDerivAt_sqrt_lensGram hD
  have h := ((((hasDerivAt_const a (1 : ℝ)).sub ((hasDerivAt_id a).pow 2)).mul hα).add
    (hβ.const_mul ((1 - b ^ 2) * c))).sub (hΔ.const_mul b)
  have ha0 := (one_sub_sq_pos_of_mem_unitInterval ha).ne'
  have hD0 := (Real.sqrt_pos.2 hD).ne'
  convert h using 1
  · ext x
    simp only [lensMomentExpression, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

end BlaschkeLebesgue
