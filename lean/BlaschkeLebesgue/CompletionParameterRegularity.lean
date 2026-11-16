module

public import BlaschkeLebesgue.CompletionParameterExtension

/-!
# Continuity of the certificate expressions on an enlarged parameter region

The bounds here hold on `a,b >= 0`, `a+b <= 1/10`, which contains every
accepted box. Positivity of the actual denominators supplies continuity in
the parameters, including at the boundary of the geometric triangle.
-/

public noncomputable section

open Set

namespace BlaschkeLebesgue.Completion

variable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1 / 10)

include ha hb hab

theorem extended_obliquity_bounds : 0 ≤ obliquity a b ∧ obliquity a b ≤ 1 / 10 := by
  have hd : 0 < 2 * (1 - a) := by linarith
  unfold obliquity
  exact ⟨div_nonneg hb hd.le, (div_le_iff₀ hd).2 (by linarith)⟩

theorem extended_midpoint_denominator_ge_one :
    1 ≤ 4 * Real.sqrt (1 - a) * Real.sqrt (1 - obliquity a b ^ 2) *
      Real.sqrt (1 / 8 - (a + b) / 16) := by
  have hc := extended_obliquity_bounds ha hb hab
  have h1 : (9 / 10 : ℝ) ≤ Real.sqrt (1 - a) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have h2 : (9 / 10 : ℝ) ≤ Real.sqrt (1 - obliquity a b ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (obliquity a b - 1 / 10)]
  have h3 : (1 / 3 : ℝ) ≤ Real.sqrt (1 / 8 - (a + b) / 16) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have h12 := mul_le_mul h1 h2 (by norm_num) (Real.sqrt_nonneg _)
  have h123 := mul_le_mul h12 h3 (by norm_num)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  nlinarith only [h123]

theorem extended_midpointError_bounds : 0 ≤ midpointError a b ∧ midpointError a b ≤ 1 / 10 := by
  have hd := extended_midpoint_denominator_ge_one ha hb hab
  have hd0 : 0 < 4 * Real.sqrt (1 - a) * Real.sqrt (1 - obliquity a b ^ 2) *
      Real.sqrt (1 / 8 - (a + b) / 16) := by linarith
  unfold midpointError
  exact ⟨div_nonneg hb hd0.le, (div_le_iff₀ hd0).2 (by linarith)⟩

theorem extended_rectangle_denominator_pos :
    0 < arcCos a b * Real.sqrt (1 - midpointError a b ^ 2) +
      arcSin a b * midpointError a b := by
  have he := extended_midpointError_bounds ha hb hab
  have hc : 0 < arcCos a b := Real.sqrt_pos.2 (div_pos (by norm_num) (by linarith))
  have hs : 0 < Real.sqrt (1 - midpointError a b ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg (midpointError a b - 1 / 10)]
  exact add_pos_of_pos_of_nonneg (mul_pos hc hs) (mul_nonneg (Real.sqrt_nonneg _) he.1)

omit ha in
theorem continuousAt_obliquity_parameters : ContinuousAt (fun p : ℝ × ℝ ↦ obliquity p.1 p.2) (a, b) := by
  unfold obliquity
  apply ContinuousAt.div continuous_snd.continuousAt (by fun_prop)
  dsimp only
  linarith

theorem continuousAt_midpointError_parameters : ContinuousAt (fun p : ℝ × ℝ ↦ midpointError p.1 p.2) (a, b) := by
  have hc := continuousAt_obliquity_parameters hb hab
  unfold midpointError
  apply ContinuousAt.div continuous_snd.continuousAt (by fun_prop)
  dsimp only
  linarith [extended_midpoint_denominator_ge_one ha hb hab]

omit ha hb in
theorem continuousAt_arcCos_parameters : ContinuousAt (fun p : ℝ × ℝ ↦ arcCos p.1 p.2) (a, b) := by
  unfold arcCos
  apply ContinuousAt.sqrt
  apply ContinuousAt.div continuousAt_const (by fun_prop)
  dsimp only
  linarith

theorem continuousAt_rectangleRadius_parameters : ContinuousAt (fun p : ℝ × ℝ ↦ rectangleRadius p.1 p.2) (a, b) := by
  have he := continuousAt_midpointError_parameters ha hb hab
  have hc := continuousAt_arcCos_parameters hab
  have hs : ContinuousAt (fun p : ℝ × ℝ ↦ arcSin p.1 p.2) (a, b) := by
    unfold arcSin
    fun_prop
  unfold rectangleRadius
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  exact (extended_rectangle_denominator_pos ha hb hab).ne'

theorem continuousAt_squareW_parameters (s t : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ ↦ squareW p.1 p.2 s t) (a, b) := by
  have hc := continuousAt_obliquity_parameters hb hab
  have hT := continuousAt_rectangleRadius_parameters ha hb hab
  have hcB := extended_obliquity_bounds ha hb hab
  unfold squareW uniformW averagedW
  apply ContinuousAt.add continuousAt_const
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  dsimp only
  nlinarith [sq_nonneg (obliquity a b - 1 / 10)]

theorem continuousAt_squareGap_parameters (s t : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ ↦ squareGap p.1 p.2 s t) (a, b) := by
  have hT := continuousAt_rectangleRadius_parameters ha hb hab
  have hW := continuousAt_squareW_parameters ha hb hab s t
  have hchi := obliquity_abs_lt_one_of_total_lt_one hb (by linarith : a + b < 1)
  have hW0 : Real.sqrt (squareW a b s t) ≠ 0 :=
    (Real.sqrt_pos.2 (uniformW_pos_of_obliquity hchi _ _)).ne'
  unfold squareGap
  apply ContinuousAt.sub _ continuousAt_const
  apply ContinuousAt.div _ hW.sqrt hW0
  unfold edgeRadius separationUpper
  fun_prop

theorem continuousAt_squareDetLower_parameters (s t : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ ↦ squareDetLower p.1 p.2 s t) (a, b) := by
  have hT := continuousAt_rectangleRadius_parameters ha hb hab
  have hW := continuousAt_squareW_parameters ha hb hab s t
  unfold squareDetLower
  apply ContinuousAt.sub continuousAt_const
  apply ContinuousAt.div
  · unfold edgeRadius
    fun_prop
  · fun_prop
  · dsimp only
    positivity

theorem continuousAt_unitSquareDensity_parameters (s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ContinuousAt (fun p : ℝ × ℝ ↦ unitSquareDensity p.1 p.2 s t) (a, b) := by
  have hT := continuousAt_rectangleRadius_parameters ha hb hab
  have hc := continuousAt_obliquity_parameters hb hab
  have hchi := obliquity_abs_lt_one_of_total_lt_one hb (by linarith : a + b < 1)
  have hW : ContinuousAt (fun p : ℝ × ℝ ↦ squareW p.1 p.2 s t) (a, b) :=
    continuousAt_squareW_parameters ha hb hab s t
  have hG := continuousAt_squareGap_parameters ha hb hab s t
  have hD := continuousAt_squareDetLower_parameters ha hb hab s t
  have hW0 := uniformW_pos_of_obliquity hchi (rectangleRadius a b * s) (rectangleRadius a b * s * t)
  have hcont : ContinuousAt (fun p : ℝ × ℝ ↦
      8 * rectangleRadius p.1 p.2 ^ 2 * s * max (squareGap p.1 p.2 s t) 0 *
        q (max (squareDetLower p.1 p.2 s t) 0) / (squareW p.1 p.2 s t * Real.sqrt (squareW p.1 p.2 s t))) (a, b) := by
    apply ContinuousAt.div
    · unfold q
      fun_prop
    · fun_prop
    · exact mul_ne_zero hW0.ne' (Real.sqrt_pos.2 hW0).ne'
  apply hcont.congr_of_eventuallyEq
  have hn : ∀ᶠ p in nhds (a, b), |obliquity p.1 p.2| < 1 :=
    hc.abs.eventually (eventually_lt_nhds hchi)
  filter_upwards [hn] with p hp
  exact unitSquareDensity_eq_clamped_of_obliquity hp ht

end BlaschkeLebesgue.Completion
