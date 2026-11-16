module

public import BlaschkeLebesgue.CompletionAlgebra

/-!
# Safe scalar bounds for the common-normal rectangle

These are the exact radical expressions in equations (eta) and (T). The
hypotheses are the two coupled sums of actual edge deficits. Connecting the
rectangle to the clipped circular edges remains a separate geometric step.
-/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Completion

def obliquity (a b : ℝ) : ℝ := b / (2 * (1 - a))
def midpointError (a b : ℝ) : ℝ :=
  b / (4 * Real.sqrt (1 - a) * Real.sqrt (1 - obliquity a b ^ 2) *
    Real.sqrt (1 / 8 - (a + b) / 16))
def arcCos (a b : ℝ) : ℝ := Real.sqrt (4 / (3 * (2 - a - b)))
def arcSin (a b : ℝ) : ℝ := Real.sqrt (1 - arcCos a b ^ 2)
def rectangleRadius (a b : ℝ) : ℝ :=
  (arcSin a b * Real.sqrt (1 - midpointError a b ^ 2) -
    arcCos a b * midpointError a b) /
  (arcCos a b * Real.sqrt (1 - midpointError a b ^ 2) +
    arcSin a b * midpointError a b)

variable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)

include ha hb hab

theorem obliquity_bounds : 0 ≤ obliquity a b ∧ obliquity a b ≤ 1 / 25 := by
  have hden : 0 < 2 * (1 - a) := by linarith
  constructor
  · exact div_nonneg hb hden.le
  · apply (div_le_iff₀ hden).2
    nlinarith

theorem midpointError_bounds : 0 ≤ midpointError a b ∧ midpointError a b < 1 / 16 := by
  have hc := obliquity_bounds ha hb hab
  have h1 : (19 / 20 : ℝ) ≤ Real.sqrt (1 - a) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have h2 : (99 / 100 : ℝ) ≤ Real.sqrt (1 - obliquity a b ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (obliquity a b - 1 / 25)]
  have h3 : (69 / 200 : ℝ) ≤ Real.sqrt (1 / 8 - (a + b) / 16) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hm := mul_le_mul h1 h2 (by norm_num) (Real.sqrt_nonneg _)
  have hm' := mul_le_mul hm h3 (by norm_num)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hden : 32 / 25 < 4 * Real.sqrt (1 - a) *
      Real.sqrt (1 - obliquity a b ^ 2) * Real.sqrt (1 / 8 - (a + b) / 16) := by
    nlinarith
  constructor
  · exact div_nonneg hb (by linarith)
  · apply (div_lt_iff₀ (show 0 < _ by linarith [hden])).2
    linarith

omit ha hb in
theorem arcCos_sq : arcCos a b ^ 2 = 4 / (3 * (2 - a - b)) := by
  exact Real.sq_sqrt (div_nonneg (by norm_num) (by linarith))

theorem arcCos_bounds :
    0 < arcCos a b ∧ 2 / 3 ≤ arcCos a b ^ 2 ∧ arcCos a b ≤ 5 / 6 := by
  have hd : 0 < 3 * (2 - a - b) := by linarith
  have hs := arcCos_sq hab
  have hlow : (2 / 3 : ℝ) ≤ 4 / (3 * (2 - a - b)) := by
    apply (le_div_iff₀ hd).2
    linarith
  have hhigh : 4 / (3 * (2 - a - b)) ≤ (5 / 6 : ℝ) ^ 2 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hn : 0 ≤ arcCos a b := Real.sqrt_nonneg _
  refine ⟨?_, by linarith, ?_⟩ <;> nlinarith

theorem arcSin_sq : arcSin a b ^ 2 = 1 - arcCos a b ^ 2 := by
  have hc := arcCos_bounds ha hb hab
  exact Real.sq_sqrt (by nlinarith [sq_nonneg (arcCos a b - 5 / 6)])

theorem arcSin_bounds : 1 / 2 ≤ arcSin a b ∧ arcSin a b ≤ 3 / 5 := by
  have hc := arcCos_bounds ha hb hab
  have hs := arcSin_sq ha hb hab
  have hn : 0 ≤ arcSin a b := Real.sqrt_nonneg _
  constructor <;> nlinarith [sq_nonneg (arcCos a b - 5 / 6)]

theorem rectangleRadius_denominator_pos :
    0 < arcCos a b * Real.sqrt (1 - midpointError a b ^ 2) +
      arcSin a b * midpointError a b := by
  have he := midpointError_bounds ha hb hab
  have hc := arcCos_bounds ha hb hab
  have hs := arcSin_bounds ha hb hab
  have hr : 0 < Real.sqrt (1 - midpointError a b ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg (midpointError a b - 1 / 16)]
  exact add_pos_of_pos_of_nonneg (mul_pos hc.1 hr) (mul_nonneg (by linarith) he.1)

/-- The uniform bounds (Tbds) hold on the full closed deficit simplex. -/
theorem rectangleRadius_bounds :
    1 / 2 < rectangleRadius a b ∧ rectangleRadius a b ≤ 1 / Real.sqrt 2 ∧
      1 / Real.sqrt 2 < (3 / 4 : ℝ) := by
  have he := midpointError_bounds ha hb hab
  have hc := arcCos_bounds ha hb hab
  have hs := arcSin_bounds ha hb hab
  have hs2 := arcSin_sq ha hb hab
  have hr : (99 / 100 : ℝ) ≤ Real.sqrt (1 - midpointError a b ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (midpointError a b - 1 / 16)]
  have hrpos : 0 < Real.sqrt (1 - midpointError a b ^ 2) := by linarith
  have hd := rectangleRadius_denominator_pos ha hb hab
  have hleft : (1 / 6 : ℝ) ≤ 2 * arcSin a b - arcCos a b := by linarith
  have hright : 2 * arcCos a b + arcSin a b ≤ (34 / 15 : ℝ) := by linarith
  have hleft' := mul_le_mul hleft hr (by norm_num)
    (show 0 ≤ 2 * arcSin a b - arcCos a b by linarith)
  have hright' := mul_le_mul hright he.2.le he.1 (by norm_num : (0 : ℝ) ≤ 34 / 15)
  have hhalf : 1 / 2 < rectangleRadius a b := by
    apply (lt_div_iff₀ hd).2
    nlinarith
  have hratio : rectangleRadius a b ≤ arcSin a b / arcCos a b := by
    apply (div_le_div_iff₀ hd hc.1).2
    have hprod := mul_nonneg he.1
      (add_nonneg (sq_nonneg (arcSin a b)) (sq_nonneg (arcCos a b)))
    nlinarith
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hroot2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hratio' : arcSin a b / arcCos a b ≤ 1 / Real.sqrt 2 := by
    apply (div_le_div_iff₀ hc.1 hroot).2
    nlinarith [sq_nonneg (arcSin a b * Real.sqrt 2 - arcCos a b)]
  refine ⟨hhalf, hratio.trans hratio', ?_⟩
  apply (div_lt_iff₀ hroot).2
  nlinarith [sq_nonneg (Real.sqrt 2 - 4 / 3)]

end BlaschkeLebesgue.Completion
