module

public import BlaschkeLebesgue.CompletionFixedSquare

/-!
# The fixed-square integral outside the geometric parameter triangle

Some certificate boxes cross `a+b=2/25`, including boxes whose centers are
outside that triangle. Their arithmetic applies to the fixed-square integral
defined here. Equality to the geometric scalar `F` is asserted only on its
proved domain. Continuity and nonnegativity in the integration coordinates
need only the explicit obliquity condition.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue.Completion

def fixedSquareIntegral (a b : ℝ) : ℝ :=
  ∫ s in 0..1, ∫ t in 0..1, unitSquareDensity a b s t

theorem F_eq_fixedSquareIntegral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    F a b = fixedSquareIntegral a b := F_eq_unitSquare ha hb hab

theorem obliquity_abs_lt_one_of_total_lt_one {a b : ℝ}
    (hb : 0 ≤ b) (hab : a + b < 1) : |obliquity a b| < 1 := by
  have hd : 0 < 2 * (1 - a) := by linarith
  unfold obliquity
  rw [abs_of_nonneg (div_nonneg hb hd.le), div_lt_iff₀ hd]
  linarith

theorem continuous_unitSquareDensity_of_obliquity {a b : ℝ} (hchi : |obliquity a b| < 1) :
    Continuous (fun p : ℝ × ℝ ↦ unitSquareDensity a b p.1 p.2) := by
  have h := (continuous_uniformDensity_of_obliquity hchi).comp
    (show Continuous (fun p : ℝ × ℝ ↦ (rectangleRadius a b * p.1, rectangleRadius a b * p.1 * p.2)) by fun_prop)
  unfold unitSquareDensity
  exact (continuous_const.mul continuous_fst).mul h

theorem unitSquareDensity_nonneg_of_obliquity {a b s : ℝ} (ha : 0 ≤ a) (hchi : |obliquity a b| < 1)
    (hs : 0 ≤ s) (t : ℝ) : 0 ≤ unitSquareDensity a b s t :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hs)
    (uniformDensity_nonneg_of_obliquity ha hchi _ _)

theorem fixedSquareIntegral_nonneg {a b : ℝ} (ha : 0 ≤ a) (hchi : |obliquity a b| < 1) :
    0 ≤ fixedSquareIntegral a b := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s hs
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (unitSquareDensity_nonneg_of_obliquity ha hchi hs.1)

theorem uniformDensity_eq_ordered_squares {a b x y : ℝ} (hchi : |obliquity a b| < 1)
    (hxy : y ^ 2 ≤ x ^ 2) :
    uniformDensity a b x y =
      max ((edgeRadius 0 * Real.sqrt (1 + x ^ 2) + edgeRadius a * Real.sqrt (1 + y ^ 2) -
        separationUpper a b) / Real.sqrt (uniformW a b x y) - 1) 0 *
      q (max (1 - edgeRadius a * Real.sqrt (uniformW a b x y) / Real.sqrt (1 + y ^ 2)) 0) /
        (uniformW a b x y * Real.sqrt (uniformW a b x y)) := by
  have hd : Real.sqrt (uniformW a b x y) ^ 3 = uniformW a b x y * Real.sqrt (uniformW a b x y) := by
    rw [pow_succ, Real.sq_sqrt (uniformW_pos_of_obliquity hchi x y).le]
  unfold uniformDensity phi allocationNumerator determinantFactor
  rw [max_eq_left hxy, min_eq_right hxy, hd]
  have hm : edgeRadius a / Real.sqrt (1 + y ^ 2) * Real.sqrt (uniformW a b x y) =
      edgeRadius a * Real.sqrt (uniformW a b x y) / Real.sqrt (1 + y ^ 2) := by ring
  rw [hm]

theorem unitSquareDensity_eq_clamped_of_obliquity {a b s t : ℝ} (hchi : |obliquity a b| < 1)
    (ht : t ∈ Icc 0 1) :
    unitSquareDensity a b s t =
      8 * rectangleRadius a b ^ 2 * s * max (squareGap a b s t) 0 * q (max (squareDetLower a b s t) 0) /
        (squareW a b s t * Real.sqrt (squareW a b s t)) := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.2, mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have hxy : (rectangleRadius a b * s * t) ^ 2 ≤ (rectangleRadius a b * s) ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) ht2
  unfold unitSquareDensity
  rw [uniformDensity_eq_ordered_squares hchi hxy]
  dsimp only [squareGap, squareDetLower, squareW]
  ring

theorem unitSquareDensity_eq_smooth_of_obliquity {a b s t : ℝ} (hchi : |obliquity a b| < 1)
    (ht : t ∈ Icc 0 1) (hG : 0 ≤ squareGap a b s t) (hD : 0 ≤ squareDetLower a b s t) :
    unitSquareDensity a b s t = unitSquareSmoothDensity a b s t := by
  rw [unitSquareDensity_eq_clamped_of_obliquity hchi ht, max_eq_left hG, max_eq_left hD]
  rfl

end BlaschkeLebesgue.Completion
