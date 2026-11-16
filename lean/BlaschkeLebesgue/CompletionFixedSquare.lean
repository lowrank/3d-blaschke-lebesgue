module

public import BlaschkeLebesgue.SymmetricSquareIntegral

/-!
# The completion certificate's fixed-square integrand

The true scalar integral is exactly the integral on the unit square used by
the numerical certificate. The clamped factors remain present; their removal
is justified only on cells where both factors are nonnegative.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue.Completion

theorem uniformDensity_swap (a b x y : ℝ) : uniformDensity a b x y = uniformDensity a b y x := by
  simp only [uniformDensity, allocationNumerator, determinantFactor, uniformW, averagedW,
    max_comm (x ^ 2) (y ^ 2), min_comm (x ^ 2) (y ^ 2), add_comm (x ^ 2) (y ^ 2)]

def unitSquareDensity (a b s t : ℝ) : ℝ :=
  8 * rectangleRadius a b ^ 2 * s *
    uniformDensity a b (rectangleRadius a b * s) (rectangleRadius a b * s * t)

theorem F_eq_unitSquare {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    F a b = ∫ s in 0..1, ∫ t in 0..1, unitSquareDensity a b s t := by
  have hT : 0 ≤ rectangleRadius a b := by linarith [(rectangleRadius_bounds ha hb hab).1]
  rw [F_eq_intervalIntegral ha hb hab,
    intervalIntegral_square_eq_two_triangle (continuous_uniformDensity ha hb hab)
      (uniformDensity_swap a b) hT,
    intervalIntegral_triangle_unitSquare (fun p : ℝ × ℝ ↦ uniformDensity a b p.1 p.2)]
  simp only [unitSquareDensity, mul_assoc, intervalIntegral.integral_const_mul]
  ring

theorem continuous_unitSquareDensity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    Continuous (fun p : ℝ × ℝ ↦ unitSquareDensity a b p.1 p.2) := by
  have h := (continuous_uniformDensity ha hb hab).comp
    (show Continuous (fun p : ℝ × ℝ ↦ (rectangleRadius a b * p.1, rectangleRadius a b * p.1 * p.2)) by fun_prop)
  unfold unitSquareDensity
  exact ((continuous_const.mul continuous_fst).mul h)

theorem integrableOn_unitSquareDensity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    IntegrableOn (fun p : ℝ × ℝ ↦ unitSquareDensity a b p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) :=
  (continuous_unitSquareDensity ha hb hab).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem unitSquareDensity_nonneg {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)
    (hs : 0 ≤ s) (t : ℝ) : 0 ≤ unitSquareDensity a b s t :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hs)
    (uniformDensity_nonneg ha hb hab _ _)

theorem uniformDensity_ordered {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)
    (hy : 0 ≤ y) (hyx : y ≤ x) :
    uniformDensity a b x y =
      max ((edgeRadius 0 * Real.sqrt (1 + x ^ 2) + edgeRadius a * Real.sqrt (1 + y ^ 2) -
        separationUpper a b) / Real.sqrt (uniformW a b x y) - 1) 0 *
      q (max (1 - edgeRadius a * Real.sqrt (uniformW a b x y) / Real.sqrt (1 + y ^ 2)) 0) /
        (uniformW a b x y * Real.sqrt (uniformW a b x y)) := by
  have hsq := (sq_le_sq₀ hy (hy.trans hyx)).2 hyx
  have hd : Real.sqrt (uniformW a b x y) ^ 3 = uniformW a b x y * Real.sqrt (uniformW a b x y) := by
    rw [pow_succ, Real.sq_sqrt (uniformW_pos ha hb hab x y).le]
  unfold uniformDensity phi allocationNumerator determinantFactor
  rw [max_eq_left hsq, min_eq_right hsq, hd]
  have hm : edgeRadius a / Real.sqrt (1 + y ^ 2) * Real.sqrt (uniformW a b x y) =
      edgeRadius a * Real.sqrt (uniformW a b x y) / Real.sqrt (1 + y ^ 2) := by ring
  rw [hm]

def squareW (a b s t : ℝ) : ℝ :=
  uniformW a b (rectangleRadius a b * s) (rectangleRadius a b * s * t)

def squareGap (a b s t : ℝ) : ℝ :=
  (edgeRadius 0 * Real.sqrt (1 + (rectangleRadius a b * s) ^ 2) +
    edgeRadius a * Real.sqrt (1 + (rectangleRadius a b * s * t) ^ 2) - separationUpper a b) /
    Real.sqrt (squareW a b s t) - 1

def squareDetLower (a b s t : ℝ) : ℝ :=
  1 - edgeRadius a * Real.sqrt (squareW a b s t) / Real.sqrt (1 + (rectangleRadius a b * s * t) ^ 2)

def unitSquareSmoothDensity (a b s t : ℝ) : ℝ :=
  8 * rectangleRadius a b ^ 2 * s * squareGap a b s t * q (squareDetLower a b s t) /
    (squareW a b s t * Real.sqrt (squareW a b s t))

theorem unitSquareDensity_eq_clamped {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)
    (hs : 0 ≤ s) (ht : t ∈ Icc 0 1) :
    unitSquareDensity a b s t =
      8 * rectangleRadius a b ^ 2 * s * max (squareGap a b s t) 0 * q (max (squareDetLower a b s t) 0) /
        (squareW a b s t * Real.sqrt (squareW a b s t)) := by
  have hT : 0 ≤ rectangleRadius a b := by linarith [(rectangleRadius_bounds ha hb hab).1]
  have hx := mul_nonneg hT hs
  have hy := mul_nonneg hx ht.1
  have hyx := mul_le_of_le_one_right hx ht.2
  unfold unitSquareDensity
  rw [uniformDensity_ordered ha hb hab hy hyx]
  dsimp only [squareGap, squareDetLower, squareW]
  ring

theorem unitSquareDensity_eq_smooth {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)
    (hs : 0 ≤ s) (ht : t ∈ Icc 0 1) (hG : 0 ≤ squareGap a b s t) (hD : 0 ≤ squareDetLower a b s t) :
    unitSquareDensity a b s t = unitSquareSmoothDensity a b s t := by
  rw [unitSquareDensity_eq_clamped ha hb hab hs ht, max_eq_left hG, max_eq_left hD]
  rfl

theorem unitSquareDensity_eq_zero_of_inactive {a b s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) (hs : 0 ≤ s) (ht : t ∈ Icc 0 1)
    (h : squareGap a b s t ≤ 0 ∨ squareDetLower a b s t ≤ 0) : unitSquareDensity a b s t = 0 := by
  rw [unitSquareDensity_eq_clamped ha hb hab hs ht]
  rcases h with h | h
  · rw [max_eq_right h]
    ring
  · rw [max_eq_right h, q]
    ring

end BlaschkeLebesgue.Completion
