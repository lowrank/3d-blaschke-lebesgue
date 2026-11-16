module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

/-!
# Algebra and soundness of the radial certificate inequalities

These lemmas justify the tangent majorant and the removal of square roots in the
rational cap tests. They do not assume numerical verifier output. The geometric
integration step leading to the radial master inequality is not asserted here.
-/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Radial

def slope (m t : ℝ) : ℝ := 2 * (t ^ 2 + 3 * m) / (3 * (t ^ 2 + m) ^ 2)

def intercept (m t : ℝ) : ℝ := 2 * t ^ 3 / (t ^ 2 + m) - slope m t * t ^ 3

def gap (m t s : ℝ) : ℝ := slope m t * s ^ 3 + intercept m t -
  2 * s ^ 3 / (s ^ 2 + m)

/-- An algebraic proof of the tangent majorant, avoiding fractional-power derivatives. -/
theorem gap_factorization {m t s : ℝ} (hm : 0 < m) :
    gap m t s = 2 * (s - t) ^ 2 *
      ((t ^ 2 + 3 * m) * s ^ 3 + (2 * t ^ 3 + 6 * m * t) * s ^ 2 +
        4 * m * t ^ 2 * s + 2 * m * t ^ 3) /
      (3 * (t ^ 2 + m) ^ 2 * (s ^ 2 + m)) := by
  have ht : t ^ 2 + m ≠ 0 := ne_of_gt (by positivity)
  have hs : s ^ 2 + m ≠ 0 := ne_of_gt (by positivity)
  unfold gap intercept slope
  field_simp
  ring

theorem gap_nonneg {m t s : ℝ} (hm : 0 < m) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ gap m t s := by
  rw [gap_factorization hm]
  positivity

/-- The scalar expression used to propagate a radial lower bound (`eq:N` in the manuscript). -/
def propagation (m x c s : ℝ) : ℝ :=
  x * (x ^ 2 + m) / ((x ^ 2 + m) * c - Real.sqrt (4 * x ^ 2 - (x ^ 2 + m) ^ 2) * s)

/-- Squared rational tests imply both a positive denominator and the propagation inequality. -/
theorem propagation_test_sound {m x y c s : ℝ}
    (hm : 0 < m) (hx : 0 < x) (hy : 0 < y) (hs : 0 ≤ s)
    (hrad : 0 ≤ 4 * x ^ 2 - (x ^ 2 + m) ^ 2)
    (hlinear : 0 < y * c - x)
    (hsquared : y ^ 2 * (4 * x ^ 2 - (x ^ 2 + m) ^ 2) * s ^ 2 ≤
      (x ^ 2 + m) ^ 2 * (y * c - x) ^ 2) :
    0 < (x ^ 2 + m) * c - Real.sqrt (4 * x ^ 2 - (x ^ 2 + m) ^ 2) * s ∧
      propagation m x c s ≤ y := by
  let T := x ^ 2 + m
  let d := Real.sqrt (4 * x ^ 2 - (x ^ 2 + m) ^ 2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d ^ 2 = 4 * x ^ 2 - (x ^ 2 + m) ^ 2 := Real.sq_sqrt hrad
  have hroot : y * d * s ≤ T * (y * c - x) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simpa only [mul_pow, hd2, T] using hsquared
  have hden : 0 < T * c - d * s := by
    have hproduct : 0 < y * (T * c - d * s) := by
      nlinarith [mul_pos hx hT]
    exact pos_of_mul_pos_right hproduct hy.le
  refine ⟨hden, ?_⟩
  change x * T / (T * c - d * s) ≤ y
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The rational tests in `eq:ztest` imply the negative-cap square-root bound. -/
theorem negative_cap_test_sound {r c s z : ℝ}
    (hsign : 0 ≤ z + r * c)
    (hsquared : 1 - r ^ 2 * s ^ 2 ≤ (z + r * c) ^ 2) :
    -r * c + Real.sqrt (1 - r ^ 2 * s ^ 2) ≤ z := by
  have h := (Real.sqrt_le_iff).2 ⟨hsign, hsquared⟩
  linarith

/-- Stereographic grid coordinates lie on the unit circle exactly. -/
theorem rational_circle (N k : ℝ) (h : N ^ 2 + k ^ 2 ≠ 0) :
    ((N ^ 2 - k ^ 2) / (N ^ 2 + k ^ 2)) ^ 2 +
      (2 * N * k / (N ^ 2 + k ^ 2)) ^ 2 = 1 := by
  field_simp
  ring

/-- Exact elimination of the scalar radial master inequality in the low-radius branch. -/
theorem low_radius_from_master {V : ℝ}
    (hmaster : 2 * Real.pi / 3 - 4 * Real.pi * intercept (16 / 25) (37 / 80) ≤
      (3 * slope (16 / 25) (37 / 80) - 2) * V) :
    (259 / 625 : ℝ) < V := by
  norm_num [slope, intercept] at hmaster
  have hpi := Real.pi_gt_d6
  linarith

end BlaschkeLebesgue.Radial
