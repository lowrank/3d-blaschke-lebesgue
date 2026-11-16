module

public import Mathlib.Tactic

/-!
# Algebraic inequalities used by the antipodal completion estimate

The matrix inputs below are the diagonal entries and determinant of a positive
semidefinite contraction in a basis diagonalizing the first curvature matrix.
The geometric curvature and variation identities are separate obligations.
-/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Completion

def psi (s : ℝ) : ℝ := 31 / 32 * s + min (1 / 32) (s / 2)
def q (s : ℝ) : ℝ := 47 / 32 * s - 2 * s ^ 2

theorem psi_monotone : Monotone psi := by
  intro a b hab
  unfold psi
  exact add_le_add (mul_le_mul_of_nonneg_left hab (by norm_num))
    (min_le_min_left _ (by linarith))

/-- The polynomial minorant (`eq:qpoly` in the manuscript). -/
theorem q_le_psi (s : ℝ) : q s ≤ psi s := by
  unfold q psi
  rw [min_def]
  split_ifs
  · nlinarith [sq_nonneg (s - 1 / 8)]
  · nlinarith [sq_nonneg s]

theorem q_nonneg {s : ℝ} (hs : 0 ≤ s) (hupper : s ≤ 1 / 5) : 0 ≤ q s := by
  unfold q
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hupper)]

theorem q_monotoneOn : MonotoneOn q (Set.Icc 0 (1 / 5)) := by
  intro a ha b hb hab
  unfold q
  have hfactor : 0 ≤ 47 / 32 - 2 * (a + b) := by linarith [ha.2, hb.2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) hfactor]

/-- The variable curvature contribution is bounded below without choosing its orientation. -/
theorem contraction_contribution_lower {a₁ a₂ u v d : ℝ}
    (ha₁ : 0 ≤ a₁) (horder : a₁ ≤ a₂) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hd : 0 ≤ d) (hcomp : u + v - 1 ≤ d) :
    min 0 (a₁ / 2 - 1 / 32) ≤
      d + (a₂ / 2 - 1 / 32) * u + (a₁ / 2 - 1 / 32) * v := by
  by_cases hc : 0 ≤ a₁ / 2 - 1 / 32
  · rw [min_eq_left hc]
    have hc₂ : 0 ≤ a₂ / 2 - 1 / 32 := by linarith
    nlinarith [mul_nonneg hc₂ hu, mul_nonneg hc hv]
  · rw [min_eq_right (le_of_not_ge hc)]
    have hdiff := mul_nonneg (show 0 ≤ a₂ / 2 - a₁ / 2 by linarith) hu
    by_cases hsum : u + v ≤ 1
    · have h := mul_nonneg (neg_nonneg.mpr (le_of_not_ge hc)) (sub_nonneg.mpr hsum)
      nlinarith
    · have h := mul_nonneg (show 0 ≤ 1 + (a₁ / 2 - 1 / 32) by linarith)
        (show 0 ≤ u + v - 1 by linarith)
      nlinarith

/-- The pointwise lower weight in the proof of the weighted completion proposition. -/
theorem curvature_weight_lower {a₁ a₂ u v d : ℝ}
    (ha₁ : 0 ≤ a₁) (horder : a₁ ≤ a₂) (ha₂ : a₂ ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 ≤ d) (hcomp : u + v - 1 ≤ d) :
    psi (a₁ * a₂) - 1 / 16 ≤ a₁ * a₂ - (a₁ + a₂) / 32 +
      d + (a₂ / 2 - 1 / 32) * u + (a₁ / 2 - 1 / 32) * v := by
  have htrace : a₁ + a₂ ≤ 1 + a₁ * a₂ := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - a₁ by linarith) (sub_nonneg.mpr ha₂)]
  have hprod : a₁ * a₂ ≤ a₁ := by nlinarith [mul_nonneg ha₁ (sub_nonneg.mpr ha₂)]
  have hmin := min_le_min_left (0 : ℝ)
    (show a₁ * a₂ / 2 - 1 / 32 ≤ a₁ / 2 - 1 / 32 by linarith)
  have hc := contraction_contribution_lower ha₁ horder hu hv hd hcomp
  have hid : psi (a₁ * a₂) - 1 / 16 =
      a₁ * a₂ - (1 + a₁ * a₂) / 32 + min 0 (a₁ * a₂ / 2 - 1 / 32) := by
    unfold psi
    rw [min_def, min_def]
    split_ifs <;> linarith
  rw [hid]
  linarith

def B₁ (u v : ℝ) : ℝ := 6 - 15 / 4 * (u + v) + 2 * u * v
def B₂ (u v : ℝ) : ℝ :=
  6 - 15 * u / 4 - 15 * v / 2 + 4 * u * v + 2 * v ^ 2 - 3 / 4 * u * v ^ 2

/-- The first polynomial bound used in the convexity calculation. -/
theorem half_le_B₁ {u v : ℝ} (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    1 / 2 ≤ B₁ u v := by
  unfold B₁
  have h := mul_nonneg (sub_nonneg.mpr hu.2)
    (show 0 ≤ 15 / 4 - 2 * v by linarith [hv.2])
  nlinarith [hv.2]

/-- The second polynomial bound used in the convexity calculation. -/
theorem convexity_remainder {u v : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (4 / 5) 1) : 7 / 40 ≤ B₁ u v / 2 - B₂ u v := by
  have hsecant := mul_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr hv.2)
  have hc : 15 / 8 - 3 * v + 3 / 4 * v ^ 2 ≤ 0 := by nlinarith
  have h := mul_nonneg (sub_nonneg.mpr hu.2) (neg_nonneg.mpr hc)
  unfold B₁ B₂
  nlinarith

/-- Summing the three affine integral bounds keeps the opposite-edge budgets coupled. -/
theorem sum_affine_bounds {A a₀ a₁ a₂ b₀ b₁ b₂ F₀ F₁ F₂ : ℝ}
    (ha : a₀ + a₁ + a₂ = A) (hb : b₀ + b₁ + b₂ = 2 * A)
    (h₀ : 153 / 100000 - 601 / 100000 * a₀ + 317 / 20000 * b₀ < F₀)
    (h₁ : 153 / 100000 - 601 / 100000 * a₁ + 317 / 20000 * b₁ < F₁)
    (h₂ : 153 / 100000 - 601 / 100000 * a₂ + 317 / 20000 * b₂ < F₂) :
    459 / 100000 + 2569 / 100000 * A < F₀ + F₁ + F₂ := by
  linarith

end BlaschkeLebesgue.Completion
