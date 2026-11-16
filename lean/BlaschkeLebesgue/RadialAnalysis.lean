module

public import BlaschkeLebesgue.Radial
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Monotonicity of the radial tangent deficit on both sides of its tangent point. -/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Radial

def gapDerivative (m t s : ℝ) : ℝ :=
  2 * s ^ 2 * (s ^ 2 - t ^ 2) * ((t ^ 2 + 3 * m) * s ^ 2 + 3 * m * t ^ 2 + 5 * m ^ 2) /
    ((t ^ 2 + m) ^ 2 * (s ^ 2 + m) ^ 2)

theorem hasDerivAt_gap {m : ℝ} (hm : 0 < m) (t s : ℝ) :
    HasDerivAt (gap m t) (gapDerivative m t s) s := by
  have hs : s ^ 2 + m ≠ 0 := ne_of_gt (by positivity)
  have ht : t ^ 2 + m ≠ 0 := ne_of_gt (by positivity)
  convert ((((hasDerivAt_pow 3 s).const_mul (slope m t)).add_const
      (intercept m t)).sub (((hasDerivAt_pow 3 s).const_mul 2).div
      ((hasDerivAt_pow 2 s).add_const m) hs)) using 1
  · rfl
  · dsimp [gapDerivative, slope]
    field_simp
    ring

theorem gapDerivative_nonneg {m t s : ℝ} (hm : 0 < m) (ht : 0 ≤ t) (hs : t ≤ s) :
    0 ≤ gapDerivative m t s := by
  have hsq : 0 ≤ s ^ 2 - t ^ 2 := by nlinarith
  unfold gapDerivative
  positivity

theorem gapDerivative_nonpos {m t s : ℝ} (hm : 0 < m) (hs : 0 ≤ s) (hst : s ≤ t) :
    gapDerivative m t s ≤ 0 := by
  have hsq : s ^ 2 - t ^ 2 ≤ 0 := by nlinarith
  unfold gapDerivative
  apply div_nonpos_of_nonpos_of_nonneg
  · apply mul_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsq
    · positivity
  · positivity

theorem gap_monotoneOn {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    MonotoneOn (gap m t) (Set.Ici t) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici t)
  · intro s _
    exact (hasDerivAt_gap hm t s).continuousAt.continuousWithinAt
  · intro s _
    exact (hasDerivAt_gap hm t s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hasDerivAt_gap hm t s).deriv]
    exact gapDerivative_nonneg hm ht (interior_subset hs)

theorem gap_antitoneOn {m t : ℝ} (hm : 0 < m) :
    AntitoneOn (gap m t) (Set.Icc 0 t) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
  · intro s _
    exact (hasDerivAt_gap hm t s).continuousAt.continuousWithinAt
  · intro s _
    exact (hasDerivAt_gap hm t s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hasDerivAt_gap hm t s).deriv]
    have hmem : s ∈ Set.Icc 0 t := interior_subset hs
    exact gapDerivative_nonpos hm hmem.1 hmem.2

/-- A uniform rational margin survives a limit; mere strict inequalities would not suffice. -/
theorem strict_bound_of_uniform_limit {v : ℕ → ℝ} {V : ℝ}
    (hv : Filter.Tendsto v Filter.atTop (nhds V))
    (hbound : ∀ n, (4144109 / 10000000 : ℝ) ≤ v n) : (259 / 625 : ℝ) < V := by
  have hle : (4144109 / 10000000 : ℝ) ≤ V :=
    ge_of_tendsto hv (Filter.Eventually.of_forall hbound)
  exact lt_of_lt_of_le (by norm_num) hle

end BlaschkeLebesgue.Radial
