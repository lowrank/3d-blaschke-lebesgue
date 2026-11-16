module

public import BlaschkeLebesgue.CutoffMeanValue
public import BlaschkeLebesgue.CompletionParameterRegularity
public import BlaschkeLebesgue.UniformGridBounds

/-!
# Parameter variation of the actual clamped completion integral

Smooth derivative enclosures give signed secant bounds, even across either
positive-part boundary. The bounds can be integrated on a finite grid without
assuming that the clamped density is differentiable at its cutoffs.
-/

public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BlaschkeLebesgue.Completion

theorem continuousOn_certificate_curve {A B : ℝ → ℝ} {l r s t : ℝ}
    (hA : ContinuousOn A (Icc l r)) (hB : ContinuousOn B (Icc l r))
    (hdom : ∀ z ∈ Icc l r, 0 ≤ A z ∧ 0 ≤ B z ∧ A z + B z ≤ 1 / 10) (ht : t ∈ Icc 0 1) :
    ContinuousOn (fun z ↦ unitSquareDensity (A z) (B z) s t) (Icc l r) ∧
    ContinuousOn (fun z ↦ squareGap (A z) (B z) s t) (Icc l r) ∧
    ContinuousOn (fun z ↦ squareDetLower (A z) (B z) s t) (Icc l r) := by
  have hAB := hA.prodMk hB
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (continuousAt_unitSquareDensity_parameters (hdom z hz).1 (hdom z hz).2.1
      (hdom z hz).2.2 s ht).comp_continuousWithinAt (f := fun z ↦ (A z, B z)) (hAB z hz)
  · intro z hz
    exact (continuousAt_squareGap_parameters (hdom z hz).1 (hdom z hz).2.1
      (hdom z hz).2.2 s t).comp_continuousWithinAt (f := fun z ↦ (A z, B z)) (hAB z hz)
  · intro z hz
    exact (continuousAt_squareDetLower_parameters (hdom z hz).1 (hdom z hz).2.1
      (hdom z hz).2.2 s t).comp_continuousWithinAt (f := fun z ↦ (A z, B z)) (hAB z hz)

/-- This is the certificate's boundary-cell rule. The smooth derivative and
its enclosure remain explicit obligations for the interval/jet checker. -/
theorem unitSquareDensity_curve_bounds_hullzero {A B P' : ℝ → ℝ} {l r s t m M : ℝ}
    (hlr : l ≤ r) (hA : ContinuousOn A (Icc l r)) (hB : ContinuousOn B (Icc l r))
    (hdom : ∀ z ∈ Icc l r, 0 ≤ A z ∧ 0 ≤ B z ∧ A z + B z ≤ 1 / 10) (ht : t ∈ Icc 0 1)
    (hd : ∀ z ∈ Ioo l r, HasDerivAt (fun z ↦ unitSquareSmoothDensity (A z) (B z) s t) (P' z) z)
    (hbnd : ∀ z ∈ Ioo l r, 0 < squareGap (A z) (B z) s t → 0 < squareDetLower (A z) (B z) s t →
      m ≤ P' z ∧ P' z ≤ M) :
    min 0 m * (r - l) ≤ unitSquareDensity (A r) (B r) s t - unitSquareDensity (A l) (B l) s t ∧
    unitSquareDensity (A r) (B r) s t - unitSquareDensity (A l) (B l) s t ≤ max 0 M * (r - l) := by
  have hc := continuousOn_certificate_curve hA hB hdom ht (s := s)
  have hchi (z : ℝ) (hz : z ∈ Icc l r) : |obliquity (A z) (B z)| < 1 :=
    obliquity_abs_lt_one_of_total_lt_one (hdom z hz).2.1 (by linarith [(hdom z hz).2.2])
  exact image_sub_bounds_of_cutoff_hullzero hlr hc.1 hc.2.1 hc.2.2
    (fun z hz h ↦ unitSquareDensity_eq_zero_of_inactive_of_obliquity (hchi z hz) ht h)
    (fun z hz hG hD ↦ unitSquareDensity_eq_smooth_of_obliquity (hchi z hz) ht hG.le hD.le) hd hbnd

/-- Strictly active cells use the original signed interval, without adjoining
zero. This preserves the sharper enclosure used by the verifier. -/
theorem unitSquareDensity_curve_bounds_of_positive {A B P' : ℝ → ℝ} {l r s t m M : ℝ}
    (hlr : l ≤ r) (hA : ContinuousOn A (Icc l r)) (hB : ContinuousOn B (Icc l r))
    (hdom : ∀ z ∈ Icc l r, 0 ≤ A z ∧ 0 ≤ B z ∧ A z + B z ≤ 1 / 10) (ht : t ∈ Icc 0 1)
    (hd : ∀ z ∈ Ioo l r, HasDerivAt (fun z ↦ unitSquareSmoothDensity (A z) (B z) s t) (P' z) z)
    (hpos : ∀ z ∈ Ioo l r, 0 < squareGap (A z) (B z) s t ∧ 0 < squareDetLower (A z) (B z) s t)
    (hbnd : ∀ z ∈ Ioo l r, m ≤ P' z ∧ P' z ≤ M) :
    m * (r - l) ≤ unitSquareDensity (A r) (B r) s t - unitSquareDensity (A l) (B l) s t ∧
    unitSquareDensity (A r) (B r) s t - unitSquareDensity (A l) (B l) s t ≤ M * (r - l) := by
  have hc := continuousOn_certificate_curve hA hB hdom ht (s := s)
  have hchi (z : ℝ) (hz : z ∈ Icc l r) : |obliquity (A z) (B z)| < 1 :=
    obliquity_abs_lt_one_of_total_lt_one (hdom z hz).2.1 (by linarith [(hdom z hz).2.2])
  exact image_sub_bounds_of_cutoff_positive hlr hc.1 hc.2.1 hc.2.2
    (fun z hz hG hD ↦ unitSquareDensity_eq_smooth_of_obliquity (hchi z hz) ht hG.le hD.le) hd hpos hbnd

/-- Integrate the signed bounds certified on the `n*n` integration cells.
The hypotheses are pointwise secant bounds, so no derivative of an integral
or measure-zero activation-boundary claim is used. -/
theorem fixedSquareIntegral_sub_bounds {a₀ b₀ a₁ b₁ delta : ℝ}
    (hc₀ : |obliquity a₀ b₀| < 1) (hc₁ : |obliquity a₁ b₁| < 1)
    {n : ℕ} (hn : 0 < n) (lower upper : ℕ → ℕ → ℝ)
    (hbnd : ∀ i < n, ∀ j < n, ∀ p ∈ UniformGrid.cell n i j,
      lower i j * delta ≤ unitSquareDensity a₁ b₁ p.1 p.2 - unitSquareDensity a₀ b₀ p.1 p.2 ∧
      unitSquareDensity a₁ b₁ p.1 p.2 - unitSquareDensity a₀ b₀ p.1 p.2 ≤ upper i j * delta) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, UniformGrid.area n * lower i j) * delta ≤
      fixedSquareIntegral a₁ b₁ - fixedSquareIntegral a₀ b₀ ∧
    fixedSquareIntegral a₁ b₁ - fixedSquareIntegral a₀ b₀ ≤
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, UniformGrid.area n * upper i j) * delta :=
  UniformGrid.integral_sub_bounds (continuous_unitSquareDensity_of_obliquity hc₁)
    (continuous_unitSquareDensity_of_obliquity hc₀) hn lower upper delta hbnd

end BlaschkeLebesgue.Completion
