module

public import BlaschkeLebesgue.RectangleQuadrature
public import BlaschkeLebesgue.CompletionParameterExtension

/-! # A retained certificate cell gives a lower bound on the true clamped density -/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue.Completion

theorem continuous_unitSquareSmoothDensity_of_obliquity {a b : ℝ}
    (hchi : |obliquity a b| < 1) :
    Continuous (fun p : ℝ × ℝ ↦ unitSquareSmoothDensity a b p.1 p.2) := by
  have hW : Continuous (fun p : ℝ × ℝ ↦ squareW a b p.1 p.2) := by
    unfold squareW uniformW averagedW
    fun_prop
  have hW0 (p : ℝ × ℝ) : squareW a b p.1 p.2 ≠ 0 := (uniformW_pos_of_obliquity hchi _ _).ne'
  have hS := hW.sqrt
  have hS0 (p : ℝ × ℝ) : Real.sqrt (squareW a b p.1 p.2) ≠ 0 := (Real.sqrt_pos.2 (uniformW_pos_of_obliquity hchi _ _)).ne'
  have hG : Continuous (fun p : ℝ × ℝ ↦ squareGap a b p.1 p.2) := by
    unfold squareGap
    apply Continuous.sub _ continuous_const
    apply Continuous.div _ hS hS0
    fun_prop
  have hD : Continuous (fun p : ℝ × ℝ ↦ squareDetLower a b p.1 p.2) := by
    unfold squareDetLower
    apply Continuous.sub continuous_const
    apply Continuous.div
    · exact continuous_const.mul hS
    · fun_prop
    · intro p
      positivity
  unfold unitSquareSmoothDensity q
  apply Continuous.div
  · fun_prop
  · exact hW.mul hS
  · exact fun p ↦ mul_ne_zero (hW0 p) (hS0 p)

theorem continuous_unitSquareSmoothDensity {a b : ℝ}
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    Continuous (fun p : ℝ × ℝ ↦ unitSquareSmoothDensity a b p.1 p.2) :=
  continuous_unitSquareSmoothDensity_of_obliquity
    (obliquity_abs_lt_one_of_total_lt_one hb (by linarith))

/-- Every derivative bound in this theorem is an explicit premise for the
future interval/jet checker. The theorem proves its fixed-square integral
conclusion for the actual clamped density, including the midpoint correction
and the positive-part truncation of a cell's lower value. -/
theorem unitSquare_cell_quadrature_lower {a b ms mt h k Ms Mt : ℝ}
    {Hx Hxx Hy Hyy : ℝ × ℝ → ℝ}
    (ha : 0 ≤ a) (hchi : |obliquity a b| < 1) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hcell : Icc (ms - h) (ms + h) ×ˢ Icc (mt - k) (mt + k) ⊆ Icc 0 1 ×ˢ Icc 0 1)
    (hG : ∀ s ∈ Icc (ms - h) (ms + h), ∀ t ∈ Icc (mt - k) (mt + k), 0 ≤ squareGap a b s t)
    (hD : ∀ s ∈ Icc (ms - h) (ms + h), ∀ t ∈ Icc (mt - k) (mt + k), 0 ≤ squareDetLower a b s t)
    (hHx : ∀ s ∈ Icc (ms - h) (ms + h),
      HasDerivAt (fun s ↦ unitSquareSmoothDensity a b s mt) (Hx (s, mt)) s)
    (hHxx : ∀ s ∈ Icc (ms - h) (ms + h), HasDerivAt (fun s ↦ Hx (s, mt)) (Hxx (s, mt)) s)
    (hHy : ∀ s ∈ Icc (ms - h) (ms + h), ∀ t ∈ Icc (mt - k) (mt + k),
      HasDerivAt (fun t ↦ unitSquareSmoothDensity a b s t) (Hy (s, t)) t)
    (hHyy : ∀ s ∈ Icc (ms - h) (ms + h), ∀ t ∈ Icc (mt - k) (mt + k),
      HasDerivAt (fun t ↦ Hy (s, t)) (Hyy (s, t)) t)
    (hMs : ∀ s ∈ Icc (ms - h) (ms + h), -Ms ≤ Hxx (s, mt))
    (hMt : ∀ s ∈ Icc (ms - h) (ms + h), ∀ t ∈ Icc (mt - k) (mt + k), -Mt ≤ Hyy (s, t)) :
    4 * h * k * max (unitSquareSmoothDensity a b ms mt - Ms * h ^ 2 / 6 - Mt * k ^ 2 / 6) 0 ≤
      ∫ s in (ms - h)..(ms + h), ∫ t in (mt - k)..(mt + k), unitSquareDensity a b s t := by
  have heq (s : ℝ) (hs : s ∈ Icc (ms - h) (ms + h)) (t : ℝ) (ht : t ∈ Icc (mt - k) (mt + k)) :
      unitSquareDensity a b s t = unitSquareSmoothDensity a b s t := by
    have hp : (s, t) ∈ Icc 0 1 ×ˢ Icc 0 1 := hcell ⟨hs, ht⟩
    exact unitSquareDensity_eq_smooth_of_obliquity hchi hp.2 (hG s hs t ht) (hD s hs t ht)
  have h0 (s : ℝ) (hs : s ∈ Icc (ms - h) (ms + h)) (t : ℝ) (ht : t ∈ Icc (mt - k) (mt + k)) :
      0 ≤ unitSquareSmoothDensity a b s t := by
    rw [← heq s hs t ht]
    have hp : (s, t) ∈ Icc 0 1 ×ˢ Icc 0 1 := hcell ⟨hs, ht⟩
    exact unitSquareDensity_nonneg_of_obliquity ha hchi hp.1.1 t
  have hquad := rectangle_midpoint_quadrature_posPart hh hk (continuous_unitSquareSmoothDensity_of_obliquity hchi)
    hHx hHxx hHy hHyy hMs hMt h0
  refine hquad.trans_eq ?_
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (show ms - h ≤ ms + h by linarith)] at hs
  dsimp only
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (show mt - k ≤ mt + k by linarith)] at ht
  exact (heq s hs t ht).symm

end BlaschkeLebesgue.Completion
