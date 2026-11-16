module

public import BlaschkeLebesgue.CompletionCellQuadrature

/-! # Exact decomposition of the unit-square integral into a finite grid -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BlaschkeLebesgue

theorem intervalIntegrable_inner_of_continuous {H : ℝ × ℝ → ℝ} (hH : Continuous H)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IntervalIntegrable (fun x ↦ ∫ y in c..d, H (x, y)) volume a b := by
  have hi : IntegrableOn H (Ioc a b ×ˢ Ioc c d) (volume.prod volume) :=
    (hH.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hip : Integrable H ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rwa [Measure.prod_restrict]
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
  simpa only [IntegrableOn, intervalIntegral.integral_of_le hcd] using hip.integral_prod_left

namespace UniformGrid

def point (n i : ℕ) : ℝ := (i : ℝ) / n
def midpoint (n i : ℕ) : ℝ := (2 * (i : ℝ) + 1) / (2 * n)
def halfWidth (n : ℕ) : ℝ := 1 / (2 * n)
def area (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2
def cell (n i j : ℕ) : Set (ℝ × ℝ) :=
  Icc (point n i) (point n (i + 1)) ×ˢ Icc (point n j) (point n (j + 1))

theorem point_zero (n : ℕ) : point n 0 = 0 := by simp [point]
theorem point_self {n : ℕ} (hn : 0 < n) : point n n = 1 := by simp [point, ne_of_gt hn]

theorem point_mono (n : ℕ) : Monotone (point n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg n)

theorem halfWidth_nonneg (n : ℕ) : 0 ≤ halfWidth n := by unfold halfWidth; positivity

theorem area_eq_four_halfWidth_sq (n : ℕ) : area n = 4 * halfWidth n * halfWidth n := by
  unfold area halfWidth
  by_cases hn : n = 0
  · simp [hn]
  · field_simp
    ring

theorem point_eq_midpoint_sub {n : ℕ} (hn : 0 < n) (i : ℕ) : point n i = midpoint n i - halfWidth n := by
  unfold point midpoint halfWidth
  field_simp
  ring

theorem point_succ_eq_midpoint_add {n : ℕ} (hn : 0 < n) (i : ℕ) :
    point n (i + 1) = midpoint n i + halfWidth n := by
  unfold point midpoint halfWidth
  push_cast
  field_simp
  ring

theorem cell_subset_unitSquare {n i j : ℕ} (hi : i < n) (hj : j < n) : cell n i j ⊆ Icc 0 1 ×ˢ Icc 0 1 := by
  have hn : 0 < n := Nat.zero_lt_of_lt hi
  have h0i : 0 ≤ point n i := by unfold point; positivity
  have h0j : 0 ≤ point n j := by unfold point; positivity
  have hi1 : point n (i + 1) ≤ 1 := by
    rw [← point_self hn]
    exact point_mono n (Nat.succ_le_of_lt hi)
  have hj1 : point n (j + 1) ≤ 1 := by
    rw [← point_self hn]
    exact point_mono n (Nat.succ_le_of_lt hj)
  exact Set.prod_mono (Icc_subset_Icc h0i hi1) (Icc_subset_Icc h0j hj1)

theorem sum_intervalIntegral {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ Finset.range n, ∫ x in point n i..point n (i + 1), f x) = ∫ x in 0..1, f x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (a := point n) (n := n) (μ := volume)
    (fun i _ ↦ hf.intervalIntegrable (point n i) (point n (i + 1)))
  simpa only [point_zero, point_self hn] using h

theorem integral_unitSquare_eq_sum {H : ℝ × ℝ → ℝ} (hH : Continuous H) {n : ℕ} (hn : 0 < n) :
    (∫ x in 0..1, ∫ y in 0..1, H (x, y)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        ∫ x in point n i..point n (i + 1), ∫ y in point n j..point n (j + 1), H (x, y) := by
  have ho := intervalIntegral.sum_integral_adjacent_intervals (a := point n) (n := n)
    (fun i _ ↦ intervalIntegrable_inner_of_continuous hH (point_mono n (Nat.le_succ i)) (by norm_num : (0 : ℝ) ≤ 1))
  simp only [point_zero, point_self hn] at ho
  rw [← ho]
  apply Finset.sum_congr rfl
  intro i hi
  have hinner (x : ℝ) := sum_intervalIntegral
    (hH.comp (continuous_const.prodMk continuous_id) : Continuous (fun y ↦ H (x, y))) hn
  calc
    _ = ∫ x in point n i..point n (i + 1),
        ∑ j ∈ Finset.range n, ∫ y in point n j..point n (j + 1), H (x, y) :=
      intervalIntegral.integral_congr (fun x _ ↦ (hinner x).symm)
    _ = _ := intervalIntegral.integral_finsetSum
      (fun j _ ↦ intervalIntegrable_inner_of_continuous hH
        (point_mono n (Nat.le_succ i)) (point_mono n (Nat.le_succ j)))

theorem sum_lower_le_unitSquare {H : ℝ × ℝ → ℝ} (hH : Continuous H) {n : ℕ} (hn : 0 < n)
    (lower : ℕ → ℕ → ℝ)
    (hcell : ∀ i < n, ∀ j < n, lower i j ≤
      ∫ x in point n i..point n (i + 1), ∫ y in point n j..point n (j + 1), H (x, y)) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, lower i j) ≤ ∫ x in 0..1, ∫ y in 0..1, H (x, y) := by
  rw [integral_unitSquare_eq_sum hH hn]
  exact Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦
    hcell i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj)

theorem cellIntegral_nonneg {H : ℝ × ℝ → ℝ}
    (hH : ∀ p ∈ Icc 0 1 ×ˢ Icc 0 1, 0 ≤ H p) {n i j : ℕ} (hi : i < n) (hj : j < n) :
    0 ≤ ∫ x in point n i..point n (i + 1), ∫ y in point n j..point n (j + 1), H (x, y) := by
  apply intervalIntegral.integral_nonneg (point_mono n (Nat.le_succ i))
  intro x hx
  apply intervalIntegral.integral_nonneg (point_mono n (Nat.le_succ j))
  intro y hy
  exact hH (x, y) (cell_subset_unitSquare hi hj ⟨hx, hy⟩)

/-- Unretained cells need no derivative estimates: their nonnegative integrals
may be omitted. The retained lower bounds still have to be supplied by the
quadrature theorem and the verified arithmetic. -/
theorem sum_retained_lower_le_unitSquare {H : ℝ × ℝ → ℝ} (hH : Continuous H)
    (hH0 : ∀ p ∈ Icc 0 1 ×ˢ Icc 0 1, 0 ≤ H p) {n : ℕ} (hn : 0 < n)
    (retained : ℕ → ℕ → Bool) (lower : ℕ → ℕ → ℝ)
    (hcell : ∀ i < n, ∀ j < n, retained i j = true → lower i j ≤
      ∫ x in point n i..point n (i + 1), ∫ y in point n j..point n (j + 1), H (x, y)) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if retained i j then lower i j else 0) ≤
      ∫ x in 0..1, ∫ y in 0..1, H (x, y) := by
  apply sum_lower_le_unitSquare hH hn
  intro i hi j hj
  split_ifs with h
  · exact hcell i hi j hj h
  · exact cellIntegral_nonneg hH0 hi hj

end UniformGrid

namespace Completion

theorem fixedSquareIntegral_ge_grid_sum {a b : ℝ} (hchi : |obliquity a b| < 1)
    {n : ℕ} (hn : 0 < n) (lower : ℕ → ℕ → ℝ)
    (hcell : ∀ i < n, ∀ j < n, lower i j ≤
      ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), unitSquareDensity a b s t) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, lower i j) ≤ fixedSquareIntegral a b :=
  UniformGrid.sum_lower_le_unitSquare (continuous_unitSquareDensity_of_obliquity hchi) hn lower hcell

theorem fixedSquareIntegral_ge_retained_grid_sum {a b : ℝ}
    (ha : 0 ≤ a) (hchi : |obliquity a b| < 1) {n : ℕ} (hn : 0 < n)
    (retained : ℕ → ℕ → Bool) (lower : ℕ → ℕ → ℝ)
    (hcell : ∀ i < n, ∀ j < n, retained i j = true → lower i j ≤
      ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), unitSquareDensity a b s t) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if retained i j then lower i j else 0) ≤
      fixedSquareIntegral a b :=
  UniformGrid.sum_retained_lower_le_unitSquare (continuous_unitSquareDensity_of_obliquity hchi)
    (fun p hp ↦ unitSquareDensity_nonneg_of_obliquity ha hchi hp.1.1 p.2) hn retained lower hcell

theorem F_ge_grid_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)
    {n : ℕ} (hn : 0 < n) (lower : ℕ → ℕ → ℝ)
    (hcell : ∀ i < n, ∀ j < n, lower i j ≤
      ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), unitSquareDensity a b s t) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, lower i j) ≤ F a b := by
  rw [F_eq_unitSquare ha hb hab]
  exact UniformGrid.sum_lower_le_unitSquare (continuous_unitSquareDensity ha hb hab) hn lower hcell

theorem F_ge_retained_grid_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)
    {n : ℕ} (hn : 0 < n) (retained : ℕ → ℕ → Bool) (lower : ℕ → ℕ → ℝ)
    (hcell : ∀ i < n, ∀ j < n, retained i j = true → lower i j ≤
      ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), unitSquareDensity a b s t) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if retained i j then lower i j else 0) ≤ F a b := by
  rw [F_eq_fixedSquareIntegral ha hb hab]
  exact fixedSquareIntegral_ge_retained_grid_sum ha
    (obliquity_abs_lt_one_of_total_lt_one hb (by linarith)) hn retained lower hcell

end Completion
end BlaschkeLebesgue
