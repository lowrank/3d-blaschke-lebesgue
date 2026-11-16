module

public import BlaschkeLebesgue.Certificates.ProjectiveGradientCell
public import BlaschkeLebesgue.Certificates.ProjectivePointIntegral
public import BlaschkeLebesgue.ParameterBoxEstimate

/-!
# Signed parameter variation from the executable gradient grid

Each cell's slope interval is multiplied by its outward-rounded area, and
the resulting intervals are added exactly. Successful evaluations imply
secant bounds for the actual fixed-square integral, including its cutoffs.
-/

@[expose] public section

open Set MeasureTheory

namespace BlaschkeLebesgue.Certificates.ProjectiveGradientIntegral

open FixedPoint ProjectiveExpressions

theorem sumRange_congr {n : ℕ} {f g : ℕ → Option Interval} (h : ∀ i < n, f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange, ih (fun i hi ↦ h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumRange_bounds {p n : ℕ} {f : ℕ → Option Interval} {g : ℕ → ℝ} {I : Interval} {delta : ℝ}
    (h : sumRange n f = some I)
    (hb : ∀ i < n, ∀ J, f i = some J → value p J.lo * delta ≤ g i ∧ g i ≤ value p J.hi * delta) :
    value p I.lo * delta ≤ ∑ i ∈ Finset.range n, g i ∧
      (∑ i ∈ Finset.range n, g i) ≤ value p I.hi * delta := by
  induction n generalizing I with
  | zero =>
    simp only [sumRange, Option.some.injEq] at h
    subst I
    simp only [value_zero, zero_mul, Finset.range_zero, Finset.sum_empty, le_refl, and_self]
  | succ n ih =>
    simp only [sumRange, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, v, hv, rfl⟩ := h
    have h1 := ih hs (fun i hi ↦ hb i (Nat.lt_succ_of_lt hi))
    have h2 := hb n (Nat.lt_succ_self n) v hv
    simp only [Interval.add, value_add, add_mul, Finset.sum_range_succ]
    exact ⟨add_le_add h1.1 h2.1, add_le_add h1.2 h2.2⟩

theorem cell_sound {p n i j : ℕ} {dir : Bool} {A B I : Interval} {par : Params Jet}
    {fixed l r : ℝ} (hp : parameterJets p dir A B = some par) (hc : cell p n par i j = some I)
    (hi : i < n) (hj : j < n) (hlr : l ≤ r)
    (hA : ∀ z ∈ Icc l r, A.Contains p (axisA dir fixed z))
    (hB : ∀ z ∈ Icc l r, B.Contains p (axisB dir fixed z))
    (hdom : ∀ z ∈ Icc l r, 0 ≤ axisA dir fixed z ∧ 0 ≤ axisB dir fixed z ∧
      axisA dir fixed z + axisB dir fixed z ≤ 1 / 10) :
    value p I.lo * (r - l) ≤
      ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1),
          (Completion.unitSquareDensity (axisA dir fixed r) (axisB dir fixed r) s t -
            Completion.unitSquareDensity (axisA dir fixed l) (axisB dir fixed l) s t) ∧
    (∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1),
          (Completion.unitSquareDensity (axisA dir fixed r) (axisB dir fixed r) s t -
            Completion.unitSquareDensity (axisA dir fixed l) (axisB dir fixed l) s t)) ≤ value p I.hi * (r - l) := by
  by_cases heq : l = r
  · subst r
    simp only [sub_self, mul_zero, intervalIntegral.integral_zero, le_refl, and_self]
  have hdelta : 0 < r - l := sub_pos.mpr (lt_of_le_of_ne hlr heq)
  have hn := Nat.zero_lt_of_lt hi
  simp only [cell, Option.map_eq_some_iff] at hc
  obtain ⟨J, hJ, rfl⟩ := hc
  have hchi (z : ℝ) (hz : z ∈ Icc l r) : |Completion.obliquity (axisA dir fixed z) (axisB dir fixed z)| < 1 :=
    Completion.obliquity_abs_lt_one_of_total_lt_one (hdom z hz).2.1 (by linarith [(hdom z hz).2.2])
  have hcont := (Completion.continuous_unitSquareDensity_of_obliquity (hchi r ⟨hlr, le_rfl⟩)).sub
    (Completion.continuous_unitSquareDensity_of_obliquity (hchi l ⟨le_rfl, hlr⟩))
  have hb (s : ℝ) (hs : s ∈ Icc (UniformGrid.point n i) (UniformGrid.point n (i + 1)))
      (t : ℝ) (ht : t ∈ Icc (UniformGrid.point n j) (UniformGrid.point n (j + 1))) := by
    have hst : (s, t) ∈ Icc 0 1 ×ˢ Icc 0 1 := UniformGrid.cell_subset_unitSquare hi hj ⟨hs, ht⟩
    exact ProjectiveGradientCell.slope_sound hp hJ hlr hA hB
      (ProjectivePointIntegral.span_contains hs) (ProjectivePointIntegral.span_contains ht) hst.2 hdom
  have horder : value p J.lo ≤ value p J.hi := by
    have hv := hb (UniformGrid.point n i) ⟨le_rfl, UniformGrid.point_mono n (Nat.le_succ i)⟩
      (UniformGrid.point n j) ⟨le_rfl, UniformGrid.point_mono n (Nat.le_succ j)⟩
    exact (mul_le_mul_iff_left₀ hdelta).mp (hv.1.trans hv.2)
  have ha : (ProjectivePointIntegral.area p n).Contains p (UniformGrid.area n) := by
    rw [UniformGrid.area_eq_four_halfWidth_sq]
    exact ProjectivePointIntegral.area_contains p n
  have hlow := (Interval.contains_mul ha (show J.Contains p (value p J.lo) from ⟨le_rfl, horder⟩)).1
  have hupp := (Interval.contains_mul ha (show J.Contains p (value p J.hi) from ⟨horder, le_rfl⟩)).2
  have hl := rectangle_integral_lower hcont (UniformGrid.point_mono n (Nat.le_succ i))
    (UniformGrid.point_mono n (Nat.le_succ j)) (fun s hs t ht ↦ (hb s hs t ht).1)
  have hu := rectangle_integral_upper hcont (UniformGrid.point_mono n (Nat.le_succ i))
    (UniformGrid.point_mono n (Nat.le_succ j)) (fun s hs t ht ↦ (hb s hs t ht).2)
  have harea : (1 / (n : ℝ)) * (1 / (n : ℝ)) = UniformGrid.area n := by
    simp only [UniformGrid.area, one_div, pow_two, mul_inv_rev]
  simp only [Pi.sub_apply, UniformGrid.cell_width hn, ← mul_assoc, harea] at hl hu
  exact ⟨(mul_le_mul_of_nonneg_right hlow hdelta.le).trans hl,
    hu.trans (mul_le_mul_of_nonneg_right hupp hdelta.le)⟩

theorem grid_sound {p n : ℕ} {dir : Bool} {A B I : Interval} {par : Params Jet}
    {fixed l r : ℝ} (hp : parameterJets p dir A B = some par) (hc : grid p n par = some I)
    (hn : 0 < n) (hlr : l ≤ r)
    (hA : ∀ z ∈ Icc l r, A.Contains p (axisA dir fixed z))
    (hB : ∀ z ∈ Icc l r, B.Contains p (axisB dir fixed z))
    (hdom : ∀ z ∈ Icc l r, 0 ≤ axisA dir fixed z ∧ 0 ≤ axisB dir fixed z ∧
      axisA dir fixed z + axisB dir fixed z ≤ 1 / 10) :
    value p I.lo * (r - l) ≤
      Completion.fixedSquareIntegral (axisA dir fixed r) (axisB dir fixed r) -
        Completion.fixedSquareIntegral (axisA dir fixed l) (axisB dir fixed l) ∧
    Completion.fixedSquareIntegral (axisA dir fixed r) (axisB dir fixed r) -
        Completion.fixedSquareIntegral (axisA dir fixed l) (axisB dir fixed l) ≤ value p I.hi * (r - l) := by
  let H : ℝ × ℝ → ℝ := fun q ↦
    Completion.unitSquareDensity (axisA dir fixed r) (axisB dir fixed r) q.1 q.2 -
      Completion.unitSquareDensity (axisA dir fixed l) (axisB dir fixed l) q.1 q.2
  have hchi (z : ℝ) (hz : z ∈ Icc l r) : |Completion.obliquity (axisA dir fixed z) (axisB dir fixed z)| < 1 :=
    Completion.obliquity_abs_lt_one_of_total_lt_one (hdom z hz).2.1 (by linarith [(hdom z hz).2.2])
  have hr := Completion.continuous_unitSquareDensity_of_obliquity (hchi r ⟨hlr, le_rfl⟩)
  have hl := Completion.continuous_unitSquareDensity_of_obliquity (hchi l ⟨le_rfl, hlr⟩)
  have hb := sumRange_bounds hc (g := fun i ↦ ∑ j ∈ Finset.range n,
      ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), H (s, t))
    (fun i hi v hv ↦ sumRange_bounds hv (fun j hj w hw ↦ cell_sound hp hw hi hj hlr hA hB hdom))
  have hcont : Continuous H := hr.sub hl
  rw [← UniformGrid.integral_unitSquare_eq_sum hcont hn] at hb
  change value p I.lo * (r - l) ≤ (∫ s in 0..1, ∫ t in 0..1, H (s, t)) ∧
    (∫ s in 0..1, ∫ t in 0..1, H (s, t)) ≤ value p I.hi * (r - l) at hb
  dsimp only [H] at hb
  rw [iterated_intervalIntegral_sub hr hl (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)] at hb
  exact hb

theorem check_sound {p n : ℕ} {dir : Bool} {A B I : Interval} {fixed l r : ℝ}
    (hc : check p n dir A B = some I) (hn : 0 < n) (hlr : l ≤ r)
    (hA : ∀ z ∈ Icc l r, A.Contains p (axisA dir fixed z))
    (hB : ∀ z ∈ Icc l r, B.Contains p (axisB dir fixed z))
    (hdom : ∀ z ∈ Icc l r, 0 ≤ axisA dir fixed z ∧ 0 ≤ axisB dir fixed z ∧
      axisA dir fixed z + axisB dir fixed z ≤ 1 / 10) :
    value p I.lo * (r - l) ≤
      Completion.fixedSquareIntegral (axisA dir fixed r) (axisB dir fixed r) -
        Completion.fixedSquareIntegral (axisA dir fixed l) (axisB dir fixed l) ∧
    Completion.fixedSquareIntegral (axisA dir fixed r) (axisB dir fixed r) -
        Completion.fixedSquareIntegral (axisA dir fixed l) (axisB dir fixed l) ≤ value p I.hi * (r - l) := by
  simp only [check, Option.bind_eq_some_iff] at hc
  obtain ⟨par, hp, hg⟩ := hc
  exact grid_sound hp hg hn hlr hA hB hdom

/-- A successful grid controls every subsegment of the supplied parameter
interval, in the form needed by the box acceptance theorem. -/
theorem check_secantBounds {p n : ℕ} {dir : Bool} {A B I : Interval} {fixed l r : ℝ}
    (hc : check p n dir A B = some I) (hn : 0 < n)
    (hA : ∀ z ∈ Icc l r, A.Contains p (axisA dir fixed z))
    (hB : ∀ z ∈ Icc l r, B.Contains p (axisB dir fixed z))
    (hdom : ∀ z ∈ Icc l r, 0 ≤ axisA dir fixed z ∧ 0 ≤ axisB dir fixed z ∧
      axisA dir fixed z + axisB dir fixed z ≤ 1 / 10) :
    SecantBounds (fun z ↦ Completion.fixedSquareIntegral (axisA dir fixed z) (axisB dir fixed z))
      l r (value p I.lo) (value p I.hi) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc l r := Icc_subset_Icc hx.1 hy.2
  exact check_sound hc hn hxy (fun z hz ↦ hA z (hsub hz))
    (fun z hz ↦ hB z (hsub hz)) (fun z hz ↦ hdom z (hsub hz))

end BlaschkeLebesgue.Certificates.ProjectiveGradientIntegral
