module

public import BlaschkeLebesgue.Certificates.ProjectiveCell
public import BlaschkeLebesgue.UniformGridIntegral

/-!
# The point-parameter integral checker

Successful cell computations are summed with exact integer addition. The
soundness theorem bounds the actual fixed-square integral for any positive
grid size, using the checked formula and derivative evaluations in each cell.
-/

@[expose] public section

open Set MeasureTheory

namespace BlaschkeLebesgue.Certificates.ProjectivePointIntegral

open FixedPoint ProjectiveExpressions

theorem sumRange_lower {p n : ℕ} {f : ℕ → Option ℤ} {g : ℕ → ℝ} {z : ℤ}
    (h : sumRange n f = some z)
    (hb : ∀ i < n, ∀ v, f i = some v → value p v ≤ g i) :
    value p z ≤ ∑ i ∈ Finset.range n, g i := by
  induction n generalizing z with
  | zero =>
    simp only [sumRange, Option.some.injEq] at h
    subst z
    simp only [value_zero, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ n ih =>
    simp only [sumRange, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, v, hv, rfl⟩ := h
    rw [value_add, Finset.sum_range_succ]
    exact add_le_add (ih hs (fun i hi ↦ hb i (Nat.lt_succ_of_lt hi))) (hb n (Nat.lt_succ_self n) v hv)

theorem point_contains (p n i : ℕ) : (point p n i).Contains p (UniformGrid.point n i) := by
  simpa only [point, UniformGrid.point, Int.cast_natCast] using Interval.contains_rational p (i : ℤ) (n : ℤ)

theorem span_contains {p n i : ℕ} {x : ℝ}
    (hx : x ∈ Icc (UniformGrid.point n i) (UniformGrid.point n (i + 1))) : (span p n i).Contains p x :=
  Interval.contains_span (point_contains p n i) (point_contains p n (i + 1)) hx.1 hx.2

theorem midpoint_contains (p n i : ℕ) : (midpoint p n i).Contains p (UniformGrid.midpoint n i) := by
  simpa only [midpoint, UniformGrid.midpoint, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_one]
    using Interval.contains_rational p (2 * (i : ℤ) + 1) (2 * (n : ℤ))

theorem halfWidth_contains (p n : ℕ) : (halfWidth p n).Contains p (UniformGrid.halfWidth n) := by
  simpa only [halfWidth, UniformGrid.halfWidth, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_one]
    using Interval.contains_rational p 1 (2 * (n : ℤ))

theorem area_contains (p n : ℕ) : (area p n).Contains p (4 * UniformGrid.halfWidth n * UniformGrid.halfWidth n) := by
  rw [← UniformGrid.area_eq_four_halfWidth_sq]
  simpa only [area, UniformGrid.area, Int.cast_mul, Int.cast_natCast, Int.cast_one, pow_two]
    using Interval.contains_rational p 1 ((n : ℤ) * n)

theorem cell_sound {p n i j : ℕ} {par : Params Interval} {l : ℤ} {a b : ℝ}
    (h : cell p n par i j = some l) (hi : i < n) (hj : j < n)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (ha : 0 ≤ a) (hchi : |Completion.obliquity a b| < 1) :
    value p l ≤ ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
      ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), Completion.unitSquareDensity a b s t := by
  have hn := Nat.zero_lt_of_lt hi
  rw [UniformGrid.point_eq_midpoint_sub hn i, UniformGrid.point_succ_eq_midpoint_add hn i,
    UniformGrid.point_eq_midpoint_sub hn j, UniformGrid.point_succ_eq_midpoint_add hn j]
  apply ProjectiveCell.lower_sound h hp
  · intro s hs
    apply span_contains
    rwa [UniformGrid.point_eq_midpoint_sub hn i, UniformGrid.point_succ_eq_midpoint_add hn i]
  · intro t ht
    apply span_contains
    rwa [UniformGrid.point_eq_midpoint_sub hn j, UniformGrid.point_succ_eq_midpoint_add hn j]
  · exact midpoint_contains p n i
  · exact midpoint_contains p n j
  · exact halfWidth_contains p n
  · exact area_contains p n
  · exact ha
  · exact hchi
  · exact UniformGrid.halfWidth_nonneg n
  · have hc := UniformGrid.cell_subset_unitSquare hi hj
    dsimp only [UniformGrid.cell] at hc
    rwa [UniformGrid.point_eq_midpoint_sub hn i, UniformGrid.point_succ_eq_midpoint_add hn i,
      UniformGrid.point_eq_midpoint_sub hn j, UniformGrid.point_succ_eq_midpoint_add hn j] at hc

theorem grid_sound {p n : ℕ} {par : Params Interval} {l : ℤ} {a b : ℝ}
    (h : grid p n par = some l) (hn : 0 < n)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (ha : 0 ≤ a) (hchi : |Completion.obliquity a b| < 1) :
    value p l ≤ Completion.fixedSquareIntegral a b := by
  have hb := sumRange_lower h (g := fun i ↦ ∑ j ∈ Finset.range n,
      ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), Completion.unitSquareDensity a b s t)
    (fun i hi v hv ↦ sumRange_lower hv (fun j hj w hw ↦ cell_sound hw hi hj hp ha hchi))
  have he := UniformGrid.integral_unitSquare_eq_sum (Completion.continuous_unitSquareDensity_of_obliquity hchi) hn
  exact hb.trans_eq he.symm

theorem check_sound {p n : ℕ} {A B : Interval} {l : ℤ} {a b : ℝ}
    (h : check p n A B = some l) (hn : 0 < n) (hA : A.Contains p a) (hB : B.Contains p b)
    (ha : 0 ≤ a) (hchi : |Completion.obliquity a b| < 1) :
    value p l ≤ Completion.fixedSquareIntegral a b := by
  simp only [check, Option.bind_eq_some_iff] at h
  obtain ⟨par, hp, hg⟩ := h
  exact grid_sound hg hn (paramsInterval_sound hp hA hB) ha hchi

end BlaschkeLebesgue.Certificates.ProjectivePointIntegral
