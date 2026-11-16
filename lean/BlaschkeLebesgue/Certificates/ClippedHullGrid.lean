module

public import BlaschkeLebesgue.Certificates.ClippedHullCheckComputation
public import BlaschkeLebesgue.Certificates.ConsecutiveCover
public import BlaschkeLebesgue.Certificates.FixedInterval

/-! # Real containment for the rational clipped-hull grid -/

public section

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint

theorem rationalInterval_contains {p : ℕ} {a b : ℚ} {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) : (rationalInterval p a b).Contains p x := by
  have ha' : (Interval.rational p a.num a.den).Contains p (a : ℝ) := by
    simpa only [Rat.cast_def, Int.cast_natCast] using Interval.contains_rational p a.num a.den
  have hb' : (Interval.rational p b.num b.den).Contains p (b : ℝ) := by
    simpa only [Rat.cast_def, Int.cast_natCast] using Interval.contains_rational p b.num b.den
  exact Interval.contains_span ha' hb' ha hb

theorem radiusInterval_contains {p i nr : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hlo : (radiusSquaredCut i nr : ℝ) ≤ R ^ 2)
    (hhi : R ^ 2 ≤ (radiusSquaredCut (i + 1) nr : ℝ))
    (hcheck : (rationalInterval p (radiusSquaredCut i nr)
      (radiusSquaredCut (i + 1) nr)).sqrtCheck = true) :
    (radiusInterval p i nr).Contains p R := by
  have h := Interval.contains_sqrt (rationalInterval_contains hlo hhi) hcheck
  simpa only [radiusInterval, Real.sqrt_sq hR] using h

theorem edgeSquaredInterval_contains {p j ne : ℕ} {x : ℝ}
    (hlo : ((1 - (2 / 25 : ℚ) * (j + 1) / ne : ℚ) : ℝ) ≤ x)
    (hhi : x ≤ ((1 - (2 / 25 : ℚ) * j / ne : ℚ) : ℝ)) :
    (edgeSquaredInterval p j ne).Contains p x := rationalInterval_contains hlo hhi

theorem radius_grid_sqrtChecks : ∀ i : Fin 32,
    (rationalInterval 128 (radiusSquaredCut i 32) (radiusSquaredCut (i + 1) 32)).sqrtCheck = true := by
  decide +kernel

theorem radius_grid_cover {R : ℝ} (hR : 60849 / 100000 ≤ R) (hRhi : R ^ 2 ≤ 3 / 8) :
    ∃ i : Fin 32, (radiusInterval 128 i 32).Contains 128 R := by
  have hR0 : 0 ≤ R := by linarith
  have hlo : (radiusSquaredCut 0 32 : ℝ) ≤ R ^ 2 := by
    norm_num [radiusSquaredCut, radiusSquaredLow]
    nlinarith
  have hhi : R ^ 2 ≤ (radiusSquaredCut 32 32 : ℝ) := by
    norm_num [radiusSquaredCut, radiusSquaredLow]
    exact hRhi
  obtain ⟨i, hi, hl, hu⟩ := exists_consecutive_interval (f := fun i ↦ (radiusSquaredCut i 32 : ℝ))
    (by norm_num : 0 < 32) hlo hhi
  exact ⟨⟨i, hi⟩, radiusInterval_contains hR0 hl hu (radius_grid_sqrtChecks ⟨i, hi⟩)⟩

theorem edge_grid_cover {x : ℝ} (hx : 23 / 25 ≤ x) (hx1 : x ≤ 1) :
    ∃ j : Fin 100, (edgeSquaredInterval 128 j 100).Contains 128 x := by
  obtain ⟨j, hj, hl, hu⟩ := exists_consecutive_interval
    (f := fun j ↦ (2 / 25 : ℝ) * j / 100) (x := 1 - x)
    (by norm_num : 0 < 100) (by simp; linarith) (by norm_num; linarith)
  refine ⟨⟨j, hj⟩, edgeSquaredInterval_contains ?_ ?_⟩
  · push_cast
    push_cast at hu
    linarith
  · push_cast
    linarith

end BlaschkeLebesgue.Certificates.ClippedHull
