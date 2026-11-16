module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation
public import BlaschkeLebesgue.Certificates.ClippedHullSecantParameters
public import BlaschkeLebesgue.Certificates.ClippedHullExpressions
public import BlaschkeLebesgue.Certificates.ClippedHullGrid

/-! # Soundness of the exact secant bucket comparisons -/

public noncomputable section

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint

attribute [local irreducible] volumeProgram

@[expose] def secantSlope (i levels : ℕ) : ℝ :=
  let R := Real.sqrt (radiusSquaredCut (i + 1) levels : ℝ)
  ((realVolumes R (1 - (secantBudget i levels : ℝ))).combined -
    (realVolumes R 1).combined) / (secantBudget i levels : ℝ)

@[expose] def secantResponse (i levels : ℕ) : ℚ :=
  (8 / 23) * (3 * (153 / 100000) +
    ((-601 / 100000) + 2 * (317 / 20000)) * 16 * (3 / 8 - radiusSquaredCut (i + 1) levels))

@[expose] def secantBound (i levels : ℕ) : ℝ :=
  (realVolumes (Real.sqrt (radiusSquaredCut i levels : ℝ)) 1).baseline +
    (16 * (3 / 8 - (radiusSquaredCut (i + 1) levels : ℝ))) * secantSlope i levels +
    (secantResponse i levels : ℝ)

theorem rationalPoint_contains (p : ℕ) (a : ℚ) : (rationalInterval p a a).Contains p (a : ℝ) :=
  rationalInterval_contains le_rfl le_rfl

theorem secantEvaluation_sound {p n i levels : ℕ} {slope margin : Interval}
    (h : secantEvaluation p n i levels = some (slope, margin))
    (h0 : (rationalInterval p (radiusSquaredCut i levels)
      (radiusSquaredCut i levels)).sqrtCheck = true)
    (h1 : (rationalInterval p (radiusSquaredCut (i + 1) levels)
      (radiusSquaredCut (i + 1) levels)).sqrtCheck = true) :
    slope.Contains p (secantSlope i levels) ∧ margin.Contains p (secantBound i levels - 259 / 625) := by
  dsimp only [secantEvaluation] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨base, hb, zero, hz, edge, he, h⟩ := h
  split_ifs at h with hE
  cases h
  have hr0 := Interval.contains_sqrt (rationalPoint_contains p (radiusSquaredCut i levels)) h0
  have hr1 := Interval.contains_sqrt (rationalPoint_contains p (radiusSquaredCut (i + 1) levels)) h1
  have hE' := rationalPoint_contains p (secantBudget i levels)
  have hone : (Interval.integer p 1).Contains p (1 : ℝ) := by
    exact_mod_cast Interval.contains_integer p 1
  have hbase := volumeInterval_sound hb hr0 hone
  have hzero := volumeInterval_sound hz hr1 hone
  have hedge := volumeInterval_sound he hr1 (Interval.contains_sub hone hE')
  have hs := Interval.contains_div (Interval.contains_sub hedge.2.2.1 hzero.2.2.1) hE' hE
  have hd := rationalPoint_contains p (16 * (3 / 8 - radiusSquaredCut (i + 1) levels))
  have hresp := rationalPoint_contains p (secantResponse i levels)
  have ht : (Interval.rational p 259 625).Contains p (259 / 625 : ℝ) := by
    simpa only [Int.cast_ofNat] using Interval.contains_rational p 259 625
  have hbound := Interval.contains_sub
    (Interval.contains_add (Interval.contains_add hbase.2.2.2 (Interval.contains_mul hd hs)) hresp) ht
  refine ⟨hs, ?_⟩
  convert hbound using 1 <;>
    norm_num [secantBound, secantSlope, secantResponse, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_div, Rat.cast_ofNat, div_eq_mul_inv, mul_assoc]

theorem secantCheck_sound {p n i levels : ℕ} (h : secantCheck p n i levels = true)
    (h0 : (rationalInterval p (radiusSquaredCut i levels)
      (radiusSquaredCut i levels)).sqrtCheck = true)
    (h1 : (rationalInterval p (radiusSquaredCut (i + 1) levels)
      (radiusSquaredCut (i + 1) levels)).sqrtCheck = true) :
    0 < secantSlope i levels ∧ 259 / 625 < secantBound i levels := by
  unfold secantCheck at h
  cases hv : secantEvaluation p n i levels with
  | none => simp [hv] at h
  | some v =>
    rcases v with ⟨s, m⟩
    simp only [hv, Bool.and_eq_true] at h
    have hs := secantEvaluation_sound hv h0 h1
    exact ⟨Interval.pos_of_positiveCheck hs.1 h.1,
      by linarith [Interval.pos_of_positiveCheck hs.2 h.2]⟩

theorem secantSlope_manuscript {i levels : ℕ}
    (hR : 1 / 2 < Real.sqrt (radiusSquaredCut (i + 1) levels : ℝ))
    (hE : (secantBudget i levels : ℝ) ≤ 1) :
    secantSlope i levels =
      (ClippedFormula.combinedEdge (Real.sqrt (radiusSquaredCut (i + 1) levels : ℝ))
          (secantBudget i levels : ℝ) -
        ClippedFormula.combinedEdge (Real.sqrt (radiusSquaredCut (i + 1) levels : ℝ)) 0) /
          (secantBudget i levels : ℝ) := by
  dsimp only [secantSlope]
  rw [realVolumes_manuscript hR (by linarith), realVolumes_manuscript hR (by norm_num)]
  simp only [sub_sub_cancel, sub_self]

theorem secantBound_manuscript {i levels : ℕ}
    (hR : 1 / 2 < Real.sqrt (radiusSquaredCut i levels : ℝ)) :
    secantBound i levels = ClippedFormula.combinedBaseline
        (Real.sqrt (radiusSquaredCut i levels : ℝ)) +
      (16 * (3 / 8 - (radiusSquaredCut (i + 1) levels : ℝ))) * secantSlope i levels +
        (secantResponse i levels : ℝ) := by
  unfold secantBound
  rw [realVolumes_baseline hR]

theorem secantCheck_sound_512 {n : ℕ} (i : Fin 512)
    (h : secantCheck 128 n i 512 = true) :
    0 < secantSlope i 512 ∧ 259 / 625 < secantBound i 512 := by
  exact secantCheck_sound h (secant_sqrt_checks ⟨i, by omega⟩)
    (secant_sqrt_checks ⟨i + 1, by omega⟩)

end BlaschkeLebesgue.Certificates.ClippedHull
