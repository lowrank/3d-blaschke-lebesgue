module

public import BlaschkeLebesgue.Certificates.ClippedHullSixEdges
public import BlaschkeLebesgue.Certificates.ClippedHullSecantSoundness

/-! # Contact deficit bounds within a certified radius bucket -/

public noncomputable section

namespace BlaschkeLebesgue.Certificates.ClippedHull

 theorem radiusSquaredCut_lower (i : ℕ) : (60849 / 100000 : ℝ) ^ 2 ≤ (radiusSquaredCut i 512 : ℝ) := by
  unfold radiusSquaredCut radiusSquaredLow
  push_cast
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  nlinarith

 theorem sqrt_cut_gt_half (i : Fin 513) : 1 / 2 < Real.sqrt (radiusSquaredCut i 512 : ℝ) := by
  have hl := radiusSquaredCut_lower i
  have hs := Real.sq_sqrt (show 0 ≤ (radiusSquaredCut i 512 : ℝ) by nlinarith)
  have hn := Real.sqrt_nonneg (radiusSquaredCut i 512 : ℝ)
  nlinarith

 theorem sqrt_cut_ge_cutoff (i : ℕ) :
    60849 / 100000 ≤ Real.sqrt (radiusSquaredCut i 512 : ℝ) := by
  have hl := radiusSquaredCut_lower i
  have hs := Real.sq_sqrt (show 0 ≤ (radiusSquaredCut i 512 : ℝ) by nlinarith)
  have hn := Real.sqrt_nonneg (radiusSquaredCut i 512 : ℝ)
  nlinarith

 theorem radius_bucket_cover {R : ℝ} (hR : 60849 / 100000 ≤ R) (hhi : R ^ 2 ≤ 3 / 8) :
    ∃ i : Fin 512, (radiusSquaredCut i 512 : ℝ) ≤ R ^ 2 ∧
      R ^ 2 ≤ (radiusSquaredCut (i + 1) 512 : ℝ) := by
  have hlo : (radiusSquaredCut 0 512 : ℝ) ≤ R ^ 2 := by
    norm_num [radiusSquaredCut, radiusSquaredLow]
    nlinarith
  have htop : R ^ 2 ≤ (radiusSquaredCut 512 512 : ℝ) := by
    norm_num [radiusSquaredCut, radiusSquaredLow]
    exact hhi
  obtain ⟨i, hi, hl, hu⟩ := exists_consecutive_interval (f := fun i ↦ (radiusSquaredCut i 512 : ℝ))
    (by norm_num : 0 < 512) hlo htop
  exact ⟨⟨i, hi⟩, hl, hu⟩

end BlaschkeLebesgue.Certificates.ClippedHull

namespace BlaschkeLebesgue.BalancedContacts

open Certificates.ClippedHull

variable (c : BalancedContacts 4 Space)

theorem deficit_in_radius_bucket (i : Fin 512)
    (hlo : (radiusSquaredCut i 512 : ℝ) ≤ c.radius ^ 2)
    (hhi : c.radius ^ 2 ≤ (radiusSquaredCut (i + 1) 512 : ℝ)) :
    16 * (3 / 8 - (radiusSquaredCut (i + 1) 512 : ℝ)) ≤ c.totalDeficit ∧
      c.totalDeficit ≤ (secantBudget i 512 : ℝ) := by
  have hp : (1 / 4 : ℝ) < (radiusSquaredCut i 512 : ℝ) := by
    have hh : ((1 / 4 : ℚ) : ℝ) < (radiusSquaredCut i 512 : ℝ) := by
      exact_mod_cast (secant_parameter_checks i).1
    norm_num at hh
    exact hh
  have hA := c.totalDeficit_nonneg
  have hu := c.deficit_upper_mul
  constructor
  · linarith [c.deficit_lower]
  · unfold secantBudget
    push_cast
    apply (le_div_iff₀ (show 0 < 1 - 8 * (3 / 8 - (radiusSquaredCut i 512 : ℝ)) by linarith)).2
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hlo)]

theorem clipped_volume_ge_certified_bucket
    (checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true)
    (baselineChecks : ∀ i : Fin 32, baselineSignCheck 128 64 i 32 = true)
    (i : Fin 512) (hs : secantCheck 128 64 i 512 = true)
    (hlo : (radiusSquaredCut i 512 : ℝ) ≤ c.radius ^ 2)
    (hhi : c.radius ^ 2 ≤ (radiusSquaredCut (i + 1) 512 : ℝ))
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hR0 : 0 ≤ c.radius)
    (hR1 : c.radius ≤ 1) :
    secantBound i 512 - (secantResponse i 512 : ℝ) ≤
      (47 * bodyVolume (clippedInnerBody c.radius (Set.range c.point) hne hR1) -
        bodyVolume (clippedOuterBody c.radius (Set.range c.point) hne)) / 46 := by
  have hp := secant_parameter_checks i
  have hE0 : (0 : ℝ) < (secantBudget i 512 : ℝ) := by exact_mod_cast hp.2.2.2.1
  have hEhi : (secantBudget i 512 : ℝ) ≤ 2 / 25 := by
    have hh : (secantBudget i 512 : ℝ) ≤ ((2 / 25 : ℚ) : ℝ) := by
      exact_mod_cast hp.2.2.2.2.le
    norm_num at hh
    exact hh
  have hrlo := sqrt_cut_gt_half ⟨i, by omega⟩
  have hrhi := sqrt_cut_gt_half ⟨i + 1, by omega⟩
  have hSsq := Real.sq_sqrt (show 0 ≤ (radiusSquaredCut (i + 1) 512 : ℝ) by
    have := radiusSquaredCut_lower (i + 1); nlinarith)
  have hSbound : Real.sqrt (radiusSquaredCut (i + 1) 512 : ℝ) ^ 2 ≤ 3 / 8 := by
    rw [hSsq]
    have hh : (radiusSquaredCut (i + 1) 512 : ℝ) ≤ ((3 / 8 : ℚ) : ℝ) := by
      exact_mod_cast hp.2.2.1
    norm_num at hh
    exact hh
  have hloR : Real.sqrt (radiusSquaredCut i 512 : ℝ) ≤ c.radius :=
    (Real.sqrt_le_iff).2 ⟨hR0, hlo⟩
  have hhiR : c.radius ≤ Real.sqrt (radiusSquaredCut (i + 1) 512 : ℝ) := by
    have hn := Real.sqrt_nonneg (radiusSquaredCut (i + 1) 512 : ℝ)
    nlinarith
  have hm := (secantCheck_sound_512 i hs).1
  rw [secantSlope_manuscript hrhi (by linarith)] at hm
  have hb := c.deficit_in_radius_bucket i hlo hhi
  have hv := c.clipped_volume_combination_ge_bucket (hne := hne) checks baselineChecks
    (sqrt_cut_ge_cutoff i) hloR hhiR hSbound hE0 hEhi hb.2 hb.1 hm.le hR1
  rw [secantBound_manuscript hrlo, secantSlope_manuscript hrhi (by linarith)]
  linarith only [hv]

end BlaschkeLebesgue.BalancedContacts
