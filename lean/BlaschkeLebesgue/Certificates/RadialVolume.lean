module

public import BlaschkeLebesgue.Certificates.RadialRows
public import BlaschkeLebesgue.RadialMaster

/-!
# The complete radial branch for actual constant-width bodies

The kernel-checked rows, their actual spherical integrals, and the proved master
inequality give the required strict volume bound for every enclosing radius at
most `60849/100000`. The larger-radius completion branch remains open.
-/

public noncomputable section

open MeasureTheory

namespace BlaschkeLebesgue.Certificates.RadialArithmetic

theorem parameterA_cast (p : Parameters) :
    (parameterA p : ℝ) = Radial.slope (parameterM p) p.tangentPoint := by
  simp [parameterA, Radial.slope]

theorem parameterB_cast (p : Parameters) :
    (parameterB p : ℝ) = Radial.intercept (parameterM p) p.tangentPoint := by
  simp [parameterB, parameterA_cast, Radial.intercept]

/-- Each stored row now gives its certified coefficient as a lower bound on actual volume. -/
theorem all_rows_volume_lower {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (i : Fin 8)
    (hRlo : ((rows i).parameters.lo : ℝ) ≤ b.radius)
    (hRhi : b.radius ≤ ((rows i).parameters.hi : ℝ)) :
    Real.pi * (coefficient (rows i).parameters (rows i).positive (rows i).negative : ℝ) ≤
      bodyVolume K := by
  let p := (rows i).parameters
  have hrow := all_rows_verified i
  have hm : (0 : ℝ) < parameterM p := by
    exact_mod_cast (checkRow_parameters_pos hrow).1
  have hmR : (parameterM p : ℝ) ≤ 1 - b.radius ^ 2 := by
    simp only [parameterM, Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
    have hhi : 0 ≤ (p.hi : ℝ) := b.radius_nonneg.trans hRhi
    nlinarith only [b.radius_nonneg, hRhi, hhi]
  have hdenQ : 0 < 3 * parameterA p - 2 := by
    simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at hrow
    tauto
  have hden : 0 < 3 * Radial.slope (parameterM p) p.tangentPoint - 2 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hdenQ
    simpa only [Rat.cast_zero, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, parameterA_cast] using h
  have hmaster := (b.centeredBody_width hK).radial_master
    (b.centeredBody_zero_mem_interior hK) b.radius_nonneg (fun _ hx => b.centeredBody_norm_le hx)
    hm hmR (p.tangentPoint : ℝ)
  have hgap := all_rows_gap_integral_lower hK b i hRlo hRhi
  rw [MinimumEnclosingBall.centeredBody, bodyVolume_translateBody] at hmaster
  change Real.pi * (coefficient p (rows i).positive (rows i).negative : ℝ) ≤ bodyVolume K
  rw [coefficient]
  push_cast
  rw [parameterA_cast, parameterB_cast, ← mul_div_assoc Real.pi]
  apply (div_le_iff₀ hden).2
  push_cast at hgap
  dsimp only [p, MinimumEnclosingBall.centeredBody] at hmaster hgap ⊢
  simp only [div_eq_mul_inv] at hmaster hgap ⊢
  nlinarith only [hmaster, hgap]

theorem volume_gt_of_radius_in_radial_interval {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (b : MinimumEnclosingBall K)
    (hR : b.radius ∈ Set.Icc (3 / 5) (60849 / 100000)) :
    (4144109 / 10000000 : ℝ) < bodyVolume K := by
  obtain ⟨i, hlo, hhi, hmargin⟩ := certified_radius_cover hR
  exact hmargin.trans_le (all_rows_volume_lower hK b i hlo hhi)

end BlaschkeLebesgue.Certificates.RadialArithmetic

namespace BlaschkeLebesgue

/-- End-to-end volume bound for the entire low- and intermediate-radius range. -/
theorem MinimumEnclosingBall.volume_gt_of_radius_le_radial_cutoff {K : ConvexBody Space}
    (b : MinimumEnclosingBall K) (hK : HasConstantWidth K 1)
    (hR : b.radius ≤ 60849 / 100000) : (259 / 625 : ℝ) < bodyVolume K := by
  by_cases hlo : b.radius ≤ 3 / 5
  · exact b.volume_gt_of_radius_le_three_fifths hK hlo
  · have h := Certificates.RadialArithmetic.volume_gt_of_radius_in_radial_interval hK b
      ⟨(lt_of_not_ge hlo).le, hR⟩
    linarith only [h]

end BlaschkeLebesgue
