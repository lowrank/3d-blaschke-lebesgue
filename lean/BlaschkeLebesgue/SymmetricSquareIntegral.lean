module

public import BlaschkeLebesgue.RectangleQuadrantIntegral

/-! # Splitting a symmetric square integral and mapping its triangle to a unit square -/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue

theorem integral_square_eq_two_triangle {H : ℝ × ℝ → ℝ} (hH : Continuous H)
    (hsym : ∀ x y, H (x, y) = H (y, x)) (T : ℝ) :
    (∫ x in Ioo 0 T, ∫ y in Ioo 0 T, H (x, y)) =
      2 * ∫ x in Ioo 0 T, ∫ y in Ioo 0 x, H (x, y) := by
  let L : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 < p.1}.indicator H
  let U : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 < p.2}.indicator H
  have hmL : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
    (isOpen_lt continuous_snd continuous_fst).measurableSet
  have hmU : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hi : IntegrableOn H (Ioo 0 T ×ˢ Ioo 0 T) (volume.prod volume) :=
    (hH.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hiL : IntegrableOn L (Ioo 0 T ×ˢ Ioo 0 T) (volume.prod volume) := hi.indicator hmL
  have hiU : IntegrableOn U (Ioo 0 T ×ˢ Ioo 0 T) (volume.prod volume) := hi.indicator hmU
  have hne : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).2
    exact Filter.Eventually.of_forall fun x ↦ (volume.ae_ne x).mono fun _ h ↦ h.symm
  have hadd : H =ᵐ[(volume.prod volume).restrict (Ioo 0 T ×ˢ Ioo 0 T)] fun p ↦ L p + U p := by
    filter_upwards [ae_restrict_of_ae hne] with p hp
    rcases lt_or_gt_of_ne hp with hp | hp
    · simp [L, U, hp, not_lt_of_gt hp]
    · simp [L, U, hp, not_lt_of_gt hp]
  have hswap : (∫ p in Ioo 0 T ×ˢ Ioo 0 T, U p ∂volume.prod volume) =
      ∫ p in Ioo 0 T ×ˢ Ioo 0 T, L p ∂volume.prod volume := by
    rw [← setIntegral_prod_swap (Ioo 0 T) (Ioo 0 T) L]
    apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p _
    dsimp only [U, L]
    by_cases hp : p.1 < p.2
    · simp [hp, hsym p.1 p.2, Prod.swap]
    · simp [hp]
  have hslice (x : ℝ) (hx : x ∈ Ioo 0 T) :
      (∫ y in Ioo 0 T, L (x, y)) = ∫ y in Ioo 0 x, H (x, y) := by
    change (∫ y in Ioo 0 T, (Iio x).indicator (fun y ↦ H (x, y)) y) = _
    rw [setIntegral_indicator measurableSet_Iio]
    have he : Ioo 0 T ∩ Iio x = Ioo 0 x := by
      ext y
      simp only [mem_inter_iff, mem_Ioo, mem_Iio]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · exact fun h ↦ ⟨⟨h.1, h.2.trans hx.2⟩, h.2⟩
    rw [he]
  calc
    _ = ∫ p in Ioo 0 T ×ˢ Ioo 0 T, H p ∂volume.prod volume := (setIntegral_prod H hi).symm
    _ = (∫ p in Ioo 0 T ×ˢ Ioo 0 T, L p ∂volume.prod volume) +
        ∫ p in Ioo 0 T ×ˢ Ioo 0 T, U p ∂volume.prod volume := by
      rw [integral_congr_ae hadd, integral_add hiL hiU]
    _ = 2 * ∫ p in Ioo 0 T ×ˢ Ioo 0 T, L p ∂volume.prod volume := by rw [hswap]; ring
    _ = _ := by
      rw [setIntegral_prod L hiL]
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioo hslice

theorem intervalIntegral_square_eq_two_triangle {H : ℝ × ℝ → ℝ} (hH : Continuous H)
    (hsym : ∀ x y, H (x, y) = H (y, x)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in 0..T, ∫ y in 0..T, H (x, y)) = 2 * ∫ x in 0..T, ∫ y in 0..x, H (x, y) := by
  have htri : (∫ x in Ioo 0 T, ∫ y in Ioo 0 x, H (x, y)) = ∫ x in 0..T, ∫ y in 0..x, H (x, y) := by
    rw [intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    rw [intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo]
  have h := integral_square_eq_two_triangle hH hsym T
  rw [htri] at h
  simpa only [intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo] using h

theorem intervalIntegral_triangle_unitSquare (H : ℝ × ℝ → ℝ) (T : ℝ) :
    (∫ x in 0..T, ∫ y in 0..x, H (x, y)) =
      T ^ 2 * ∫ s in 0..1, ∫ t in 0..1, s * H (T * s, T * s * t) := by
  have hx := intervalIntegral.smul_integral_comp_mul_left
    (fun x ↦ ∫ y in 0..x, H (x, y)) (a := 0) (b := 1) T
  simp only [smul_eq_mul, mul_zero, mul_one] at hx
  rw [← hx]
  have hy (x : ℝ) := intervalIntegral.smul_integral_comp_mul_left
    (fun y ↦ H (x, y)) (a := 0) (b := 1) x
  simp only [smul_eq_mul, mul_zero, mul_one] at hy
  simp_rw [← hy, intervalIntegral.integral_const_mul, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

end BlaschkeLebesgue
