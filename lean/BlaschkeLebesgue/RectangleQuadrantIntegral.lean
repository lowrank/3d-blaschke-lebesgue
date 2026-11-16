module

public import BlaschkeLebesgue.ActiveCompletionIntegral

/-! # Identifying the scalar rectangle integral with the manuscript's quadrant integral -/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue

theorem integral_Ioo_even {h : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hi : IntegrableOn h (Ioo (-T) T)) (he : ∀ x, h (-x) = h x) :
    (∫ x in Ioo (-T) T, h x) = 2 * ∫ x in Ioo 0 T, h x := by
  have hleft : IntervalIntegrable h volume (-T) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).2
      (hi.mono_set (Ioo_subset_Ioo le_rfl hT))
  have hright : IntervalIntegrable h volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).2
      (hi.mono_set (Ioo_subset_Ioo (by linarith) le_rfl))
  have hn := intervalIntegral.integral_comp_neg h (a := 0) (b := T)
  simp only [he, neg_zero] at hn
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [← hn] at hadd
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hadd
  linarith only [hadd]

theorem integral_rectangle_eq_four_quadrant {H : ℝ × ℝ → ℝ} (hH : Continuous H) {T : ℝ}
    (hT : 0 ≤ T) (he1 : ∀ x y, H (-x, y) = H (x, y))
    (he2 : ∀ x y, H (x, -y) = H (x, y)) :
    (∫ p in {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}, H p) =
      4 * ∫ x in Ioo 0 T, ∫ y in Ioo 0 T, H (x, y) := by
  have hs : {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T} = Ioo (-T) T ×ˢ Ioo (-T) T := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_Ioo, abs_lt]
  have hi := integrableOn_abs_rectangle hH T
  rw [hs] at hi ⊢
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ] at hi ⊢
  rw [setIntegral_prod H hi]
  have hi' : Integrable H ((volume.restrict (Ioo (-T) T)).prod (volume.restrict (Ioo (-T) T))) := by
    rwa [Measure.prod_restrict]
  have he : ∀ x, (∫ y in Ioo (-T) T, H (-x, y)) = ∫ y in Ioo (-T) T, H (x, y) := by
    intro x
    simp_rw [he1]
  rw [integral_Ioo_even hT hi'.integral_prod_left he]
  have hy : ∀ x, (∫ y in Ioo (-T) T, H (x, y)) = 2 * ∫ y in Ioo 0 T, H (x, y) := by
    intro x
    apply integral_Ioo_even hT _ (he2 x)
    exact ((hH.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  simp_rw [hy]
  rw [integral_const_mul]
  ring

namespace Completion

@[expose] def F (a b : ℝ) : ℝ :=
  4 * ∫ x in Ioo 0 (rectangleRadius a b), ∫ y in Ioo 0 (rectangleRadius a b), uniformDensity a b x y

theorem uniformDensity_neg_left (a b x y : ℝ) : uniformDensity a b (-x) y = uniformDensity a b x y := by
  simp only [uniformDensity, allocationNumerator, determinantFactor, uniformW, averagedW, neg_sq]

theorem uniformDensity_neg_right (a b x y : ℝ) : uniformDensity a b x (-y) = uniformDensity a b x y := by
  simp only [uniformDensity, allocationNumerator, determinantFactor, uniformW, averagedW, neg_sq]

theorem rectangleIntegral_eq_F {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    rectangleIntegral a b = F a b := by
  have hT : 0 ≤ rectangleRadius a b := by linarith [(rectangleRadius_bounds ha hb hab).1]
  exact integral_rectangle_eq_four_quadrant (continuous_uniformDensity ha hb hab) hT
    (uniformDensity_neg_left a b) (uniformDensity_neg_right a b)

theorem F_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) : 0 ≤ F a b := by
  rw [← rectangleIntegral_eq_F ha hb hab]
  exact rectangleIntegral_nonneg ha hb hab

theorem F_eq_intervalIntegral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    F a b = 4 * ∫ x in 0..rectangleRadius a b, ∫ y in 0..rectangleRadius a b, uniformDensity a b x y := by
  have hT : 0 ≤ rectangleRadius a b := by linarith [(rectangleRadius_bounds ha hb hab).1]
  simp only [F, intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo]

end Completion
end BlaschkeLebesgue
