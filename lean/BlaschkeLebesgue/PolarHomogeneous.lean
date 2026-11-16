module

public import BlaschkeLebesgue.RadialVolume

/-!
# Integrating degree-zero homogeneous functions

Polar coordinates identify the integral over the unit ball with one third of
the spherical integral. The statement uses Bochner integrals and remains valid
with their standard value zero when the function is not integrable.
-/

public noncomputable section

open MeasureTheory Set Metric Filter

namespace BlaschkeLebesgue

theorem integral_ball_homogeneous_zero (f : Space → ℝ)
    (hf : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = f x) :
    (∫ x in ball (0 : Space) 1, f x) = (∫ u : UnitSphere, f u ∂sphereMeasure) / 3 := by
  let H := homeomorphUnitSphereProd Space
  let g : UnitSphere × Ioi (0 : ℝ) → ℝ := fun p =>
    (ball (0 : Space) 1).indicator f (H.symm p).val
  let r₁ : Ioi (0 : ℝ) := ⟨1, zero_lt_one⟩
  have hdim : Module.finrank ℝ Space - 1 = 2 := by simp [Space]
  have hg (p : UnitSphere × Ioi (0 : ℝ)) :
      g p = f p.1 * (Iio r₁).indicator (fun _ => (1 : ℝ)) p.2 := by
    have hn : ‖(p.2 : ℝ) • (p.1 : Space)‖ = p.2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.property, p.1.norm_eq_one, mul_one]
    have hm : (p.2 : ℝ) • (p.1 : Space) ∈ ball (0 : Space) 1 ↔ p.2 ∈ Iio r₁ := by
      simp only [mem_ball, dist_zero_right, hn, mem_Iio, r₁]
      rfl
    change (ball (0 : Space) 1).indicator f ((H.symm p).val) = _
    rw [homeomorphUnitSphereProd_symm_apply_coe]
    by_cases hp : p.2 ∈ Iio r₁
    · rw [indicator_of_mem (hm.2 hp), indicator_of_mem hp, mul_one, hf _ p.2.property]
    · rw [indicator_of_notMem (fun h => hp (hm.1 h)), indicator_of_notMem hp, mul_zero]
  calc
    (∫ x in ball (0 : Space) 1, f x) = ∫ x, (ball (0 : Space) 1).indicator f x := by
      rw [integral_indicator measurableSet_ball]
    _ = ∫ x : ({0}ᶜ : Set Space), (ball (0 : Space) 1).indicator f x
        ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫ p, g p ∂sphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := (volume : Measure Space).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) g
      simpa only [g, H, Homeomorph.symm_apply_apply, sphereMeasure, hdim] using h
    _ = (∫ u : UnitSphere, f u ∂sphereMeasure) *
        ∫ r, (Iio r₁).indicator (fun _ => (1 : ℝ)) r ∂Measure.volumeIoiPow 2 := by
      simp_rw [hg]
      exact integral_prod_mul (fun u : UnitSphere => f u)
        ((Iio r₁).indicator (fun _ : Ioi (0 : ℝ) => (1 : ℝ)))
    _ = _ := by
      rw [integral_indicator measurableSet_Iio, integral_const, measureReal_def,
        Measure.restrict_apply_univ, Measure.volumeIoiPow_apply_Iio]
      norm_num [r₁, smul_eq_mul, div_eq_mul_inv]

theorem integral_closedBall_homogeneous_zero (f : Space → ℝ)
    (hf : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = f x) :
    (∫ x in closedBall (0 : Space) 1, f x) =
      (∫ u : UnitSphere, f u ∂sphereMeasure) / 3 := by
  have hn : ∀ᵐ x ∂(volume : Measure Space), x ∉ sphere (0 : Space) 1 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using Measure.addHaar_sphere volume (0 : Space) 1
  have he : closedBall (0 : Space) 1 =ᵐ[volume] ball (0 : Space) 1 := by
    filter_upwards [hn] with x hx
    simp only [mem_sphere, dist_zero_right] at hx
    simp only [mem_closedBall, mem_ball, dist_zero_right]
    exact propext (le_iff_lt_or_eq.trans (or_iff_left hx))
  rw [setIntegral_congr_set he]
  exact integral_ball_homogeneous_zero f hf

end BlaschkeLebesgue
