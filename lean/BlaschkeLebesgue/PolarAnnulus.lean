module

public import BlaschkeLebesgue.ShellParametrization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Polar integration on the Euclidean annulus

The ordinary three-dimensional Jacobian is `r²`. Both the integral identity and
integrability of the resulting spherical integral follow from the measure-
preserving polar homeomorphism and Fubini's theorem.
-/

public noncomputable section

open MeasureTheory Set Metric Filter

namespace BlaschkeLebesgue

theorem integral_radial_annulus (f : Space → ℝ) (u : UnitSphere) :
    (∫ r : Ioi (0 : ℝ), unitAnnulus.indicator f ((r : ℝ) • (u : Space))
      ∂Measure.volumeIoiPow 2) =
      ∫ r in (1 : ℝ)..2, r ^ 2 * f (r • (u : Space)) := by
  rw [Measure.volumeIoiPow]
  change (∫ r : Ioi (0 : ℝ), unitAnnulus.indicator f ((r : ℝ) • (u : Space))
    ∂(volume.comap Subtype.val).withDensity
      (fun r => (Real.toNNReal ((r : ℝ) ^ 2) : ENNReal))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_subtype_coe.pow_const 2).real_toNNReal)]
  simp_rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => r ^ 2 * unitAnnulus.indicator f (r • (u : Space)))]
  have he : ∀ r ∈ Ioi (0 : ℝ), r ^ 2 * unitAnnulus.indicator f (r • (u : Space)) =
      (Icc (1 : ℝ) 2).indicator (fun r => r ^ 2 * f (r • (u : Space))) r := by
    intro r hr
    have hm : r • (u : Space) ∈ unitAnnulus ↔ r ∈ Icc (1 : ℝ) 2 := by
      rw [mem_unitAnnulus_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        u.norm_eq_one, mul_one]
      rfl
    by_cases h : r ∈ Icc (1 : ℝ) 2
    · rw [indicator_of_mem (hm.2 h), indicator_of_mem h]
    · rw [indicator_of_notMem (fun hx => h (hm.1 hx)), indicator_of_notMem h, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Icc,
    inter_eq_right.2 (show Icc (1 : ℝ) 2 ⊆ Ioi 0 from
      fun _ hr => lt_of_lt_of_le zero_lt_one hr.1), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]

theorem integral_annulus_polar (f : Space → ℝ) (hf : IntegrableOn f unitAnnulus) :
    Integrable (fun u : UnitSphere => ∫ r in (1 : ℝ)..2, r ^ 2 * f (r • (u : Space)))
        sphereMeasure ∧
      (∫ x in unitAnnulus, f x) =
        ∫ u : UnitSphere, (∫ r in (1 : ℝ)..2, r ^ 2 * f (r • (u : Space))) ∂sphereMeasure := by
  let H := homeomorphUnitSphereProd Space
  let g : UnitSphere × Ioi (0 : ℝ) → ℝ := fun p =>
    unitAnnulus.indicator f (H.symm p).val
  have hdim : Module.finrank ℝ Space - 1 = 2 := by simp [Space]
  have hfi : Integrable (unitAnnulus.indicator f) volume :=
    (integrable_indicator_iff isCompact_unitAnnulus.measurableSet).2 hf
  have hfc : Integrable (fun x : ({0}ᶜ : Set Space) => unitAnnulus.indicator f x)
      (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hfi.integrableOn
  have hg : Integrable g (sphereMeasure.prod (Measure.volumeIoiPow 2)) := by
    have h := (volume : Measure Space).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (Homeomorph.measurableEmbedding _) (g := g)
    rw [hdim] at h
    apply h.mp
    simpa only [Function.comp_def, g, H, Homeomorph.symm_apply_apply] using hfc
  have hrad (u : UnitSphere) : (∫ r, g (u, r) ∂Measure.volumeIoiPow 2) =
      ∫ r in (1 : ℝ)..2, r ^ 2 * f (r • (u : Space)) := by
    simpa only [g, H, homeomorphUnitSphereProd_symm_apply_coe] using integral_radial_annulus f u
  refine ⟨hg.integral_prod_left.congr (Eventually.of_forall hrad), ?_⟩
  calc
    (∫ x in unitAnnulus, f x) = ∫ x, unitAnnulus.indicator f x := by
      rw [integral_indicator isCompact_unitAnnulus.measurableSet]
    _ = ∫ x : ({0}ᶜ : Set Space), unitAnnulus.indicator f x
        ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫ p, g p ∂sphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := (volume : Measure Space).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) g
      simpa only [g, H, Homeomorph.symm_apply_apply, sphereMeasure, hdim] using h
    _ = ∫ u : UnitSphere, (∫ r in (1 : ℝ)..2, r ^ 2 * f (r • (u : Space))) ∂sphereMeasure := by
      rw [integral_prod _ hg]
      exact integral_congr_ae (Eventually.of_forall hrad)

end BlaschkeLebesgue
