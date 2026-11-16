module

public import BlaschkeLebesgue.ParallelInverse
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Change of variables with an almost-everywhere derivative

Lipschitz maps send Lebesgue null sets to null sets. This allows the Jacobian
formula to be applied on a measurable full-measure differentiability set,
without losing any volume in its image.
-/

public noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace BlaschkeLebesgue

theorem lipschitz_image_volume_zero {f : Space → Space} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s : Set Space} (hs : volume s = 0) :
    volume (f '' s) = 0 := by
  let μ : Measure Space := Measure.hausdorffMeasure (Module.finrank ℝ Space)
  have hμ : μ s = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure μ volume) hs
  apply Measure.absolutelyContinuous_isAddHaarMeasure volume μ
  apply le_antisymm _ zero_le
  have h := hf.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ Module.finrank ℝ Space) s
  change μ (f '' s) ≤ (C : ENNReal) ^ (Module.finrank ℝ Space : ℝ) * μ s at h
  simpa only [hμ, mul_zero] using h

theorem lipschitz_image_ae_eq {f : Space → Space} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s t : Set Space} (hst : s =ᵐ[volume] t) :
    f '' s =ᵐ[volume] f '' t := by
  apply ae_eq_set.2
  constructor
  · apply measure_mono_null ?_ (lipschitz_image_volume_zero hf (ae_eq_set.1 hst).1)
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, fun hxt => hy ⟨x, hxt, rfl⟩⟩, rfl⟩
  · apply measure_mono_null ?_ (lipschitz_image_volume_zero hf (ae_eq_set.1 hst).2)
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, fun hxs => hy ⟨x, hxs, rfl⟩⟩, rfl⟩

/-- A compact-domain Jacobian formula requiring differentiability only almost everywhere. -/
theorem integral_abs_det_of_lipschitz_injective {f : Space → Space}
    {f' : Space → Space →L[ℝ] Space} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hinj : Function.Injective f) {s : Set Space} (hs : IsCompact s)
    (hd : ∀ᵐ x ∂(volume : Measure Space), HasFDerivAt f (f' x) x) :
    IntegrableOn (fun x => |(f' x).det|) s ∧
      (∫ x in s, |(f' x).det|) = (volume (f '' s)).toReal := by
  let g := {x | HasFDerivAt f (f' x) x}
  have hgae : g =ᵐ[volume] univ := ae_eq_univ.2 hd
  have hgnull : NullMeasurableSet g volume := nullMeasurableSet_univ.congr hgae.symm
  obtain ⟨u, hug, hu, huae⟩ := hgnull.exists_measurable_subset_ae_eq
  have huae' : u =ᵐ[volume] univ := huae.trans hgae
  have hsuae : s ∩ u =ᵐ[volume] s := by
    filter_upwards [huae'] with x hx
    simp_all only [mem_univ, mem_inter_iff, and_true]
  have himae := lipschitz_image_ae_eq hf hsuae
  have hsu := hs.measurableSet.inter hu
  have hdu : ∀ x ∈ s ∩ u, HasFDerivWithinAt f (f' x) (s ∩ u) x :=
    fun x hx => (hug hx.2).hasFDerivWithinAt
  have hi : IntegrableOn (fun _ : Space => (1 : ℝ)) (f '' (s ∩ u)) :=
    integrableOn_const (measure_ne_top_of_subset (image_mono inter_subset_left)
      (hs.image hf.continuous).measure_ne_top)
  have hint := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hsu hdu hinj.injOn (fun _ : Space => (1 : ℝ))).1 hi
  simp only [smul_eq_mul, mul_one] at hint
  refine ⟨(integrableOn_congr_set_ae hsuae).1 hint, ?_⟩
  have heq := integral_image_eq_integral_abs_det_fderiv_smul
    volume hsu hdu hinj.injOn (fun _ : Space => (1 : ℝ))
  simp only [smul_eq_mul, mul_one, integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ] at heq
  rw [← setIntegral_congr_set hsuae, ← heq, measure_congr himae]

/-- A lower Lipschitz estimate passes to every existing derivative. -/
theorem norm_le_mul_fderiv_of_antilipschitz {f : Space → Space}
    {A : Space →L[ℝ] Space} {C : ℝ≥0} {x : Space}
    (hf : AntilipschitzWith C f) (hd : HasFDerivAt f A x) (v : Space) :
    ‖v‖ ≤ C * ‖A v‖ := by
  apply ge_of_tendsto (hd.lim_real v |>.norm.const_mul (C : ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have h := hf.le_mul_dist (x + r⁻¹ • v) x
  simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr] at h ⊢
  have h' := mul_le_mul_of_nonneg_left h hr.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_comm r (C : ℝ)] using h'

theorem fderiv_injective_of_antilipschitz {f : Space → Space}
    {A : Space →L[ℝ] Space} {C : ℝ≥0} {x : Space}
    (hf : AntilipschitzWith C f) (hd : HasFDerivAt f A x) : Function.Injective A := by
  intro v w hvw
  apply sub_eq_zero.1
  apply norm_eq_zero.1
  have h := norm_le_mul_fderiv_of_antilipschitz hf hd (v - w)
  rw [map_sub, hvw, sub_self, norm_zero, mul_zero] at h
  exact le_antisymm h (norm_nonneg _)

end BlaschkeLebesgue
