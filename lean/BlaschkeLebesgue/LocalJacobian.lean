module

public import BlaschkeLebesgue.LipschitzJacobian

/-!
# A Jacobian formula localized to the integration domain

For shell parametrizations, Lipschitz continuity and injectivity are needed only
on the compact annulus being integrated. The exceptional differentiability set
can likewise be discarded relative to that domain.
-/

public noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace BlaschkeLebesgue

theorem lipschitzOn_image_volume_zero {f : Space → Space} {C : ℝ≥0} {s : Set Space}
    (hf : LipschitzOnWith C f s) (hs : volume s = 0) : volume (f '' s) = 0 := by
  let μ : Measure Space := Measure.hausdorffMeasure (Module.finrank ℝ Space)
  have hμ : μ s = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure μ volume) hs
  apply Measure.absolutelyContinuous_isAddHaarMeasure volume μ
  apply le_antisymm _ zero_le
  have h := hf.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ Module.finrank ℝ Space)
  change μ (f '' s) ≤ (C : ENNReal) ^ (Module.finrank ℝ Space : ℝ) * μ s at h
  simpa only [hμ, mul_zero] using h

theorem lipschitzOn_image_ae_eq {f : Space → Space} {C : ℝ≥0} {s t u : Set Space}
    (hf : LipschitzOnWith C f s) (ht : t ⊆ s) (hu : u ⊆ s) (htu : t =ᵐ[volume] u) :
    f '' t =ᵐ[volume] f '' u := by
  apply ae_eq_set.2
  constructor
  · apply measure_mono_null ?_ (lipschitzOn_image_volume_zero
      (hf.mono (sdiff_subset.trans ht)) (ae_eq_set.1 htu).1)
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, fun hxu => hy ⟨x, hxu, rfl⟩⟩, rfl⟩
  · apply measure_mono_null ?_ (lipschitzOn_image_volume_zero
      (hf.mono (sdiff_subset.trans hu)) (ae_eq_set.1 htu).2)
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, fun hxt => hy ⟨x, hxt, rfl⟩⟩, rfl⟩

/-- Change of variables with hypotheses only on the actual compact integration domain. -/
theorem integral_abs_det_of_lipschitzOn_injOn {f : Space → Space}
    {f' : Space → Space →L[ℝ] Space} {C : ℝ≥0} {s : Set Space}
    (hs : IsCompact s) (hf : LipschitzOnWith C f s) (hinj : InjOn f s)
    (hd : ∀ᵐ x ∂volume.restrict s, HasFDerivAt f (f' x) x) :
    IntegrableOn (fun x => |(f' x).det|) s ∧
      (∫ x in s, |(f' x).det|) = (volume (f '' s)).toReal := by
  let g := s ∩ {x | HasFDerivAt f (f' x) x}
  have hgae : g =ᵐ[volume] s := by
    filter_upwards [(ae_restrict_iff' hs.measurableSet).1 hd] with x hx
    exact propext ⟨And.left, fun hxs => ⟨hxs, hx hxs⟩⟩
  have hgnull : NullMeasurableSet g volume := hs.measurableSet.nullMeasurableSet.congr hgae.symm
  obtain ⟨u, hug, hu, huae⟩ := hgnull.exists_measurable_subset_ae_eq
  have hus : u ⊆ s := hug.trans inter_subset_left
  have huae' : u =ᵐ[volume] s := huae.trans hgae
  have himae := lipschitzOn_image_ae_eq hf hus (Subset.refl s) huae'
  have hdu : ∀ x ∈ u, HasFDerivWithinAt f (f' x) u x :=
    fun x hx => (hug hx).2.hasFDerivWithinAt
  have hi : IntegrableOn (fun _ : Space => (1 : ℝ)) (f '' u) :=
    integrableOn_const (measure_ne_top_of_subset (image_mono hus)
      (hs.image_of_continuousOn hf.continuousOn).measure_ne_top)
  have hint := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hu hdu (hinj.mono hus) (fun _ : Space => (1 : ℝ))).1 hi
  simp only [smul_eq_mul, mul_one] at hint
  refine ⟨(integrableOn_congr_set_ae huae').1 hint, ?_⟩
  have heq := integral_image_eq_integral_abs_det_fderiv_smul
    volume hu hdu (hinj.mono hus) (fun _ : Space => (1 : ℝ))
  simp only [smul_eq_mul, mul_one, integral_const, Measure.real,
    Measure.restrict_apply_univ] at heq
  rw [← setIntegral_congr_set huae', ← heq, measure_congr himae]

end BlaschkeLebesgue
