module

public import BlaschkeLebesgue.LongitudeMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Reconstruction and integration in height-longitude coordinates -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

@[expose] def heightLongitudePoint (z : ℝ) (a : AddCircle (2 * Real.pi)) : Space :=
  !₂[z, Real.sqrt (1 - z ^ 2) * Real.Angle.cos a,
    Real.sqrt (1 - z ^ 2) * Real.Angle.sin a]

theorem heightLongitudePoint_zero (z : ℝ) (a : AddCircle (2 * Real.pi)) :
    heightLongitudePoint z a 0 = z := rfl

theorem heightLongitudePoint_one (z : ℝ) (a : AddCircle (2 * Real.pi)) :
    heightLongitudePoint z a 1 = Real.sqrt (1 - z ^ 2) * Real.Angle.cos a := rfl

theorem heightLongitudePoint_two (z : ℝ) (a : AddCircle (2 * Real.pi)) :
    heightLongitudePoint z a 2 = Real.sqrt (1 - z ^ 2) * Real.Angle.sin a := rfl

@[fun_prop] theorem continuous_heightLongitudePoint :
    Continuous (fun p : ℝ × AddCircle (2 * Real.pi) ↦ heightLongitudePoint p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × AddCircle (2 * Real.pi) ↦ Real.Angle.cos p.2) :=
    Real.Angle.continuous_cos.comp continuous_snd
  have hs : Continuous (fun p : ℝ × AddCircle (2 * Real.pi) ↦ Real.Angle.sin p.2) :=
    Real.Angle.continuous_sin.comp continuous_snd
  unfold heightLongitudePoint
  fun_prop

theorem norm_transverseComplex (u : UnitSphere) :
    ‖transverseComplex u‖ = Real.sqrt (1 - (u : Space) 0 ^ 2) := by
  have hn := u.norm_eq_one
  have hs := EuclideanSpace.real_norm_sq_eq (u : Space)
  rw [hn] at hs
  simp only [Fin.sum_univ_three, one_pow] at hs
  rw [Complex.norm_def]
  congr 1
  simp only [transverseComplex, Complex.normSq_apply, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, mul_one,
    zero_add, add_zero, sub_zero]
  nlinarith

/-- The coordinate reconstruction holds even at both poles. -/
theorem heightLongitudePoint_longitude (u : UnitSphere) :
    heightLongitudePoint ⟪coordinatePole, (u : Space)⟫_ℝ (longitude u) = (u : Space) := by
  rw [inner_coordinatePole]
  ext i
  fin_cases i
  · rfl
  · change Real.sqrt (1 - (u : Space) 0 ^ 2) * Real.Angle.cos (longitude u) = (u : Space) 1
    rw [← norm_transverseComplex]
    change ‖transverseComplex u‖ * Real.cos (transverseComplex u).arg = (u : Space) 1
    rw [Complex.norm_mul_cos_arg]
    simp [transverseComplex]
  · change Real.sqrt (1 - (u : Space) 0 ^ 2) * Real.Angle.sin (longitude u) = (u : Space) 2
    rw [← norm_transverseComplex]
    change ‖transverseComplex u‖ * Real.sin (transverseComplex u).arg = (u : Space) 2
    rw [Complex.norm_mul_sin_arg]
    simp [transverseComplex]

theorem norm_heightLongitudePoint {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1)
    (a : AddCircle (2 * Real.pi)) : ‖heightLongitudePoint z a‖ = 1 := by
  have hs : 0 ≤ 1 - z ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hz.2) (show 0 ≤ z + 1 by linarith [hz.1])]
  have he : ‖heightLongitudePoint z a‖ ^ 2 = 1 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
      heightLongitudePoint_zero, heightLongitudePoint_one, heightLongitudePoint_two, mul_pow]
    rw [Real.sq_sqrt hs]
    linear_combination (1 - z ^ 2) * Real.Angle.cos_sq_add_sin_sq a
  nlinarith [norm_nonneg (heightLongitudePoint z a)]

/-- Pull an ambient integrand back to the exact product coordinate measure. -/
theorem integral_sphere_heightLongitude {f : Space → ℝ} (hf : StronglyMeasurable f) :
    (∫ u : UnitSphere, f (u : Space) ∂sphereMeasure) =
      ∫ p : ℝ × AddCircle (2 * Real.pi), f (heightLongitudePoint p.1 p.2)
        ∂((volume.restrict (Icc (-1 : ℝ) 1)).prod volume) := by
  rw [← sphereMeasure_map_height_longitude,
    integral_map (f := fun p : ℝ × AddCircle (2 * Real.pi) ↦ f (heightLongitudePoint p.1 p.2))
      ((continuous_const.inner continuous_subtype_val).measurable.prodMk
        measurable_longitude).aemeasurable
      (hf.comp_measurable continuous_heightLongitudePoint.measurable).aestronglyMeasurable]
  simp only [heightLongitudePoint_longitude]

theorem integrable_heightLongitude_iff {f : Space → ℝ} (hf : StronglyMeasurable f) :
    Integrable (fun p : ℝ × AddCircle (2 * Real.pi) ↦ f (heightLongitudePoint p.1 p.2))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod volume) ↔
      Integrable (fun u : UnitSphere ↦ f (u : Space)) sphereMeasure := by
  rw [← sphereMeasure_map_height_longitude,
    integrable_map_measure
      (g := fun p : ℝ × AddCircle (2 * Real.pi) ↦ f (heightLongitudePoint p.1 p.2))
      (hf.comp_measurable continuous_heightLongitudePoint.measurable).aestronglyMeasurable
      ((continuous_const.inner continuous_subtype_val).measurable.prodMk
        measurable_longitude).aemeasurable]
  change Integrable (fun u : UnitSphere ↦
    f (heightLongitudePoint ⟪coordinatePole, (u : Space)⟫_ℝ (longitude u))) sphereMeasure ↔ _
  simp only [heightLongitudePoint_longitude]

theorem integral_sphere_heightLongitude_iterated {f : Space → ℝ} (hf : StronglyMeasurable f)
    (hi : Integrable (fun u : UnitSphere ↦ f (u : Space)) sphereMeasure) :
    (∫ u : UnitSphere, f (u : Space) ∂sphereMeasure) =
      ∫ z in Icc (-1 : ℝ) 1, ∫ a : AddCircle (2 * Real.pi), f (heightLongitudePoint z a) := by
  rw [integral_sphere_heightLongitude hf,
    integral_prod _ ((integrable_heightLongitude_iff hf).2 hi)]

theorem sphereMeasure_cap_map_height_longitude {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    (sphereMeasure.restrict (sphereCap coordinatePole c)).map
        (fun u : UnitSphere ↦ (⟪coordinatePole, (u : Space)⟫_ℝ, longitude u)) =
      (volume.restrict (Icc c 1)).prod (volume : Measure (AddCircle (2 * Real.pi))) := by
  have hm : Measurable (fun u : UnitSphere ↦ (⟪coordinatePole, (u : Space)⟫_ℝ, longitude u)) :=
    (continuous_const.inner continuous_subtype_val).measurable.prodMk measurable_longitude
  have he : (fun u : UnitSphere ↦ (⟪coordinatePole, (u : Space)⟫_ℝ, longitude u)) ⁻¹'
      ((Ici c) ×ˢ (univ : Set (AddCircle (2 * Real.pi)))) = sphereCap coordinatePole c := by
    ext u
    simp [sphereCap]
  rw [← he, ← Measure.restrict_map hm (measurableSet_Ici.prod MeasurableSet.univ),
    sphereMeasure_map_height_longitude, ← Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_restrict measurableSet_Ici]
  have hi : Ici c ∩ Icc (-1 : ℝ) 1 = Icc c 1 := by
    ext z
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hc.1.trans h.1, h.2⟩⟩
  rw [hi]

theorem integral_sphereCap_heightLongitude {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1)
    {f : Space → ℝ} (hf : StronglyMeasurable f) :
    (∫ u in sphereCap coordinatePole c, f (u : Space) ∂sphereMeasure) =
      ∫ p : ℝ × AddCircle (2 * Real.pi), f (heightLongitudePoint p.1 p.2)
        ∂((volume.restrict (Icc c 1)).prod volume) := by
  rw [← sphereMeasure_cap_map_height_longitude hc,
    integral_map (f := fun p : ℝ × AddCircle (2 * Real.pi) ↦ f (heightLongitudePoint p.1 p.2))
      ((continuous_const.inner continuous_subtype_val).measurable.prodMk
        measurable_longitude).aemeasurable
      (hf.comp_measurable continuous_heightLongitudePoint.measurable).aestronglyMeasurable]
  simp only [heightLongitudePoint_longitude]

theorem integrable_cap_heightLongitude_iff {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1)
    {f : Space → ℝ} (hf : StronglyMeasurable f) :
    Integrable (fun p : ℝ × AddCircle (2 * Real.pi) ↦ f (heightLongitudePoint p.1 p.2))
      ((volume.restrict (Icc c 1)).prod volume) ↔
      IntegrableOn (fun u : UnitSphere ↦ f (u : Space)) (sphereCap coordinatePole c)
        sphereMeasure := by
  rw [← sphereMeasure_cap_map_height_longitude hc,
    integrable_map_measure
      (g := fun p : ℝ × AddCircle (2 * Real.pi) ↦ f (heightLongitudePoint p.1 p.2))
      (hf.comp_measurable continuous_heightLongitudePoint.measurable).aestronglyMeasurable
      ((continuous_const.inner continuous_subtype_val).measurable.prodMk
        measurable_longitude).aemeasurable]
  change Integrable (fun u : UnitSphere ↦
    f (heightLongitudePoint ⟪coordinatePole, (u : Space)⟫_ℝ (longitude u))) _ ↔ _
  simp only [heightLongitudePoint_longitude, IntegrableOn]

theorem integral_sphereCap_heightLongitude_iterated {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1)
    {f : Space → ℝ} (hf : StronglyMeasurable f)
    (hi : IntegrableOn (fun u : UnitSphere ↦ f (u : Space)) (sphereCap coordinatePole c)
      sphereMeasure) :
    (∫ u in sphereCap coordinatePole c, f (u : Space) ∂sphereMeasure) =
      ∫ z in Icc c 1, ∫ a : AddCircle (2 * Real.pi), f (heightLongitudePoint z a) := by
  rw [integral_sphereCap_heightLongitude hc hf,
    integral_prod _ ((integrable_cap_heightLongitude_iff hc hf).2 hi)]

end BlaschkeLebesgue
