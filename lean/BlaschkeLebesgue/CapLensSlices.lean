module

public import BlaschkeLebesgue.SphereCoordinates
public import BlaschkeLebesgue.LongitudeSlice

/-! # Latitude integration for intersections of two spherical caps -/

public noncomputable section

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace

namespace BlaschkeLebesgue

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

@[expose] def latitudeCapAxis (c : ℝ) : Space := !₂[c, Real.sqrt (1 - c ^ 2), 0]

@[expose] def latitudeCapThreshold (b c z : ℝ) : ℝ :=
  (b - c * z) / (Real.sqrt (1 - c ^ 2) * Real.sqrt (1 - z ^ 2))

theorem inner_latitudeCapAxis (c : ℝ) (x : Space) :
    ⟪latitudeCapAxis c, x⟫_ℝ = c * x 0 + Real.sqrt (1 - c ^ 2) * x 1 := by
  simp [latitudeCapAxis, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

theorem norm_latitudeCapAxis {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    ‖latitudeCapAxis c‖ = 1 := by
  have hs : 0 ≤ 1 - c ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc.2) (show 0 ≤ c + 1 by linarith [hc.1])]
  have he : ‖latitudeCapAxis c‖ ^ 2 = 1 := by
    simp [latitudeCapAxis, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Real.sq_sqrt hs]
  nlinarith [norm_nonneg (latitudeCapAxis c)]

theorem inner_latitudeCapAxis_heightLongitudePoint (c z : ℝ) (t : AddCircle (2 * Real.pi)) :
    ⟪latitudeCapAxis c, heightLongitudePoint z t⟫_ℝ =
      c * z + (Real.sqrt (1 - c ^ 2) * Real.sqrt (1 - z ^ 2)) * Real.Angle.cos t := by
  rw [inner_latitudeCapAxis, heightLongitudePoint_zero, heightLongitudePoint_one]
  ring

theorem latitudeCap_slice_iff {c z : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (b : ℝ) (t : AddCircle (2 * Real.pi)) :
    b ≤ ⟪latitudeCapAxis c, heightLongitudePoint z t⟫_ℝ ↔
      latitudeCapThreshold b c z ≤ Real.Angle.cos t := by
  have hc' : 0 < 1 - c ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hc.2) (show 0 < c + 1 by linarith [hc.1])]
  have hz' : 0 < 1 - z ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hz.2) (show 0 < z + 1 by linarith [hz.1])]
  rw [inner_latitudeCapAxis_heightLongitudePoint, latitudeCapThreshold,
    div_le_iff₀ (mul_pos (Real.sqrt_pos.2 hc') (Real.sqrt_pos.2 hz'))]
  constructor <;> intro h <;> nlinarith

theorem integral_latitudeCap_slice {c z : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (b w : ℝ) :
    (∫ t : AddCircle (2 * Real.pi),
      {t : AddCircle (2 * Real.pi) | b ≤ ⟪latitudeCapAxis c, heightLongitudePoint z t⟫_ℝ}.indicator
        (fun _ ↦ w) t) = 2 * Real.arccos (latitudeCapThreshold b c z) * w := by
  have he : {t : AddCircle (2 * Real.pi) | b ≤ ⟪latitudeCapAxis c, heightLongitudePoint z t⟫_ℝ} =
      {t : AddCircle (2 * Real.pi) | latitudeCapThreshold b c z ≤ Real.Angle.cos t} := by
    ext t
    exact latitudeCap_slice_iff hc hz b t
  have hm : Measurable (fun t : AddCircle (2 * Real.pi) ↦ Real.Angle.cos t) :=
    (show Continuous (fun t : AddCircle (2 * Real.pi) ↦ Real.Angle.cos t) from
      Real.Angle.continuous_cos).measurable
  rw [he, integral_indicator_const _
    (measurableSet_le measurable_const hm),
    volume_real_angle_cos_ge, smul_eq_mul]

/-- Every continuous function of height on a two-cap lens reduces to one real integral. -/
theorem integral_capLens_height {a c : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (b : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ u in sphereCap coordinatePole a ∩ sphereCap (latitudeCapAxis c) b,
      g ⟪coordinatePole, (u : Space)⟫_ℝ ∂sphereMeasure) =
      ∫ z in Icc a 1, 2 * Real.arccos (latitudeCapThreshold b c z) * g z := by
  classical
  let H : Set Space := {x | b ≤ ⟪latitudeCapAxis c, x⟫_ℝ}
  have hH : MeasurableSet H := measurableSet_le measurable_const
    (continuous_const.inner continuous_id).measurable
  let f : Space → ℝ := H.indicator (fun x ↦ g ⟪coordinatePole, x⟫_ℝ)
  have hm : StronglyMeasurable f :=
    (hg.comp (continuous_const.inner continuous_id)).stronglyMeasurable.indicator hH
  have hf (u : UnitSphere) : f (u : Space) = (sphereCap (latitudeCapAxis c) b).indicator
      (fun u : UnitSphere ↦ g ⟪coordinatePole, (u : Space)⟫_ℝ) u := by
    rfl
  have hi0 : Integrable (fun u : UnitSphere ↦ g ⟪coordinatePole, (u : Space)⟫_ℝ)
      sphereMeasure :=
    (hg.comp (continuous_const.inner continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun u : UnitSphere ↦ f (u : Space)) sphereMeasure := by
    simpa only [hf] using hi0.indicator (measurableSet_sphereCap (latitudeCapAxis c) b)
  have he : (∫ u in sphereCap coordinatePole a, f (u : Space) ∂sphereMeasure) =
      ∫ u in sphereCap coordinatePole a ∩ sphereCap (latitudeCapAxis c) b,
        g ⟪coordinatePole, (u : Space)⟫_ℝ ∂sphereMeasure := by
    simp_rw [hf]
    rw [setIntegral_indicator (measurableSet_sphereCap (latitudeCapAxis c) b), inter_comm]
  rw [← he, integral_sphereCap_heightLongitude_iterated ha hm hi.integrableOn]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (-1 : ℝ)), ae_restrict_of_ae (volume.ae_ne (1 : ℝ))]
    with z hz hz0 hz1
  have hz' : z ∈ Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (ha.1.trans hz.1) (Ne.symm hz0), lt_of_le_of_ne hz.2 hz1⟩
  have hf' (t : AddCircle (2 * Real.pi)) : f (heightLongitudePoint z t) =
      {t : AddCircle (2 * Real.pi) | b ≤ ⟪latitudeCapAxis c, heightLongitudePoint z t⟫_ℝ}.indicator
        (fun _ ↦ g z) t := by
    simp only [f, H, indicator_apply, mem_ofPred_eq, inner_coordinatePole,
      heightLongitudePoint_zero]
  simp_rw [hf']
  exact integral_latitudeCap_slice hc hz' b (g z)

theorem sphereMeasure_real_capLens {a c : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (b : ℝ) :
    sphereMeasure.real (sphereCap coordinatePole a ∩ sphereCap (latitudeCapAxis c) b) =
      ∫ z in Icc a 1, 2 * Real.arccos (latitudeCapThreshold b c z) := by
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using
    integral_capLens_height ha hc b (g := fun _ ↦ 1) continuous_const

theorem integral_capLens_inner_axis {a c : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1)
    (hc : c ∈ Ioo (-1 : ℝ) 1) (b : ℝ) :
    (∫ u in sphereCap coordinatePole a ∩ sphereCap (latitudeCapAxis c) b,
      ⟪coordinatePole, (u : Space)⟫_ℝ ∂sphereMeasure) =
      ∫ z in Icc a 1, 2 * Real.arccos (latitudeCapThreshold b c z) * z :=
  integral_capLens_height ha hc b continuous_id

end BlaschkeLebesgue
