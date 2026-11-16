module

public import BlaschkeLebesgue.RadialFunction
public import BlaschkeLebesgue.Target
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Radial integration of ordinary volume

The measure on the unit sphere comes from Lebesgue measure by mathlib's polar
coordinate construction. Its normalization and the radial volume identity are
proved here for the actual convex body, including nonsmooth bodies.
-/

public noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BlaschkeLebesgue

/-- The unit sphere in the same Euclidean space used by the volume target. -/
abbrev UnitSphere := ↥(sphere (0 : Space) 1)

/-- Spherical area, with its normalization fixed by ordinary Lebesgue volume. -/
@[expose] def sphereMeasure : Measure UnitSphere := (volume : Measure Space).toSphere

instance : IsFiniteMeasure sphereMeasure := by
  unfold sphereMeasure
  infer_instance

theorem UnitSphere.norm_eq_one (u : UnitSphere) : ‖(u : Space)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using u.property

theorem UnitSphere.ne_zero (u : UnitSphere) : (u : Space) ≠ 0 := by
  intro h
  have := UnitSphere.norm_eq_one u
  simp [h] at this

theorem continuous_radialFunction_sphere {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    Continuous (fun u : UnitSphere ↦ radialFunction K u) := by
  exact (continuous_gauge K.convex (mem_interior_iff_mem_nhds.1 h0)).comp
    continuous_subtype_val |>.inv₀
      (fun u ↦ (body_gauge_pos h0 (UnitSphere.ne_zero u)).ne')

theorem sphereMeasure_univ : sphereMeasure univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [sphereMeasure, Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin,
    ENNReal.ofReal_one, one_pow, one_mul]
  calc
    3 * ENNReal.ofReal (Real.pi * 4 / 3) =
        ENNReal.ofReal (3 * (Real.pi * 4 / 3)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ = ENNReal.ofReal (4 * Real.pi) := by congr 1; ring

theorem sphereMeasure_real_univ : sphereMeasure.real univ = 4 * Real.pi := by
  rw [measureReal_def, sphereMeasure_univ, ENNReal.toReal_ofReal (by positivity)]

theorem integrable_radialFunction_pow {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) (n : ℕ) :
    Integrable (fun u : UnitSphere ↦ radialFunction K u ^ n) sphereMeasure := by
  exact ((continuous_radialFunction_sphere h0).pow n).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Polar coordinates express the body's Lebesgue measure as its radial subgraph. -/
theorem volume_eq_lintegral_radialFunction {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    volume (K : Set Space) =
      ∫⁻ u : UnitSphere, ENNReal.ofReal (radialFunction K u ^ 3 / 3) ∂sphereMeasure := by
  let U : Set (UnitSphere × Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) < radialFunction K p.1}
  have hU : MeasurableSet U :=
    (isOpen_lt (continuous_subtype_val.comp continuous_snd)
      ((continuous_radialFunction_sphere h0).comp continuous_fst)).measurableSet
  have hpre : homeomorphUnitSphereProd Space ⁻¹' U =
      (Subtype.val : ({0}ᶜ : Set Space) → Space) ⁻¹' interior (K : Set Space) := by
    ext x
    have hx := congrArg Subtype.val ((homeomorphUnitSphereProd Space).symm_apply_apply x)
    simp only [homeomorphUnitSphereProd_symm_apply_coe] at hx
    change (homeomorphUnitSphereProd Space x).2.val <
      radialFunction K (homeomorphUnitSphereProd Space x).1.val ↔ _
    rw [← smul_mem_interior_iff_lt_radialFunction h0
      (UnitSphere.ne_zero (homeomorphUnitSphereProd Space x).1)
      (homeomorphUnitSphereProd Space x).2.property.le, hx]
    rfl
  have himage : (Subtype.val : ({0}ᶜ : Set Space) → Space) ''
      (homeomorphUnitSphereProd Space ⁻¹' U) = interior (K : Set Space) \ {0} := by
    rw [hpre, Subtype.image_preimage_coe]
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_sdiff]
    exact and_comm
  have hpolar := (volume : Measure Space).measurePreserving_homeomorphUnitSphereProd
  have hdim : Module.finrank ℝ Space - 1 = 2 := by simp [Space]
  calc
    volume (K : Set Space) = volume (interior (K : Set Space) \ {0}) := by
      rw [measure_sdiff_null (measure_singleton _),
        measure_interior_of_null_frontier (K.convex.addHaar_frontier volume)]
    _ = (volume.comap (Subtype.val : ({0}ᶜ : Set Space) → Space))
        (homeomorphUnitSphereProd Space ⁻¹' U) := by
      rw [comap_subtype_coe_apply (measurableSet_singleton _).compl, himage]
    _ = sphereMeasure.prod (Measure.volumeIoiPow 2) U := by
      simpa only [sphereMeasure, hdim] using hpolar.measure_preimage hU.nullMeasurableSet
    _ = ∫⁻ u : UnitSphere, ENNReal.ofReal (radialFunction K u ^ 3 / 3)
        ∂sphereMeasure := by
      rw [Measure.prod_apply hU]
      apply lintegral_congr
      intro u
      let r : Ioi (0 : ℝ) := ⟨radialFunction K u, radialFunction_pos h0
        (UnitSphere.ne_zero u)⟩
      change Measure.volumeIoiPow 2 (Iio r) = _
      convert Measure.volumeIoiPow_apply_Iio 2 r using 1
      norm_num [r]

/-- The standard radial volume formula, for ordinary Lebesgue volume. -/
theorem bodyVolume_eq_integral_radialFunction {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    bodyVolume K = (∫ u : UnitSphere, radialFunction K u ^ 3 ∂sphereMeasure) / 3 := by
  rw [bodyVolume, volume_eq_lintegral_radialFunction h0,
    ← integral_eq_lintegral_of_nonneg_ae, integral_div]
  · exact Filter.Eventually.of_forall fun u ↦
      div_nonneg (pow_nonneg (radialFunction_pos h0 (UnitSphere.ne_zero u)).le _) (by norm_num)
  · exact ((continuous_radialFunction_sphere h0).pow 3 |>.div_const 3).aestronglyMeasurable

theorem integral_radialFunction_cube {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    (∫ u : UnitSphere, radialFunction K u ^ 3 ∂sphereMeasure) = 3 * bodyVolume K := by
  rw [bodyVolume_eq_integral_radialFunction h0]
  ring

end BlaschkeLebesgue
