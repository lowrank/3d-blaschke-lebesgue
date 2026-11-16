module

public import BlaschkeLebesgue.LongitudeRotation
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Uniform longitude on every spherical cap

Rotations fixing the pole preserve the restricted spherical measure. Its
longitude pushforward is therefore Haar measure on the angle circle, with
normalization fixed by the proved cap area.
-/

public noncomputable section

open MeasureTheory Measure Set Metric Filter
open scoped InnerProductSpace ENNReal

namespace BlaschkeLebesgue

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

theorem sphereMeasure_transverseComplex_zero :
    sphereMeasure {u : UnitSphere | transverseComplex u = 0} = 0 := by
  have hn : ‖(EuclideanSpace.single 1 1 : Space)‖ = 1 := by
    simp [EuclideanSpace.single, PiLp.norm_single]
  apply measure_mono_null (t := {u : UnitSphere |
    ⟪(EuclideanSpace.single 1 1 : Space), (u : Space)⟫_ℝ = 0}) _
    (sphereMeasure_inner_level_unit hn 0)
  intro u hu
  change transverseComplex u = 0 at hu
  have h := congrArg Complex.re hu
  simpa [transverseComplex, EuclideanSpace.inner_single_left] using h

@[expose] def longitudeCapMeasure (c : ℝ) : Measure (AddCircle (2 * Real.pi)) :=
  (sphereMeasure.restrict (sphereCap coordinatePole c)).map longitude

instance longitudeCapMeasure_finite (c : ℝ) : IsFiniteMeasure (longitudeCapMeasure c) := by
  unfold longitudeCapMeasure
  infer_instance

theorem longitudeRotation_preserves_cap (t c : ℝ) :
    MeasurePreserving (sphereIsometry (longitudeRotation t))
      (sphereMeasure.restrict (sphereCap coordinatePole c))
      (sphereMeasure.restrict (sphereCap coordinatePole c)) := by
  simpa only [longitudeRotation_pole] using
    sphereIsometry_measurePreserving_restrict_cap (longitudeRotation t) coordinatePole c

instance longitudeCapMeasure_invariant (c : ℝ) : IsAddLeftInvariant (longitudeCapMeasure c) where
  map_add_left_eq_self a := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
    change ((sphereMeasure.restrict (sphereCap coordinatePole c)).map longitude).map
      ((t : AddCircle (2 * Real.pi)) + ·) =
        (sphereMeasure.restrict (sphereCap coordinatePole c)).map longitude
    rw [Measure.map_map (g := fun x : AddCircle (2 * Real.pi) ↦ (t : AddCircle (2 * Real.pi)) + x)
      (by fun_prop) measurable_longitude]
    have hn : ∀ᵐ u : UnitSphere ∂sphereMeasure, transverseComplex u ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using sphereMeasure_transverseComplex_zero
    calc
      _ = (sphereMeasure.restrict (sphereCap coordinatePole c)).map
          (longitude ∘ sphereIsometry (longitudeRotation t)) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_of_ae hn] with u hu
        exact (longitude_rotate t u hu).symm
      _ = ((sphereMeasure.restrict (sphereCap coordinatePole c)).map
          (sphereIsometry (longitudeRotation t))).map longitude :=
        (Measure.map_map measurable_longitude (sphereIsometry (longitudeRotation t)).measurable).symm
      _ = _ := by rw [(longitudeRotation_preserves_cap t c).map_eq]

theorem longitudeCapMeasure_real_univ (c : ℝ) :
    (longitudeCapMeasure c).real univ = sphereMeasure.real (sphereCap coordinatePole c) := by
  rw [measureReal_def, longitudeCapMeasure, Measure.map_apply measurable_longitude MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply_univ, measureReal_def]

/-- Longitude is uniform, independently of the height cutoff defining the cap. -/
theorem longitudeCapMeasure_eq_smul {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    longitudeCapMeasure c = ENNReal.ofReal (1 - c) •
      (volume : Measure (AddCircle (2 * Real.pi))) := by
  let k := addHaarScalarFactor (longitudeCapMeasure c) (volume : Measure (AddCircle (2 * Real.pi)))
  have he : longitudeCapMeasure c = k • (volume : Measure (AddCircle (2 * Real.pi))) :=
    isAddInvariant_eq_smul_of_compactSpace _ _
  have hm := congrArg (fun μ : Measure (AddCircle (2 * Real.pi)) ↦ μ.real univ) he
  rw [longitudeCapMeasure_real_univ, sphereMeasure_real_cap_of_mem_Icc norm_coordinatePole hc,
    measureReal_nnreal_smul_apply, measureReal_def, AddCircle.measure_univ,
    ENNReal.toReal_ofReal (by positivity)] at hm
  have hk : (k : ℝ) = 1 - c := by nlinarith [Real.pi_pos]
  have hk' : (k : ℝ≥0∞) = ENNReal.ofReal (1 - c) := by
    rw [← hk, ENNReal.ofReal_coe_nnreal]
  change longitudeCapMeasure c = (k : ℝ≥0∞) • (volume : Measure (AddCircle (2 * Real.pi))) at he
  rwa [hk'] at he

theorem longitudeCapMeasure_eq_height_mass (c : ℝ) :
    longitudeCapMeasure c = ((volume.restrict (Icc (-1 : ℝ) 1)) (Ici c)) •
      (volume : Measure (AddCircle (2 * Real.pi))) := by
  have he : Ici c ∩ Icc (-1 : ℝ) 1 = Icc (max c (-1)) 1 := by
    ext z
    simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]
    tauto
  rw [Measure.restrict_apply measurableSet_Ici, he, Real.volume_Icc]
  by_cases hlo : c ≤ -1
  · have hcap : longitudeCapMeasure c = longitudeCapMeasure (-1) := by
      simp only [longitudeCapMeasure, sphereCap_eq_univ_of_le_neg_one norm_coordinatePole hlo,
        sphereCap_eq_univ_of_le_neg_one norm_coordinatePole (le_refl (-1 : ℝ))]
    rw [hcap, longitudeCapMeasure_eq_smul (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1), max_eq_right hlo]
  · rw [max_eq_left (le_of_not_ge hlo)]
    by_cases hhi : c ≤ 1
    · exact longitudeCapMeasure_eq_smul ⟨by linarith, hhi⟩
    · rw [longitudeCapMeasure, sphereCap_eq_empty_of_one_lt norm_coordinatePole (lt_of_not_ge hhi),
        Measure.restrict_empty, Measure.map_zero,
        ENNReal.ofReal_eq_zero.2 (show 1 - c ≤ 0 by linarith), zero_smul]

/-- Restricting longitude does not change the uniform distribution of height. -/
theorem sphereMeasure_map_height_restrict_longitude {s : Set (AddCircle (2 * Real.pi))}
    (hs : MeasurableSet s) :
    (sphereMeasure.restrict (longitude ⁻¹' s)).map
      (fun u : UnitSphere ↦ ⟪coordinatePole, (u : Space)⟫_ℝ) =
        (volume s) • volume.restrict (Icc (-1 : ℝ) 1) := by
  apply Measure.ext_of_Ici
  intro c
  have hm : Measurable (fun u : UnitSphere ↦ ⟪coordinatePole, (u : Space)⟫_ℝ) := by fun_prop
  rw [Measure.map_apply hm measurableSet_Ici,
    Measure.restrict_apply (measurableSet_Ici.preimage hm), Measure.smul_apply, smul_eq_mul]
  have h := congrArg (fun μ : Measure (AddCircle (2 * Real.pi)) ↦ μ s)
    (longitudeCapMeasure_eq_height_mass c)
  rw [longitudeCapMeasure, Measure.map_apply measurable_longitude hs,
    Measure.restrict_apply (hs.preimage measurable_longitude), Measure.smul_apply, smul_eq_mul] at h
  change sphereMeasure (sphereCap coordinatePole c ∩ longitude ⁻¹' s) = _
  rw [inter_comm, h, mul_comm]

/-- Spherical area in height and longitude coordinates is exactly product Lebesgue measure. -/
theorem sphereMeasure_map_height_longitude :
    sphereMeasure.map (fun u : UnitSphere ↦ (⟪coordinatePole, (u : Space)⟫_ℝ, longitude u)) =
      (volume.restrict (Icc (-1 : ℝ) 1)).prod
        (volume : Measure (AddCircle (2 * Real.pi))) := by
  apply Measure.ext_prod
  intro s t hs ht
  have hm : Measurable (fun u : UnitSphere ↦ ⟪coordinatePole, (u : Space)⟫_ℝ) := by fun_prop
  rw [Measure.map_apply (hm.prodMk measurable_longitude) (hs.prod ht), Measure.prod_prod]
  have h := congrArg (fun μ : Measure ℝ ↦ μ s) (sphereMeasure_map_height_restrict_longitude ht)
  rw [Measure.map_apply hm hs, Measure.restrict_apply (hs.preimage hm),
    Measure.smul_apply, smul_eq_mul] at h
  change sphereMeasure ((fun u : UnitSphere ↦ ⟪coordinatePole, (u : Space)⟫_ℝ) ⁻¹' s ∩
    longitude ⁻¹' t) = _
  rw [h, mul_comm]

@[expose] def longitudeSector (c : ℝ) (a : AddCircle (2 * Real.pi)) (r : ℝ) : Set UnitSphere :=
  sphereCap coordinatePole c ∩ longitude ⁻¹' closedBall a r

theorem measurableSet_longitudeSector (c : ℝ) (a : AddCircle (2 * Real.pi)) (r : ℝ) :
    MeasurableSet (longitudeSector c a r) :=
  (measurableSet_sphereCap _ _).inter (measurableSet_closedBall.preimage measurable_longitude)

/-- A cap sector of angular width `2r` has area `2r(1-c)`. -/
theorem sphereMeasure_longitudeSector {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1)
    (a : AddCircle (2 * Real.pi)) {r : ℝ} (hr : r ≤ Real.pi) :
    sphereMeasure (longitudeSector c a r) = ENNReal.ofReal (2 * r * (1 - c)) := by
  have h := congrArg (fun μ : Measure (AddCircle (2 * Real.pi)) ↦ μ (closedBall a r))
    (longitudeCapMeasure_eq_smul hc)
  rw [longitudeCapMeasure, Measure.map_apply measurable_longitude measurableSet_closedBall,
    Measure.restrict_apply (measurableSet_closedBall.preimage measurable_longitude),
    Measure.smul_apply, smul_eq_mul, AddCircle.volume_closedBall,
    min_eq_right (show 2 * r ≤ 2 * Real.pi by linarith),
    ← ENNReal.ofReal_mul (sub_nonneg.2 hc.2)] at h
  change sphereMeasure (sphereCap coordinatePole c ∩ longitude ⁻¹' closedBall a r) = _
  rw [inter_comm, h]
  congr 1
  ring

theorem sphereMeasure_real_longitudeSector {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1)
    (a : AddCircle (2 * Real.pi)) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ Real.pi) :
    sphereMeasure.real (longitudeSector c a r) = 2 * r * (1 - c) := by
  rw [measureReal_def, sphereMeasure_longitudeSector hc a hr,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (sub_nonneg.2 hc.2))]

end BlaschkeLebesgue
