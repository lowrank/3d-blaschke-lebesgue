module

public import BlaschkeLebesgue.CapBoundaries
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Uniform distribution of height on the two-sphere

The exact cap areas determine the pushforward of spherical measure under a
unit linear coordinate. This gives one-dimensional formulas for all integrable
functions of height and, in particular, exact cap first moments.
-/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

/-- Spherical height has constant density `2 pi` on `[-1,1]`. -/
theorem sphereMeasure_map_height {u : Space} (hu : ‖u‖ = 1) :
    sphereMeasure.map (fun v : UnitSphere ↦ ⟪u, (v : Space)⟫_ℝ) =
      ENNReal.ofReal (2 * Real.pi) • (volume.restrict (Icc (-1 : ℝ) 1)) := by
  apply Measure.ext_of_Ici
  intro c
  rw [Measure.map_apply (continuous_const.inner continuous_subtype_val).measurable measurableSet_Ici,
    Measure.smul_apply, Measure.restrict_apply measurableSet_Ici, smul_eq_mul]
  change sphereMeasure (sphereCap u c) = _
  have he : Ici c ∩ Icc (-1 : ℝ) 1 = Icc (max c (-1)) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]
    tauto
  rw [he, Real.volume_Icc]
  by_cases hlo : c ≤ -1
  · have hs : sphereCap u c = univ := by
      apply eq_univ_of_forall
      intro v
      have h := (abs_le.1 (abs_real_inner_le_norm u (v : Space))).1
      rw [hu, v.norm_eq_one, mul_one] at h
      exact hlo.trans h
    rw [hs, sphereMeasure_univ, max_eq_right hlo, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · rw [max_eq_left (le_of_not_ge hlo)]
    by_cases hhi : c ≤ 1
    · rw [← ofReal_measureReal, sphereMeasure_real_cap_of_mem_Icc hu ⟨by linarith, hhi⟩,
        ← ENNReal.ofReal_mul (by positivity)]
    · have hs : sphereCap u c = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        intro v hv
        have h := (abs_le.1 (abs_real_inner_le_norm u (v : Space))).2
        rw [hu, v.norm_eq_one, mul_one] at h
        exact hhi (hv.trans h)
      rw [hs, measure_empty, ENNReal.ofReal_eq_zero.2 (show 1 - c ≤ 0 by linarith), mul_zero]

theorem integral_sphere_height {u : Space} (hu : ‖u‖ = 1) {f : ℝ → ℝ}
    (hf : StronglyMeasurable f) :
    (∫ v : UnitSphere, f ⟪u, (v : Space)⟫_ℝ ∂sphereMeasure) =
      2 * Real.pi * ∫ z in Icc (-1 : ℝ) 1, f z := by
  rw [← integral_map (continuous_const.inner continuous_subtype_val).measurable.aemeasurable
    hf.aestronglyMeasurable, sphereMeasure_map_height hu, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem integral_sphereCap_height {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : c ∈ Icc (-1 : ℝ) 1) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    (∫ v in sphereCap u c, f ⟪u, (v : Space)⟫_ℝ ∂sphereMeasure) =
      2 * Real.pi * ∫ z in Icc c 1, f z := by
  have hmap := setIntegral_map (μ := sphereMeasure) (s := Ici c)
    (g := fun v : UnitSphere ↦ ⟪u, (v : Space)⟫_ℝ) measurableSet_Ici
    (f := f) hf.aestronglyMeasurable
    (continuous_const.inner continuous_subtype_val).measurable.aemeasurable
  change (∫ z in Ici c, f z ∂sphereMeasure.map (fun v : UnitSphere ↦ ⟪u, (v : Space)⟫_ℝ)) =
    ∫ v in sphereCap u c, f ⟪u, (v : Space)⟫_ℝ ∂sphereMeasure at hmap
  rw [← hmap, sphereMeasure_map_height hu, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul, Measure.restrict_restrict measurableSet_Ici]
  have he : Ici c ∩ Icc (-1 : ℝ) 1 = Icc c 1 := by
    ext z
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hc.1.trans h.1, h.2⟩⟩
  rw [he]

/-- The first moment along the cap axis, including hemispheres and both poles. -/
theorem integral_sphereCap_inner_self {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : c ∈ Icc (-1 : ℝ) 1) :
    (∫ v in sphereCap u c, ⟪u, (v : Space)⟫_ℝ ∂sphereMeasure) = Real.pi * (1 - c ^ 2) := by
  rw [integral_sphereCap_height hu hc (f := fun z : ℝ ↦ z) continuous_id.stronglyMeasurable,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc.2, integral_id]
  ring

end BlaschkeLebesgue
