module

public import BlaschkeLebesgue.SphericalMeasure
public import BlaschkeLebesgue.SliceVolume

/-!
# Exact area of spherical caps

Slice the unit cone at height `c`. Below that height its slices are disks in a
straight cone; above that height they are the slices of the unit ball. Their
polynomial volume integrals yield `2 * pi * (1 - c)` for spherical cap area.
-/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def coordinatePole : Space := EuclideanSpace.single 0 1

theorem norm_coordinatePole : ‖coordinatePole‖ = 1 := by
  simp [coordinatePole, EuclideanSpace.single, PiLp.norm_single]

theorem inner_coordinatePole (x : Space) : ⟪coordinatePole, x⟫_ℝ = x 0 := by
  simp [coordinatePole, EuclideanSpace.inner_single_left]

/-- The elementary scalar geometry underlying the two disk-slice regions. -/
theorem capCone_slice_iff {c n z w : ℝ} (hc : 0 < c)
    (hn : 0 ≤ n) (hw : 0 ≤ w) (hsq : n ^ 2 = z ^ 2 + w) :
    (n ≤ 1 ∧ c * n ≤ z) ↔
      (z ∈ Icc 0 c ∧ w ≤ (1 - c ^ 2) / c ^ 2 * z ^ 2) ∨
      (z ∈ Icc c 1 ∧ w ≤ 1 - z ^ 2) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hmul := congrArg (fun t : ℝ ↦ c ^ 2 * t) hsq
  constructor
  · rintro ⟨hn1, hcn⟩
    have hz : 0 ≤ z := (mul_nonneg hc.le hn).trans hcn
    have hzn : z ≤ n := by nlinarith only [hsq, hw, hn, hz]
    have hz1 : z ≤ 1 := hzn.trans hn1
    by_cases hzc : z ≤ c
    · left
      refine ⟨⟨hz, hzc⟩, ?_⟩
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc2).2
      have hsqcn := (sq_le_sq₀ (mul_nonneg hc.le hn) hz).2 hcn
      nlinarith only [hsqcn, hmul]
    · exact Or.inr ⟨⟨(lt_of_not_ge hzc).le, hz1⟩,
        by nlinarith only [hsq, hn, hn1]⟩
  · rintro (⟨⟨hz, hzc⟩, hwc⟩ | ⟨⟨hcz, hz1⟩, hw1⟩)
    · rw [div_mul_eq_mul_div] at hwc
      have hh := (le_div_iff₀ hc2).1 hwc
      have hcn : c * n ≤ z := by
        apply (sq_le_sq₀ (mul_nonneg hc.le hn) hz).1
        nlinarith only [hh, hmul]
      exact ⟨by nlinarith only [hc, hcn, hzc], hcn⟩
    · have hn1 : n ≤ 1 := by nlinarith only [hsq, hw1, hn]
      exact ⟨hn1, (mul_le_mul_of_nonneg_left hn1 hc.le).trans (by simpa using hcz)⟩

theorem capCone_coordinatePole_slices {c : ℝ} (hc : 0 < c) :
    capCone coordinatePole c = sliceEquiv ⁻¹'
      (diskSolid 0 c (fun z ↦ (1 - c ^ 2) / c ^ 2 * z ^ 2) ∪
        diskSolid c 1 (fun z ↦ 1 - z ^ 2)) := by
  ext x
  simp only [capCone, mem_ofPred_eq, inner_coordinatePole, mem_preimage,
    mem_union, diskSolid, sliceEquiv_fst]
  apply capCone_slice_iff hc (norm_nonneg _) (sq_nonneg _)
  simpa only [sliceEquiv_fst] using norm_sq_sliceEquiv x

theorem volume_capCone_coordinatePole {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    volume (capCone coordinatePole c) = ENNReal.ofReal (2 * Real.pi / 3 * (1 - c)) := by
  let f : ℝ → ℝ := fun z ↦ (1 - c ^ 2) / c ^ 2 * z ^ 2
  let g : ℝ → ℝ := fun z ↦ 1 - z ^ 2
  have hf : Continuous f := (continuous_id.pow 2).const_mul _
  have hg : Continuous g := continuous_const.sub (continuous_id.pow 2)
  have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith only [hc, hc1]
  have hfp : ∀ z ∈ Icc 0 c, 0 ≤ f z := by intros; dsimp [f]; positivity
  have hgp : ∀ z ∈ Icc c 1, 0 ≤ g z := by
    intro z hz
    dsimp [g]
    nlinarith only [hz.1, hz.2, hc]
  have hdisj : AEDisjoint volume (diskSolid 0 c f) (diskSolid c 1 g) := by
    apply measure_mono_null (t := ({c} : Set ℝ) ×ˢ (univ : Set SlicePlane))
    · intro p hp
      exact ⟨le_antisymm hp.1.1.2 hp.2.1.1, mem_univ _⟩
    · change volume.prod volume _ = 0
      simp
  rw [capCone_coordinatePole_slices hc,
    sliceEquiv_measurePreserving.measure_preimage
      ((measurableSet_diskSolid 0 c hf).union
        (measurableSet_diskSolid c 1 hg)).nullMeasurableSet,
    measure_union₀ (measurableSet_diskSolid c 1 hg).nullMeasurableSet hdisj,
    volume_diskSolid hc.le hf hfp, volume_diskSolid hc1 hg hgp]
  have hfint : (∫ z in 0..c, f z) = (1 - c ^ 2) / c ^ 2 * (c ^ 3 / 3) := by
    dsimp [f]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  have hgint : (∫ z in c..1, g z) = (2 / 3 : ℝ) - c + c ^ 3 / 3 := by
    dsimp [g]
    rw [intervalIntegral.integral_sub (intervalIntegrable_const)
      (intervalIntegral.intervalIntegrable_pow 2),
      intervalIntegral.integral_const, integral_pow]
    norm_num
    ring
  rw [hfint, hgint, ← ENNReal.ofReal_add]
  · congr 1
    field_simp
    ring
  · positivity
  · have hfactor : (2 / 3 : ℝ) - c + c ^ 3 / 3 = (1 - c) ^ 2 * (c + 2) / 3 := by ring
    rw [hfactor]
    positivity

/-- The exact cap area for every unit center and every positive height at most one. -/
theorem sphereMeasure_cap {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    sphereMeasure (sphereCap u c) = ENNReal.ofReal (2 * Real.pi * (1 - c)) := by
  let e : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ (u - coordinatePole))ᗮ.reflection
  have he : e u = coordinatePole := Submodule.reflection_sub (hu.trans norm_coordinatePole.symm)
  rw [← sphereMeasure_cap_isometry e u c, he, sphereMeasure_capCone,
    volume_capCone_coordinatePole hc hc1]
  calc
    3 * ENNReal.ofReal (2 * Real.pi / 3 * (1 - c)) =
        ENNReal.ofReal (3 * (2 * Real.pi / 3 * (1 - c))) := by
      have hh := ENNReal.ofReal_mul (show 0 ≤ (3 : ℝ) by norm_num)
        (q := 2 * Real.pi / 3 * (1 - c))
      simpa only [ENNReal.ofReal_ofNat] using hh.symm
    _ = ENNReal.ofReal (2 * Real.pi * (1 - c)) := by congr 1; ring

theorem sphereMeasure_real_cap {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    sphereMeasure.real (sphereCap u c) = 2 * Real.pi * (1 - c) := by
  rw [measureReal_def, sphereMeasure_cap hu hc hc1,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (sub_nonneg.2 hc1))]

end BlaschkeLebesgue
