module

public import BlaschkeLebesgue.RadialVolume
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Volume by planar disk slices

A solid whose squared slice radius is a nonnegative function has volume equal
to pi times the integral of that function. The measure here is the ordinary
product Lebesgue measure, and the disk area is mathlib's proved Euclidean area.
-/

public noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BlaschkeLebesgue

abbrev SlicePlane := EuclideanSpace ℝ (Fin 2)

@[expose] def diskSolid (a b : ℝ) (f : ℝ → ℝ) : Set (ℝ × SlicePlane) :=
  {p | p.1 ∈ Icc a b ∧ ‖p.2‖ ^ 2 ≤ f p.1}

theorem measurableSet_diskSolid (a b : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    MeasurableSet (diskSolid a b f) :=
  ((isClosed_Icc.preimage continuous_fst).inter
    (isClosed_le (continuous_snd.norm.pow 2) (hf.comp continuous_fst))).measurableSet

/-- Disk slicing, with no numerical approximation in the integral formula. -/
theorem volume_diskSolid {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f)
    (hpos : ∀ z ∈ Icc a b, 0 ≤ f z) :
    volume (diskSolid a b f) = ENNReal.ofReal (Real.pi * ∫ z in a..b, f z) := by
  have hsection (z : ℝ) :
      volume (Prod.mk z ⁻¹' diskSolid a b f) =
        (Icc a b).indicator (fun z ↦ ENNReal.ofReal (Real.pi * f z)) z := by
    by_cases hz : z ∈ Icc a b
    · rw [indicator_of_mem hz]
      have heq : Prod.mk z ⁻¹' diskSolid a b f = closedBall 0 (Real.sqrt (f z)) := by
        ext y
        simp only [diskSolid, mem_preimage, mem_ofPred_eq, hz, true_and,
          mem_closedBall, dist_zero_right, Real.le_sqrt (norm_nonneg _) (hpos z hz)]
      rw [heq, EuclideanSpace.volume_closedBall_fin_two,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hpos z hz),
        ← ENNReal.ofReal_mul (hpos z hz), mul_comm]
    · have heq : Prod.mk z ⁻¹' diskSolid a b f = ∅ := by
        ext y
        simp only [diskSolid, mem_preimage, mem_ofPred_eq, hz, false_and, mem_empty_iff_false]
      simp [heq, indicator_of_notMem hz]
  change volume.prod volume (diskSolid a b f) = _
  rw [Measure.prod_apply (measurableSet_diskSolid a b hf)]
  simp_rw [hsection]
  have hint : IntegrableOn (fun z ↦ Real.pi * f z) (Icc a b) volume :=
    (hf.const_mul Real.pi).integrableOn_Icc
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal hint,
    integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
  exact mul_nonneg Real.pi_pos.le (hpos z hz)

/-- Separate the first coordinate, preserving Lebesgue measure in both directions. -/
@[expose] def sliceEquiv : Space ≃ᵐ ℝ × SlicePlane :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem sliceEquiv_measurePreserving : MeasurePreserving sliceEquiv := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

theorem sliceEquiv_fst (x : Space) : (sliceEquiv x).1 = x 0 := rfl

theorem sliceEquiv_snd (x : Space) (i : Fin 2) : (sliceEquiv x).2 i = x i.succ := by
  simp [sliceEquiv, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodCongr, Fin.tail]

theorem norm_sq_sliceEquiv (x : Space) :
    ‖x‖ ^ 2 = (sliceEquiv x).1 ^ 2 + ‖(sliceEquiv x).2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ, sliceEquiv_fst]
  simp only [sliceEquiv_snd]

end BlaschkeLebesgue
