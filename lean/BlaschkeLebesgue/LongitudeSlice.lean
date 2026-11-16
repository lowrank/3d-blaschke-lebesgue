module

public import BlaschkeLebesgue.LongitudeMeasure

/-! # Exact angular measure of a latitude slice of a cap -/

public noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BlaschkeLebesgue

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

theorem norm_angle_eq_abs_toReal (a : AddCircle (2 * Real.pi)) :
    ‖a‖ = |Real.Angle.toReal a| := by
  have h := (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)
    (x := Real.Angle.toReal a)).2 (by
      simpa only [abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_div_cancel_left₀ _
        (two_ne_zero : (2 : ℝ) ≠ 0)] using Real.Angle.abs_toReal_le_pi a)
  have he : ((Real.Angle.toReal a : ℝ) : AddCircle (2 * Real.pi)) = a :=
    Real.Angle.coe_toReal a
  rwa [he] at h

theorem le_angle_cos_iff_mem_closedBall {q : ℝ} (hq : q ∈ Icc (-1 : ℝ) 1)
    (a : AddCircle (2 * Real.pi)) :
    q ≤ Real.Angle.cos a ↔ a ∈ closedBall 0 (Real.arccos q) := by
  rw [mem_closedBall, dist_zero_right, norm_angle_eq_abs_toReal]
  calc
    q ≤ Real.Angle.cos a ↔ Real.cos (Real.arccos q) ≤ Real.cos |Real.Angle.toReal a| := by
      rw [Real.cos_arccos hq.1 hq.2, Real.cos_abs, Real.Angle.cos_toReal a]
    _ ↔ |Real.Angle.toReal a| ≤ Real.arccos q :=
      Real.strictAntiOn_cos.le_iff_ge ⟨Real.arccos_nonneg q, Real.arccos_le_pi q⟩
        ⟨abs_nonneg _, Real.Angle.abs_toReal_le_pi a⟩

/-- The clamped inverse cosine gives the slice length for every real cutoff. -/
theorem volume_angle_cos_ge (q : ℝ) :
    volume {a : AddCircle (2 * Real.pi) | q ≤ Real.Angle.cos a} =
      ENNReal.ofReal (2 * Real.arccos q) := by
  by_cases hlo : q < -1
  · have he : {a : AddCircle (2 * Real.pi) | q ≤ Real.Angle.cos a} = univ := by
      apply eq_univ_of_forall
      intro a
      change q ≤ Real.Angle.cos a
      rw [← Real.Angle.cos_toReal a]
      exact hlo.le.trans (Real.neg_one_le_cos _)
    rw [he, AddCircle.measure_univ, Real.arccos_eq_pi.2 hlo.le]
  · by_cases hhi : 1 < q
    · have he : {a : AddCircle (2 * Real.pi) | q ≤ Real.Angle.cos a} = ∅ := by
        apply eq_empty_iff_forall_notMem.2
        intro a ha
        change q ≤ Real.Angle.cos a at ha
        rw [← Real.Angle.cos_toReal a] at ha
        exact (not_le_of_gt hhi) (ha.trans (Real.cos_le_one _))
      rw [he, measure_empty, Real.arccos_eq_zero.2 hhi.le, mul_zero, ENNReal.ofReal_zero]
    · have he : {a : AddCircle (2 * Real.pi) | q ≤ Real.Angle.cos a} =
          closedBall 0 (Real.arccos q) := by
        ext a
        exact le_angle_cos_iff_mem_closedBall ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩ a
      rw [he, AddCircle.volume_closedBall,
        min_eq_right (mul_le_mul_of_nonneg_left (Real.arccos_le_pi q) (by norm_num))]

theorem volume_real_angle_cos_ge (q : ℝ) :
    volume.real {a : AddCircle (2 * Real.pi) | q ≤ Real.Angle.cos a} =
      2 * Real.arccos q := by
  rw [measureReal_def, volume_angle_cos_ge, ENNReal.toReal_ofReal (by
    exact mul_nonneg (by norm_num) (Real.arccos_nonneg q))]

end BlaschkeLebesgue
