module

public import BlaschkeLebesgue.ActiveProjectiveRegion
public import BlaschkeLebesgue.ProjectiveCompletionIntegral

/-! # Integrability of the actual and scalar completion densities -/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue

theorem ObliqueFrame.continuous_projectiveUnitNormal (f : ObliqueFrame) :
    Continuous (fun p : ℝ × ℝ ↦ f.projectiveUnitNormal p.1 p.2) := by
  exact f.continuous_projectiveNormal.subtype_mk _

theorem integrableOn_abs_rectangle {H : ℝ × ℝ → ℝ} (hH : Continuous H) (T : ℝ) :
    IntegrableOn H {p | |p.1| < T ∧ |p.2| < T} := by
  apply (hH.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (t := Icc (-T) T ×ˢ Icc (-T) T)
  intro p hp
  exact ⟨⟨(abs_lt.1 hp.1).1.le, (abs_lt.1 hp.1).2.le⟩,
    ⟨(abs_lt.1 hp.2).1.le, (abs_lt.1 hp.2).2.le⟩⟩

theorem integrableOn_projectiveCompletionIntegrand {D D' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (f : ObliqueFrame) (T : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ projectiveCompletionIntegrand D f p.1 p.2)
      {p | |p.1| < T ∧ |p.2| < T} := by
  have hnormal := f.continuous_projectiveUnitNormal
  have hden : Continuous (fun p : ℝ × ℝ ↦ f.sine * Real.sqrt (f.W p.1 p.2) ^ 3) := by
    unfold ObliqueFrame.W
    fun_prop
  have hden0 : ∀ p : ℝ × ℝ, f.sine * Real.sqrt (f.W p.1 p.2) ^ 3 ≠ 0 := fun p ↦
    mul_ne_zero f.sine_pos.ne' (pow_ne_zero 3 (Real.sqrt_pos.2 (f.W_pos p.1 p.2)).ne')
  have hc := ((continuous_missingWidth hD).comp hnormal).div hden hden0
  have hi := integrableOn_abs_rectangle hc T
  have hm := (measurable_antipodalCompletionWeight D).comp hnormal.measurable
  have hb : ∀ p : ℝ × ℝ, ‖antipodalCompletionWeight D (f.projectiveUnitNormal p.1 p.2)‖ ≤ 1 := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (antipodalCompletionWeight_bounds hD _).1]
    exact (antipodalCompletionWeight_bounds hD _).2
  have hmul := hi.mul_bdd hm.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hb)
  apply hmul.congr
  filter_upwards [] with p
  dsimp only [projectiveCompletionIntegrand, Function.comp_apply, Pi.div_apply]
  ring

namespace Completion

@[expose] def uniformDensity (a b x y : ℝ) : ℝ :=
  phi (allocationNumerator a b x y) (determinantFactor a x y) (uniformW a b x y)

theorem uniformW_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) (x y : ℝ) :
    0 < uniformW a b x y := by
  have ho := obliquity_bounds ha hb hab
  have h := averagedW_ge (x := x) (y := y) (t := obliquity a b)
    (by rw [abs_of_nonneg ho.1]; linarith [ho.2])
  change _ ≤ uniformW a b x y at h
  nlinarith [sq_nonneg x, le_max_left (x ^ 2) (y ^ 2)]

theorem continuous_uniformDensity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    Continuous (fun p : ℝ × ℝ ↦ uniformDensity a b p.1 p.2) := by
  have hN : Continuous (fun p : ℝ × ℝ ↦ allocationNumerator a b p.1 p.2) := by
    unfold allocationNumerator
    fun_prop
  have hz : Continuous (fun p : ℝ × ℝ ↦ determinantFactor a p.1 p.2) := by
    unfold determinantFactor
    apply continuous_const.div
    · fun_prop
    · intro p
      apply ne_of_gt (Real.sqrt_pos.2 _)
      have h := le_min (sq_nonneg p.1) (sq_nonneg p.2)
      linarith
  have hS : Continuous (fun p : ℝ × ℝ ↦ Real.sqrt (uniformW a b p.1 p.2)) := by
    unfold uniformW averagedW
    fun_prop
  have hS0 : ∀ p : ℝ × ℝ, Real.sqrt (uniformW a b p.1 p.2) ≠ 0 := fun p ↦
    (Real.sqrt_pos.2 (uniformW_pos ha hb hab p.1 p.2)).ne'
  unfold uniformDensity phi q
  apply Continuous.div
  · fun_prop
  · exact hS.pow 3
  · exact fun p ↦ pow_ne_zero 3 (hS0 p)

theorem uniformDensity_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 2 / 25) (x y : ℝ) : 0 ≤ uniformDensity a b x y := by
  have ho := obliquity_bounds ha hb hab
  exact phi_nonneg (determinantFactor_sqrt_lower ha x y
    (averagedW_ge (by rw [abs_of_nonneg ho.1]; linarith [ho.2])))

end Completion

namespace BalancedContacts.Opposite

theorem integrableOn_activeProjectiveIntegrand (c : BalancedContacts 4 Space) (f : ObliqueFrame)
    {D D' : ConvexBody Space} (hD : D + D' = unitBallBody) :
    IntegrableOn (fun p : ℝ × ℝ ↦ activeProjectiveIntegrand c f D p.1 p.2) (projectiveRectangle c) := by
  exact (integrableOn_projectiveCompletionIntegrand hD f _).indicator
    (measurableSet_positiveProjectiveCurvature c f)

end BalancedContacts.Opposite
end BlaschkeLebesgue
