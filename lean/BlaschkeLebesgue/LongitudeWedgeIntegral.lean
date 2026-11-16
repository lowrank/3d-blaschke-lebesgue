module

public import BlaschkeLebesgue.SphereCoordinates
public import BlaschkeLebesgue.LensScalar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Exact integration of the circle-curvature density over a normal wedge -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

@[expose] def longitudeWedge (a b : ℝ) (s : Set (AddCircle (2 * Real.pi))) : Set UnitSphere :=
  {u | ⟪coordinatePole, (u : Space)⟫_ℝ ∈ Icc a b} ∩ longitude ⁻¹' s

theorem measurableSet_longitudeWedge (a b : ℝ) {s : Set (AddCircle (2 * Real.pi))}
    (hs : MeasurableSet s) : MeasurableSet (longitudeWedge a b s) :=
  (measurableSet_Icc.preimage (continuous_const.inner continuous_subtype_val).measurable).inter
    (hs.preimage measurable_longitude)

theorem integral_longitudeWedge_height {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1)
    {s : Set (AddCircle (2 * Real.pi))} (hs : MeasurableSet s) {f : ℝ → ℝ}
    (hf : StronglyMeasurable f) :
    (∫ u in longitudeWedge a b s, f ⟪coordinatePole, (u : Space)⟫_ℝ ∂sphereMeasure) =
      volume.real s * ∫ z in Icc a b, f z := by
  have hm : Measurable (fun u : UnitSphere ↦ ⟪coordinatePole, (u : Space)⟫_ℝ) := by fun_prop
  have h := setIntegral_map (μ := sphereMeasure.restrict (longitude ⁻¹' s))
    (s := Icc a b) measurableSet_Icc (f := f) hf.aestronglyMeasurable hm.aemeasurable
  rw [sphereMeasure_map_height_restrict_longitude hs, Measure.restrict_smul,
    integral_smul_measure, smul_eq_mul, Measure.restrict_restrict measurableSet_Icc,
    Measure.restrict_restrict (measurableSet_Icc.preimage hm)] at h
  have he : Icc a b ∩ Icc (-1 : ℝ) 1 = Icc a b :=
    inter_eq_left.2 (fun _ hz ↦ ⟨ha.trans hz.1, hz.2.trans hb⟩)
  rw [he] at h
  exact h.symm

theorem integral_one_div_sqrt_one_sub_sq {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    (∫ z in Icc a b, 1 / Real.sqrt (1 - z ^ 2)) = Real.arcsin b - Real.arcsin a := by
  have hz' : ∀ z ∈ Icc a b, z ∈ Ioo (-1 : ℝ) 1 := fun z hz ↦
    ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
  have hi : IntervalIntegrable (fun z : ℝ ↦ 1 / Real.sqrt (1 - z ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro z hz
    have hn := (Real.sqrt_pos.2 (one_sub_sq_pos_of_mem_unitInterval (hz' z hz))).ne'
    exact (continuousAt_const.div (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.sub (continuousAt_id.pow 2))) hn).continuousWithinAt
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab Real.continuous_arcsin.continuousOn
    _ hi
  intro z hz
  exact Real.hasDerivAt_arcsin (ne_of_gt (ha.trans hz.1)) (ne_of_lt (hz.2.trans hb))

/-- A circle of radius `r` contributes `r` times the longitude length times the normal angle. -/
theorem integral_longitudeWedge_circleDensity {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b)
    {s : Set (AddCircle (2 * Real.pi))} (hs : MeasurableSet s) (r : ℝ) :
    (∫ u in longitudeWedge a b s,
      r / Real.sqrt (1 - ⟪coordinatePole, (u : Space)⟫_ℝ ^ 2) ∂sphereMeasure) =
      r * volume.real s * (Real.arcsin b - Real.arcsin a) := by
  have hm : StronglyMeasurable (fun z : ℝ ↦ r / Real.sqrt (1 - z ^ 2)) :=
    (show Measurable (fun z : ℝ ↦ r / Real.sqrt (1 - z ^ 2)) by fun_prop).stronglyMeasurable
  rw [integral_longitudeWedge_height ha.le hb.le hs (f := fun z ↦ r / Real.sqrt (1 - z ^ 2)) hm]
  have he : (fun z : ℝ ↦ r / Real.sqrt (1 - z ^ 2)) =
      fun z : ℝ ↦ r * (1 / Real.sqrt (1 - z ^ 2)) := by funext z; ring
  rw [he, integral_const_mul, integral_one_div_sqrt_one_sub_sq ha hb hab]
  ring

theorem arcsin_one_sub_two_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arcsin (1 - 2 * x ^ 2) = Real.pi / 2 - 2 * Real.arcsin x := by
  apply Real.arcsin_eq_of_sin_eq
  · rw [Real.sin_pi_div_two_sub, Real.cos_two_mul_eq_one_sub,
      Real.sin_arcsin (by linarith) hx1]
  · constructor <;> linarith [Real.arcsin_nonneg.2 hx0, Real.arcsin_le_pi_div_two x]

theorem unit_radius_normal_angle {R : ℝ} (hR : 1 / 2 < R) :
    Real.arcsin (1 - 1 / (2 * R ^ 2)) - Real.arcsin (-(1 / (2 * R))) =
      Real.arccos (1 / (2 * R)) := by
  have hR0 : 0 < R := by linarith
  have hx0 : 0 ≤ 1 / (2 * R) := by positivity
  have hx1 : 1 / (2 * R) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  rw [show 1 - 1 / (2 * R ^ 2) = 1 - 2 * (1 / (2 * R)) ^ 2 by ring,
    arcsin_one_sub_two_sq hx0 hx1, Real.arcsin_neg, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

theorem integral_unit_pair_wedge {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    {s : Set (AddCircle (2 * Real.pi))} (hs : MeasurableSet s) (r : ℝ) :
    (∫ u in longitudeWedge (-(d / 2)) (d / 2) s,
      r / Real.sqrt (1 - ⟪coordinatePole, (u : Space)⟫_ℝ ^ 2) ∂sphereMeasure) =
      2 * r * volume.real s * Real.arcsin (d / 2) := by
  rw [integral_longitudeWedge_circleDensity (by linarith) (by linarith) (by linarith) hs r,
    Real.arcsin_neg]
  ring

theorem integral_unit_radius_wedge {R : ℝ} (hR : 1 / 2 < R)
    {s : Set (AddCircle (2 * Real.pi))} (hs : MeasurableSet s) (r : ℝ) :
    (∫ u in longitudeWedge (-(1 / (2 * R))) (1 - 1 / (2 * R ^ 2)) s,
      r / Real.sqrt (1 - ⟪coordinatePole, (u : Space)⟫_ℝ ^ 2) ∂sphereMeasure) =
      r * volume.real s * Real.arccos (1 / (2 * R)) := by
  have hR0 : 0 < R := by linarith
  have ha : -1 < -(1 / (2 * R)) := by
    have h := (div_lt_one (by positivity : 0 < 2 * R)).2 (show 1 < 2 * R by linarith)
    linarith
  have hb : 1 - 1 / (2 * R ^ 2) < 1 := by
    have h : 0 < 1 / (2 * R ^ 2) := by positivity
    linarith
  have hab : -(1 / (2 * R)) ≤ 1 - 1 / (2 * R ^ 2) := by
    have h : 1 / (2 * R ^ 2) ≤ 1 + 1 / (2 * R) := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * R ^ 2)).2
      have he : (1 + 1 / (2 * R)) * (2 * R ^ 2) = 2 * R ^ 2 + R := by field_simp
      rw [he]
      nlinarith
    linarith
  rw [integral_longitudeWedge_circleDensity ha hb hab hs r, unit_radius_normal_angle hR]

end BlaschkeLebesgue
