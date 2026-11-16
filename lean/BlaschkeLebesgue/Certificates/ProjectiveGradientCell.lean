module

public import BlaschkeLebesgue.Certificates.ProjectiveParameterJets
public import BlaschkeLebesgue.CompletionParameterVariation

/-!
# Parameter secant bounds from the checked gradient cells

Inactive cells have slope zero. Strictly active cells keep the signed smooth
derivative interval. All other cells adjoin zero before applying the proved
cutoff mean-value theorem. No derivative at an activation boundary is assumed.
-/

@[expose] public section

open Set

namespace BlaschkeLebesgue.Certificates.ProjectiveGradientCell

open FixedPoint ProjectiveExpressions

def inactive (v : Values Jet) : Bool := decide (v.G.v.hi ≤ 0 ∨ v.D.v.hi ≤ 0)
def active (v : Values Jet) : Bool := v.G.v.positiveCheck && v.D.v.positiveCheck

def slope (p : ℕ) (par : Params Jet) (U V : Interval) : Option Interval :=
  (valuesJet p par (Jet.const p U) (Jet.const p V)).map fun v ↦
    if inactive v then Interval.integer p 0
    else if active v then v.V.d else v.V.d.hullzero

theorem slope_sound {p : ℕ} {dir : Bool} {A B U V I : Interval} {par : Params Jet}
    {fixed l r s t : ℝ} (hp : parameterJets p dir A B = some par) (hc : slope p par U V = some I)
    (hlr : l ≤ r)
    (hA : ∀ z ∈ Icc l r, A.Contains p (axisA dir fixed z))
    (hB : ∀ z ∈ Icc l r, B.Contains p (axisB dir fixed z))
    (hU : U.Contains p s) (hV : V.Contains p t) (ht : t ∈ Icc 0 1)
    (hdom : ∀ z ∈ Icc l r, 0 ≤ axisA dir fixed z ∧ 0 ≤ axisB dir fixed z ∧
      axisA dir fixed z + axisB dir fixed z ≤ 1 / 10) :
    value p I.lo * (r - l) ≤
      Completion.unitSquareDensity (axisA dir fixed r) (axisB dir fixed r) s t -
        Completion.unitSquareDensity (axisA dir fixed l) (axisB dir fixed l) s t ∧
    Completion.unitSquareDensity (axisA dir fixed r) (axisB dir fixed r) s t -
        Completion.unitSquareDensity (axisA dir fixed l) (axisB dir fixed l) s t ≤ value p I.hi * (r - l) := by
  simp only [slope, Option.map_eq_some_iff] at hc
  obtain ⟨v, hv, rfl⟩ := hc
  have hvals (z : ℝ) (hz : z ∈ Icc l r) := parameterJet_values hp hv (hA z hz) (hB z hz) hU hV
  have hd (z : ℝ) (hz : z ∈ Ioo l r) :=
    parameterJet_derivatives hp hv (hA z ⟨hz.1.le, hz.2.le⟩) (hB z ⟨hz.1.le, hz.2.le⟩) hU hV
  have hcA : ContinuousOn (axisA dir fixed) (Icc l r) := by
    cases dir
    · exact continuous_const.continuousOn
    · exact continuous_id.continuousOn
  have hcB : ContinuousOn (axisB dir fixed) (Icc l r) := by
    cases dir
    · exact continuous_id.continuousOn
    · exact continuous_const.continuousOn
  split_ifs with hzero hpos
  · have hz : v.G.v.hi ≤ 0 ∨ v.D.v.hi ≤ 0 := of_decide_eq_true hzero
    have htrue (z : ℝ) (hzr : z ∈ Icc l r) :
        Completion.unitSquareDensity (axisA dir fixed z) (axisB dir fixed z) s t = 0 := by
      have hchi : |Completion.obliquity (axisA dir fixed z) (axisB dir fixed z)| < 1 :=
        Completion.obliquity_abs_lt_one_of_total_lt_one (hdom z hzr).2.1 (by linarith [(hdom z hzr).2.2])
      apply Completion.unitSquareDensity_eq_zero_of_inactive_of_obliquity hchi ht
      rcases hz with hG | hD
      · left
        exact (hvals z hzr).1.2.trans ((value_mono p hG).trans_eq (value_zero p))
      · right
        exact (hvals z hzr).2.1.2.trans ((value_mono p hD).trans_eq (value_zero p))
    rw [htrue r ⟨hlr, le_rfl⟩, htrue l ⟨le_rfl, hlr⟩]
    simp only [Interval.integer, value_zero, zero_mul, sub_self, le_refl, and_self]
  · simp only [active, Bool.and_eq_true] at hpos
    exact Completion.unitSquareDensity_curve_bounds_of_positive hlr hcA hcB hdom ht
      (fun z hz ↦ (hd z hz).1)
      (fun z hz ↦ ⟨Interval.pos_of_positiveCheck (hvals z ⟨hz.1.le, hz.2.le⟩).1 hpos.1,
        Interval.pos_of_positiveCheck (hvals z ⟨hz.1.le, hz.2.le⟩).2.1 hpos.2⟩)
      (fun z hz ↦ (hd z hz).2.2.1)
  · have h := Completion.unitSquareDensity_curve_bounds_hullzero hlr hcA hcB hdom ht
      (fun z hz ↦ (hd z hz).1) (fun z hz _ _ ↦ (hd z hz).2.2.1)
    simpa only [Interval.hullzero, value_min, value_max, value_zero] using h

end BlaschkeLebesgue.Certificates.ProjectiveGradientCell
