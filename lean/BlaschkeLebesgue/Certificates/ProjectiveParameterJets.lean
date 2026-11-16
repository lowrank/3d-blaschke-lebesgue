module

public import BlaschkeLebesgue.Certificates.ProjectiveJets

/-! # Checked jets in either parameter direction -/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ProjectiveExpressions

open FixedPoint

/-- `true` varies `a`, and `false` varies `b`. -/
def axisA (dir : Bool) (fixed z : ℝ) : ℝ := if dir then z else fixed
def axisB (dir : Bool) (fixed z : ℝ) : ℝ := if dir then fixed else z

noncomputable def realInputA (dir : Bool) (a : ℝ) : SecondOrder.Jet :=
  if dir then SecondOrder.Jet.var a else SecondOrder.Jet.const a
noncomputable def realInputB (dir : Bool) (b : ℝ) : SecondOrder.Jet :=
  if dir then SecondOrder.Jet.const b else SecondOrder.Jet.var b

noncomputable def realParameterJets (dir : Bool) (a b : ℝ) : Params SecondOrder.Jet :=
  paramsRealJet (realInputA dir a) (realInputB dir b)

noncomputable def parameterJet (dir : Bool) (a b s t : ℝ) : Values SecondOrder.Jet :=
  valuesRealJet (realParameterJets dir a b) (SecondOrder.Jet.const s) (SecondOrder.Jet.const t)

theorem inputA_contains {p : ℕ} {dir : Bool} {A : Interval} {a : ℝ} (h : A.Contains p a) :
    (inputA p dir A).Contains p (realInputA dir a) := by
  cases dir
  · exact Jet.contains_const h
  · exact Jet.contains_var h

theorem inputB_contains {p : ℕ} {dir : Bool} {B : Interval} {b : ℝ} (h : B.Contains p b) :
    (inputB p dir B).Contains p (realInputB dir b) := by
  cases dir
  · exact Jet.contains_var h
  · exact Jet.contains_const h

theorem realInputA_validAt (dir : Bool) (fixed x : ℝ) :
    SecondOrder.Jet.ValidAt (fun z ↦ realInputA dir (axisA dir fixed z)) x := by
  cases dir
  · exact SecondOrder.Jet.validAt_const fixed x
  · exact SecondOrder.Jet.validAt_var x

theorem realInputB_validAt (dir : Bool) (fixed x : ℝ) :
    SecondOrder.Jet.ValidAt (fun z ↦ realInputB dir (axisB dir fixed z)) x := by
  cases dir
  · exact SecondOrder.Jet.validAt_var x
  · exact SecondOrder.Jet.validAt_const fixed x

theorem realParameterJets_v (dir : Bool) (a b : ℝ) :
    (realParameterJets dir a b).map SecondOrder.Jet.v = realParams a b := by
  cases dir
  · exact paramsRealJet_v (SecondOrder.Jet.const a) (SecondOrder.Jet.var b)
  · exact paramsRealJet_v (SecondOrder.Jet.var a) (SecondOrder.Jet.const b)

theorem parameterJet_values {p : ℕ} {dir : Bool} {A B U V : Interval} {par : Params Jet} {out : Values Jet}
    {a b s t : ℝ} (hp : parameterJets p dir A B = some par)
    (hv : valuesJet p par (Jet.const p U) (Jet.const p V) = some out)
    (ha : A.Contains p a) (hb : B.Contains p b) (hs : U.Contains p s) (ht : V.Contains p t) :
    (out.map Jet.v).Rel (fun I z ↦ I.Contains p z) (realValues a b s t) :=
  valuesJet_values_sound (P := realParameterJets dir a b)
    (S := SecondOrder.Jet.const s) (T := SecondOrder.Jet.const t)
    hv (paramsJet_sound hp (inputA_contains ha) (inputB_contains hb))
    (Jet.contains_const hs) (Jet.contains_const ht) (realParameterJets_v dir a b)

theorem parameterJet_derivatives {p : ℕ} {dir : Bool} {A B U V : Interval} {par : Params Jet} {out : Values Jet}
    {fixed x s t : ℝ} (hp : parameterJets p dir A B = some par)
    (hv : valuesJet p par (Jet.const p U) (Jet.const p V) = some out)
    (ha : A.Contains p (axisA dir fixed x)) (hb : B.Contains p (axisB dir fixed x))
    (hs : U.Contains p s) (ht : V.Contains p t) :
    HasDerivAt (fun z ↦ Completion.unitSquareSmoothDensity (axisA dir fixed z) (axisB dir fixed z) s t)
      (parameterJet dir (axisA dir fixed x) (axisB dir fixed x) s t).V.d x ∧
    HasDerivAt (fun z ↦ (parameterJet dir (axisA dir fixed z) (axisB dir fixed z) s t).V.d)
      (parameterJet dir (axisA dir fixed x) (axisB dir fixed x) s t).V.dd x ∧
    out.V.d.Contains p (parameterJet dir (axisA dir fixed x) (axisB dir fixed x) s t).V.d ∧
    out.V.dd.Contains p (parameterJet dir (axisA dir fixed x) (axisB dir fixed x) s t).V.dd := by
  have hpar := paramsJet_sound hp (inputA_contains ha) (inputB_contains hb)
  have hvalid := paramsJet_validAt
    (f := fun z ↦ realInputA dir (axisA dir fixed z)) (g := fun z ↦ realInputB dir (axisB dir fixed z))
    hp (inputA_contains ha) (inputB_contains hb)
    (realInputA_validAt dir fixed x) (realInputB_validAt dir fixed x)
  exact valuesJet_density_derivatives
    (P := fun z ↦ realParameterJets dir (axisA dir fixed z) (axisB dir fixed z))
    (S := fun _ ↦ SecondOrder.Jet.const s) (T := fun _ ↦ SecondOrder.Jet.const t)
    (A := axisA dir fixed) (B := axisB dir fixed) (x := x)
    hv hpar (Jet.contains_const hs) (Jet.contains_const ht) hvalid
    (SecondOrder.Jet.validAt_const s x) (SecondOrder.Jet.validAt_const t x)
    (fun z ↦ realParameterJets_v dir (axisA dir fixed z) (axisB dir fixed z))

end BlaschkeLebesgue.Certificates.ProjectiveExpressions
