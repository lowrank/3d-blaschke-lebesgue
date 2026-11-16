module

public import BlaschkeLebesgue.Certificates.ProjectiveSpatialJets

/-! # Checked derivatives of the gap and determinant in the spatial directions -/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Certificates.ProjectiveExpressions

open FixedPoint

theorem spatialJetS_activation_derivatives {p : ℕ} {par : Params Interval} {U V : Interval} {out : Values Jet}
    {a b s t : ℝ}
    (h : valuesJet p (par.map (Jet.const p)) (Jet.var p U) (Jet.const p V) = some out)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (hs : U.Contains p s) (ht : V.Contains p t) :
    (HasDerivAt (fun z ↦ Completion.squareGap a b z t) (spatialJetS a b s t).G.d s ∧
      out.G.d.Contains p (spatialJetS a b s t).G.d) ∧
    (HasDerivAt (fun z ↦ Completion.squareDetLower a b z t) (spatialJetS a b s t).D.d s ∧
      out.D.d.Contains p (spatialJetS a b s t).D.d) := by
  have hv := valuesJet_validAt (P := fun _ ↦ (realParams a b).map SecondOrder.Jet.const)
    (S := SecondOrder.Jet.var) (T := (fun _ ↦ SecondOrder.Jet.const t)) (x := s)
    h (Params.contains_const hp) (Jet.contains_var hs) (Jet.contains_const ht)
    (Params.validAt_const (realParams a b) s) (SecondOrder.Jet.validAt_var s) (SecondOrder.Jet.validAt_const t s)
  have hc := valuesJet_sound h (Params.contains_const hp) (Jet.contains_var hs) (Jet.contains_const ht)
  have hG (z : ℝ) : (spatialJetS a b z t).G.v = Completion.squareGap a b z t :=
    congrArg Values.G (valuesRealJet_v (Params.map_const_v (realParams a b)) (SecondOrder.Jet.var z) (SecondOrder.Jet.const t))
  have hD (z : ℝ) : (spatialJetS a b z t).D.v = Completion.squareDetLower a b z t :=
    congrArg Values.D (valuesRealJet_v (Params.map_const_v (realParams a b)) (SecondOrder.Jet.var z) (SecondOrder.Jet.const t))
  refine ⟨⟨?_, hc.1.2.1⟩, ⟨?_, hc.2.1.2.1⟩⟩
  · simp_rw [← hG]
    exact hv.1.1
  · simp_rw [← hD]
    exact hv.2.1.1

theorem spatialJetT_activation_derivatives {p : ℕ} {par : Params Interval} {U V : Interval} {out : Values Jet}
    {a b s t : ℝ}
    (h : valuesJet p (par.map (Jet.const p)) (Jet.const p U) (Jet.var p V) = some out)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (hs : U.Contains p s) (ht : V.Contains p t) :
    (HasDerivAt (fun z ↦ Completion.squareGap a b s z) (spatialJetT a b s t).G.d t ∧
      out.G.d.Contains p (spatialJetT a b s t).G.d) ∧
    (HasDerivAt (fun z ↦ Completion.squareDetLower a b s z) (spatialJetT a b s t).D.d t ∧
      out.D.d.Contains p (spatialJetT a b s t).D.d) := by
  have hv := valuesJet_validAt (P := fun _ ↦ (realParams a b).map SecondOrder.Jet.const)
    (S := (fun _ ↦ SecondOrder.Jet.const s)) (T := SecondOrder.Jet.var) (x := t)
    h (Params.contains_const hp) (Jet.contains_const hs) (Jet.contains_var ht)
    (Params.validAt_const (realParams a b) t) (SecondOrder.Jet.validAt_const s t) (SecondOrder.Jet.validAt_var t)
  have hc := valuesJet_sound h (Params.contains_const hp) (Jet.contains_const hs) (Jet.contains_var ht)
  have hG (z : ℝ) : (spatialJetT a b s z).G.v = Completion.squareGap a b s z :=
    congrArg Values.G (valuesRealJet_v (Params.map_const_v (realParams a b)) (SecondOrder.Jet.const s) (SecondOrder.Jet.var z))
  have hD (z : ℝ) : (spatialJetT a b s z).D.v = Completion.squareDetLower a b s z :=
    congrArg Values.D (valuesRealJet_v (Params.map_const_v (realParams a b)) (SecondOrder.Jet.const s) (SecondOrder.Jet.var z))
  refine ⟨⟨?_, hc.1.2.1⟩, ⟨?_, hc.2.1.2.1⟩⟩
  · simp_rw [← hG]
    exact hv.1.1
  · simp_rw [← hD]
    exact hv.2.1.1

end BlaschkeLebesgue.Certificates.ProjectiveExpressions
