module

public import BlaschkeLebesgue.Certificates.ProjectiveJets

/-! # Pure spatial derivatives used by the point quadrature -/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Certificates.ProjectiveExpressions

open FixedPoint

def spatialJetS (a b s t : ℝ) : Values SecondOrder.Jet :=
  valuesRealJet ((realParams a b).map SecondOrder.Jet.const)
    (SecondOrder.Jet.var s) (SecondOrder.Jet.const t)

def spatialJetT (a b s t : ℝ) : Values SecondOrder.Jet :=
  valuesRealJet ((realParams a b).map SecondOrder.Jet.const)
    (SecondOrder.Jet.const s) (SecondOrder.Jet.var t)

theorem spatialJetS_derivatives {p : ℕ} {par : Params Interval} {U V : Interval} {out : Values Jet}
    {a b s t : ℝ}
    (h : valuesJet p (par.map (Jet.const p)) (Jet.var p U) (Jet.const p V) = some out)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (hs : U.Contains p s) (ht : V.Contains p t) :
    HasDerivAt (fun z ↦ Completion.unitSquareSmoothDensity a b z t) (spatialJetS a b s t).V.d s ∧
    HasDerivAt (fun z ↦ (spatialJetS a b z t).V.d) (spatialJetS a b s t).V.dd s ∧
    out.V.d.Contains p (spatialJetS a b s t).V.d ∧
    out.V.dd.Contains p (spatialJetS a b s t).V.dd :=
  valuesJet_density_derivatives (P := fun _ ↦ (realParams a b).map SecondOrder.Jet.const)
    (S := SecondOrder.Jet.var) (T := fun _ ↦ SecondOrder.Jet.const t)
    (A := fun _ ↦ a) (B := fun _ ↦ b) (x := s)
    h (Params.contains_const hp) (Jet.contains_var hs) (Jet.contains_const ht)
    (Params.validAt_const (realParams a b) s) (SecondOrder.Jet.validAt_var s)
    (SecondOrder.Jet.validAt_const t s) (fun _ ↦ Params.map_const_v (realParams a b))

theorem spatialJetT_derivatives {p : ℕ} {par : Params Interval} {U V : Interval} {out : Values Jet}
    {a b s t : ℝ}
    (h : valuesJet p (par.map (Jet.const p)) (Jet.const p U) (Jet.var p V) = some out)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (hs : U.Contains p s) (ht : V.Contains p t) :
    HasDerivAt (fun z ↦ Completion.unitSquareSmoothDensity a b s z) (spatialJetT a b s t).V.d t ∧
    HasDerivAt (fun z ↦ (spatialJetT a b s z).V.d) (spatialJetT a b s t).V.dd t ∧
    out.V.d.Contains p (spatialJetT a b s t).V.d ∧
    out.V.dd.Contains p (spatialJetT a b s t).V.dd :=
  valuesJet_density_derivatives (P := fun _ ↦ (realParams a b).map SecondOrder.Jet.const)
    (S := fun _ ↦ SecondOrder.Jet.const s) (T := SecondOrder.Jet.var)
    (A := fun _ ↦ a) (B := fun _ ↦ b) (x := t)
    h (Params.contains_const hp) (Jet.contains_const hs) (Jet.contains_var ht)
    (Params.validAt_const (realParams a b) t) (SecondOrder.Jet.validAt_const s t)
    (SecondOrder.Jet.validAt_var t) (fun _ ↦ Params.map_const_v (realParams a b))

theorem spatialJetS_values {p : ℕ} {par : Params Interval} {U V : Interval} {out : Values Jet}
    {a b s t : ℝ}
    (h : valuesJet p (par.map (Jet.const p)) (Jet.var p U) (Jet.const p V) = some out)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (hs : U.Contains p s) (ht : V.Contains p t) :
    (out.map Jet.v).Rel (fun I z ↦ I.Contains p z) (realValues a b s t) :=
  valuesJet_values_sound (P := (realParams a b).map SecondOrder.Jet.const)
    (S := SecondOrder.Jet.var s) (T := SecondOrder.Jet.const t)
    h (Params.contains_const hp) (Jet.contains_var hs) (Jet.contains_const ht)
    (Params.map_const_v (realParams a b))

end BlaschkeLebesgue.Certificates.ProjectiveExpressions
