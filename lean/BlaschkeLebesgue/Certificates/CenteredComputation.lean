module

public import BlaschkeLebesgue.Certificates.ProjectiveComputation

/-! # Point quadrature with a centered test for retaining cells -/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.CenteredProjective

open FixedPoint ProjectiveExpressions

def variationLower (p : ℕ) (half mid ds dt : Interval) : ℤ :=
  (mid.sub (Interval.mul p half ⟨ds.absMax + dt.absMax, ds.absMax + dt.absMax⟩)).lo

def retained (p : ℕ) (half : Interval) (mid : Values Interval) (js jt : Values Jet) : Bool :=
  ProjectiveCell.retained js ||
    (decide (0 < variationLower p half mid.G js.G.d jt.G.d) &&
      decide (0 < variationLower p half mid.D js.D.d jt.D.d))

def lower (p : ℕ) (par : Params Interval) (U V Um Vm half area : Interval) : Option ℤ :=
  (valuesJet p (par.map (Jet.const p)) (Jet.var p U) (Jet.const p V)).bind fun js ↦
    (valuesJet p (par.map (Jet.const p)) (Jet.const p U) (Jet.var p V)).bind fun jt ↦
      (valuesInterval p par Um Vm).map fun mid ↦
        if retained p half mid js jt then ProjectiveCell.contribution p half area mid.V js.V.dd jt.V.dd else 0

def cell (p n : ℕ) (par : Params Interval) (i j : ℕ) : Option ℤ :=
  lower p par (ProjectivePointIntegral.span p n i) (ProjectivePointIntegral.span p n j)
    (ProjectivePointIntegral.midpoint p n i) (ProjectivePointIntegral.midpoint p n j)
    (ProjectivePointIntegral.halfWidth p n) (ProjectivePointIntegral.area p n)

def grid (p n : ℕ) (par : Params Interval) : Option ℤ :=
  ProjectivePointIntegral.sumRange n fun i ↦ ProjectivePointIntegral.sumRange n fun j ↦ cell p n par i j

def check (p n : ℕ) (a b : Interval) : Option ℤ :=
  (paramsInterval p a b).bind fun par ↦ grid p n par

end BlaschkeLebesgue.Certificates.CenteredProjective
