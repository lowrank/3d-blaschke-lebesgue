module

public import BlaschkeLebesgue.Certificates.ExpressionComputation

/-!
# Executable projective quadrature checks

These definitions are the same operations used by the analytic soundness
proofs. Finite kernel proofs can import this file without importing those
proofs, the real integrals, or the geometry library.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ProjectiveCell

open FixedPoint ProjectiveExpressions

def correction (p : ℕ) (half : Interval) : Interval :=
  Interval.div p (Interval.sq p half) (Interval.integer p 6)

def correctedValue (p : ℕ) (half mid ds dt : Interval) : Interval :=
  let M : Interval := ⟨ds.absMax + dt.absMax, ds.absMax + dt.absMax⟩
  mid.sub (Interval.mul p (correction p half) M)

def contribution (p : ℕ) (half area mid ds dt : Interval) : ℤ :=
  let v := correctedValue p half mid ds dt
  (Interval.mul p (Interval.pos ⟨v.lo, v.lo⟩) area).lo

def retained (v : Values Jet) : Bool := v.G.v.positiveCheck && v.D.v.positiveCheck

def lower (p : ℕ) (par : Params Interval) (U V Um Vm half area : Interval) : Option ℤ :=
  (valuesJet p (par.map (Jet.const p)) (Jet.var p U) (Jet.const p V)).bind fun js ↦
  if retained js then
    (valuesJet p (par.map (Jet.const p)) (Jet.const p U) (Jet.var p V)).bind fun jt ↦
      (valuesInterval p par Um Vm).map fun mid ↦ contribution p half area mid.V js.V.dd jt.V.dd
  else some 0

end BlaschkeLebesgue.Certificates.ProjectiveCell

namespace BlaschkeLebesgue.Certificates.ProjectivePointIntegral

open FixedPoint ProjectiveExpressions

def sumRange : ℕ → (ℕ → Option ℤ) → Option ℤ
  | 0, _ => some 0
  | n + 1, f => (sumRange n f).bind fun s ↦ (f n).map fun v ↦ s + v

def point (p n i : ℕ) : Interval := Interval.rational p (i : ℤ) (n : ℤ)
def span (p n i : ℕ) : Interval := Interval.span (point p n i) (point p n (i + 1))
def midpoint (p n i : ℕ) : Interval := Interval.rational p (2 * (i : ℤ) + 1) (2 * (n : ℤ))
def halfWidth (p n : ℕ) : Interval := Interval.rational p 1 (2 * (n : ℤ))
def area (p n : ℕ) : Interval := Interval.rational p 1 ((n : ℤ) * n)

def cell (p n : ℕ) (par : Params Interval) (i j : ℕ) : Option ℤ :=
  ProjectiveCell.lower p par (span p n i) (span p n j) (midpoint p n i) (midpoint p n j)
    (halfWidth p n) (area p n)

def grid (p n : ℕ) (par : Params Interval) : Option ℤ := sumRange n fun i ↦ sumRange n fun j ↦ cell p n par i j

def check (p n : ℕ) (a b : Interval) : Option ℤ :=
  (paramsInterval p a b).bind fun par ↦ grid p n par

end BlaschkeLebesgue.Certificates.ProjectivePointIntegral

namespace BlaschkeLebesgue.Certificates.ProjectiveGradientCell

open FixedPoint ProjectiveExpressions

def inactive (v : Values Jet) : Bool := decide (v.G.v.hi ≤ 0 ∨ v.D.v.hi ≤ 0)
def active (v : Values Jet) : Bool := v.G.v.positiveCheck && v.D.v.positiveCheck

def slope (p : ℕ) (par : Params Jet) (U V : Interval) : Option Interval :=
  (valuesJet p par (Jet.const p U) (Jet.const p V)).map fun v ↦
    if inactive v then Interval.integer p 0
    else if active v then v.V.d else v.V.d.hullzero

end BlaschkeLebesgue.Certificates.ProjectiveGradientCell

namespace BlaschkeLebesgue.Certificates.ProjectiveGradientIntegral

open FixedPoint ProjectiveExpressions

def sumRange : ℕ → (ℕ → Option Interval) → Option Interval
  | 0, _ => some ⟨0, 0⟩
  | n + 1, f => (sumRange n f).bind fun s ↦ (f n).map (Interval.add s)

def cell (p n : ℕ) (par : Params Jet) (i j : ℕ) : Option Interval :=
  (ProjectiveGradientCell.slope p par (ProjectivePointIntegral.span p n i) (ProjectivePointIntegral.span p n j)).map
    fun I ↦ Interval.mul p (ProjectivePointIntegral.area p n) I

def grid (p n : ℕ) (par : Params Jet) : Option Interval :=
  sumRange n fun i ↦ sumRange n fun j ↦ cell p n par i j

def check (p n : ℕ) (dir : Bool) (A B : Interval) : Option Interval :=
  (parameterJets p dir A B).bind fun par ↦ grid p n par

end BlaschkeLebesgue.Certificates.ProjectiveGradientIntegral
