module

public import BlaschkeLebesgue.Certificates.ClippedHullComputation

/-! # Executable clipped-hull sign checks on the complete rational grid -/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint

def radiusSquaredLow : ℚ := (60849 / 100000) ^ 2

def radiusSquaredCut (i nr : ℕ) : ℚ :=
  radiusSquaredLow + (3 / 8 - radiusSquaredLow) * i / nr

def rationalInterval (p : ℕ) (a b : ℚ) : Interval :=
  Interval.span (Interval.rational p a.num a.den) (Interval.rational p b.num b.den)

def radiusInterval (p i nr : ℕ) : Interval :=
  Interval.sqrt p (rationalInterval p (radiusSquaredCut i nr) (radiusSquaredCut (i + 1) nr))

def edgeSquaredInterval (p j ne : ℕ) : Interval :=
  rationalInterval p (1 - (2 / 25 : ℚ) * (j + 1) / ne) (1 - (2 / 25 : ℚ) * j / ne)

def edgeSignCheck (p n i j nr ne : ℕ) : Bool :=
  let R := radiusInterval p i nr
  let x := edgeSquaredInterval p j ne
  match dxJet p n (Jet.const p R) (Jet.var p x),
      dxJet p n (Jet.var p R) (Jet.const p x) with
  | some dx, some dr => decide (dx.combined.v.hi < 0 ∧ dx.combined.d.hi < 0 ∧
      0 < dr.combined.d.lo)
  | _, _ => false

def baselineSignCheck (p n i nr : ℕ) : Bool :=
  match volumeJet p n (Jet.var p (radiusInterval p i nr))
      (Jet.const p (Interval.integer p 1)) with
  | some v => decide (0 < v.baseline.d.lo)
  | none => false

end BlaschkeLebesgue.Certificates.ClippedHull
