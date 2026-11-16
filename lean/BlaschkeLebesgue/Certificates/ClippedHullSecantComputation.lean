module

public import BlaschkeLebesgue.Certificates.ClippedHullCheckComputation

/-! # Exact interval computations for the final 512 secant buckets -/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint

def secantBudget (i levels : ℕ) : ℚ :=
  let d := 3 / 8 - radiusSquaredCut i levels
  16 * d / (1 - 8 * d)

def secantEvaluation (p n i levels : ℕ) : Option (Interval × Interval) :=
  let z0 := radiusSquaredCut i levels
  let z1 := radiusSquaredCut (i + 1) levels
  let E := secantBudget i levels
  let r0 := Interval.sqrt p (rationalInterval p z0 z0)
  let r1 := Interval.sqrt p (rationalInterval p z1 z1)
  let e := rationalInterval p E E
  (volumeInterval p n r0 (Interval.integer p 1)).bind fun base ↦
    (volumeInterval p n r1 (Interval.integer p 1)).bind fun atZero ↦
      (volumeInterval p n r1 (Interval.sub (Interval.integer p 1) e)).bind fun atBudget ↦
        if e.invCheck then
          let slope := Interval.div p (Interval.sub atBudget.combined atZero.combined) e
          let d1 := 3 / 8 - z1
          let response : ℚ := (8 / 23) * (3 * (153 / 100000) +
            ((-601 / 100000) + 2 * (317 / 20000)) * 16 * d1)
          let bound := Interval.add (Interval.add base.baseline
            (Interval.mul p (rationalInterval p (16 * d1) (16 * d1)) slope))
            (rationalInterval p response response)
          some (slope, Interval.sub bound (Interval.rational p 259 625))
        else none

def secantCheck (p n i levels : ℕ) : Bool :=
  match secantEvaluation p n i levels with
  | none => false
  | some (slope, margin) => slope.positiveCheck && margin.positiveCheck

end BlaschkeLebesgue.Certificates.ClippedHull
