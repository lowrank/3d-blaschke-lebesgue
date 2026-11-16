module

public import BlaschkeLebesgue.Certificates.ClippedHullComputation

/-! # A kernel-checked sample of the clipped-hull derivative computation

This checks one point, rather than the complete sign cover.
-/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint

def sampleSigns : Bool :=
  match dxJet 128 64 (Jet.const 128 (Interval.rational 128 61 100))
      (Jet.var 128 (Interval.rational 128 99 100)),
    volumeJet 128 64 (Jet.var 128 (Interval.rational 128 61 100))
      (Jet.const 128 (Interval.integer 128 1)) with
  | some dx, some vol => decide
      (dx.combined.v.hi < 0 ∧ dx.combined.d.hi < 0 ∧ 0 < vol.baseline.d.lo)
  | _, _ => false

theorem sampleSigns_verified : sampleSigns = true := by decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull
