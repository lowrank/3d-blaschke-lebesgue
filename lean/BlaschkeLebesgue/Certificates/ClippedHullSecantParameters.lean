module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel-checked exact parameters of all 512 secant buckets -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint

theorem secant_parameter_checks : ∀ i : Fin 512,
    (1 / 4 : ℚ) < radiusSquaredCut i 512 ∧
    radiusSquaredCut i 512 < radiusSquaredCut (i + 1) 512 ∧
    radiusSquaredCut (i + 1) 512 ≤ 3 / 8 ∧
    0 < secantBudget i 512 ∧ secantBudget i 512 < 2 / 25 := by
  decide +kernel

theorem secant_sqrt_checks : ∀ i : Fin 513,
    (rationalInterval 128 (radiusSquaredCut i 512) (radiusSquaredCut i 512)).sqrtCheck = true := by
  decide +kernel

end BlaschkeLebesgue.Certificates.ClippedHull
