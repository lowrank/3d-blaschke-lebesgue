module

public import BlaschkeLebesgue.Certificates.ProjectiveComputation

/-! # A finite point-integral computation checked without analytic imports -/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ProjectivePointIntegral

open FixedPoint

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem origin_coarse_grid_verified :
    check 52 8 (Interval.integer 52 0) (Interval.integer 52 0) = some 2247975690989 := by
  decide +kernel

end BlaschkeLebesgue.Certificates.ProjectivePointIntegral
