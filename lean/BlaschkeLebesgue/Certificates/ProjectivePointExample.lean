module

public import BlaschkeLebesgue.Certificates.ProjectivePointIntegral

/-!
# A complete kernel-checked point-integral example

This small grid exercises the entire chain from integer operations to a
lower bound on the geometric integral. It does not replace the 584 required
center checks at the certificate's finer grid size.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ProjectivePointIntegral

open FixedPoint

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem origin_coarse_grid_verified :
    check 52 8 (Interval.integer 52 0) (Interval.integer 52 0) = some 2247975690989 := by
  decide +kernel

theorem origin_coarse_integral_lower : (49 / 100000 : ℝ) ≤ Completion.F 0 0 := by
  have h0 : (Interval.integer 52 0).Contains 52 (0 : ℝ) := by
    simpa only [Int.cast_zero] using Interval.contains_integer 52 0
  have hchi : |Completion.obliquity 0 0| < 1 := by norm_num [Completion.obliquity]
  have hv := check_sound origin_coarse_grid_verified (by decide) h0 h0 (by norm_num) hchi
  rw [← Completion.F_eq_fixedSquareIntegral (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num)] at hv
  have hlo : (49 / 100000 : ℝ) ≤ value 52 2247975690989 := by norm_num [value, scale]
  exact hlo.trans hv

end BlaschkeLebesgue.Certificates.ProjectivePointIntegral
