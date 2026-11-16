module

public import BlaschkeLebesgue.Certificates.MainAssembly
public import BlaschkeLebesgue.Certificates.Generated.HullSignSuite
public import BlaschkeLebesgue.Certificates.Generated.HullSecantSuite
public import BlaschkeLebesgue.Certificates.Generated.ProjectiveSuite

/-! # The three-dimensional constant-width volume bound

This module requires all three complete kernel certificate suites. Its source
is not a verification claim until those imports and this module have compiled.
-/

public noncomputable section

namespace BlaschkeLebesgue

/-- The full geometric target, discharged by the finite kernel certificates. -/
theorem constantWidthVolumeBound : ConstantWidthVolumeBound :=
  Certificates.constantWidthVolumeBound_of_certificates
    Certificates.ClippedHull.all_edge_checks Certificates.ClippedHull.all_baseline_checks
    Certificates.ClippedHull.all_secant_checks
    (fun _ _ ha hb hab ↦ Certificates.ProjectiveSuite.completion_affine_lower ha hb hab)

/-- Every convex body of constant width `w>0` in Euclidean three-space has
Lebesgue volume strictly greater than `0.4144*w^3`. -/
theorem constantWidth_volume_gt (K : ConvexBody Space)
    (hinterior : (interior (K : Set Space)).Nonempty) (w : ℝ) (hw : 0 < w)
    (hwidth : HasConstantWidth K w) : (259 / 625 : ℝ) * w ^ 3 < bodyVolume K :=
  constantWidthVolumeBound K hinterior w hw hwidth

end BlaschkeLebesgue
