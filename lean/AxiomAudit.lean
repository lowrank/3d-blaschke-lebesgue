module

import BlaschkeLebesgue
import Lean.Util.CollectAxioms

/-! Audit every project declaration, including transitive dependencies. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`BlaschkeLebesgue).isPrefixOf name then
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} uses forbidden axiom {axiomName}"
      checked := checked + 1
  for name in #[``BlaschkeLebesgue.HasConstantWidth.opposite_point,
      ``BlaschkeLebesgue.HasConstantWidth.ballTransform_eq,
      ``BlaschkeLebesgue.HasConstantWidth.radial_normal,
      ``BlaschkeLebesgue.BalancedContacts.deficit_budget,
      ``BlaschkeLebesgue.exists_minimumEnclosingBall,
      ``BlaschkeLebesgue.MinimumEnclosingBall.center_mem_convexHull_contacts,
      ``BlaschkeLebesgue.MinimumEnclosingBall.exists_contacts_with_deficit_budget,
      ``BlaschkeLebesgue.EnclosingContacts.zero_mem_interior_convexHull,
      ``BlaschkeLebesgue.exists_centered_unit_body,
      ``BlaschkeLebesgue.Radial.propagation_test_sound,
      ``BlaschkeLebesgue.Radial.gap_monotoneOn,
      ``BlaschkeLebesgue.Completion.curvature_weight_lower,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.certified_radius_cover,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.all_rows_negative_body_bound,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.all_rows_negative_caps_disjoint,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.negativeStep_gap_lower,
      ``BlaschkeLebesgue.radialFunction_smul_mem_frontier,
      ``BlaschkeLebesgue.continuousOn_radialFunction,
      ``BlaschkeLebesgue.HasConstantWidth.positive_cap_step,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.all_rows_positive_radial_bound,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.all_rows_positive_gap_lower,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.all_rows_negative_gap_lower,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.all_rows_opposite_caps_disjoint,
      ``BlaschkeLebesgue.integral_radialFunction_cube,
      ``BlaschkeLebesgue.sphereMeasure_cap,
      ``BlaschkeLebesgue.volume_diskSolid,
      ``BlaschkeLebesgue.integral_radial_gap_eq,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.checkRow_gap_integral_lower,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.all_rows_gap_integral_lower,
      ``BlaschkeLebesgue.HasConstantWidth.add_reflectBody,
      ``BlaschkeLebesgue.supportPoint_firm_of_ball_sum,
      ``BlaschkeLebesgue.homogeneousSupport_ae_differentiable_of_ball_sum,
      ``BlaschkeLebesgue.parallelSupport_image_closedBall,
      ``BlaschkeLebesgue.parallelSupport_antilipschitz,
      ``BlaschkeLebesgue.lipschitz_image_volume_zero,
      ``BlaschkeLebesgue.integral_abs_det_of_lipschitz_injective,
      ``BlaschkeLebesgue.parallelJacobian_integral,
      ``BlaschkeLebesgue.parallelBody_volume_polynomial,
      ``BlaschkeLebesgue.HasConstantWidth.blaschke_identity,
      ``BlaschkeLebesgue.HasConstantWidth.parallelBody_volume_derivative,
      ``BlaschkeLebesgue.HasConstantWidth.radial_master,
      ``BlaschkeLebesgue.Certificates.RadialArithmetic.all_rows_volume_lower,
      ``BlaschkeLebesgue.MinimumEnclosingBall.volume_gt_of_radius_le_radial_cutoff,
      ``BlaschkeLebesgue.smallBall_chord_perturbation,
      ``BlaschkeLebesgue.smallBallIntersection_opposite_mem,
      ``BlaschkeLebesgue.smallBallIntersection_add_complement,
      ``BlaschkeLebesgue.complementary_volume_coefficients,
      ``BlaschkeLebesgue.clippedBodies_complement,
      ``BlaschkeLebesgue.HasConstantWidth.clippedBodies_volume_coefficients,
      ``BlaschkeLebesgue.hasFDerivAt_support,
      ``BlaschkeLebesgue.normalSupport_derivative_symmetric,
      ``BlaschkeLebesgue.normalSupport_sphere_ae_differentiable,
      ``BlaschkeLebesgue.sphereCurvature_le_tangentProjection,
      ``BlaschkeLebesgue.sphereCurvature_complement_ae,
      ``BlaschkeLebesgue.curvatureDet_bounds,
      ``BlaschkeLebesgue.curvatureTrace_sub_one_le_det,
      ``BlaschkeLebesgue.integrable_curvatureDet,
      ``BlaschkeLebesgue.homogeneousSupport_det_eq_curvature_ae,
      ``BlaschkeLebesgue.integral_closedBall_homogeneous_zero,
      ``BlaschkeLebesgue.integral_support_curvatureDet,
      ``BlaschkeLebesgue.unitWidthVolumeBound_iff,
      ``BlaschkeLebesgue.ConstantWidthVolumeBound] do
    unless env.contains name do
      throwError "Missing required declaration {name}"
  if checked == 0 then
    throwError "No project declarations were audited"
  logInfo m!"Axiom audit passed for {checked} project declarations."
