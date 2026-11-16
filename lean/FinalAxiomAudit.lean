module

import BlaschkeLebesgue
import BlaschkeLebesgue.Final
import Lean.Util.CollectAxioms

/-! Audit the unconditional theorem and all imported project declarations. -/

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
  for name in #[``BlaschkeLebesgue.constantWidthVolumeBound,
      ``BlaschkeLebesgue.constantWidth_volume_gt,
      ``BlaschkeLebesgue.Certificates.ClippedHull.all_edge_checks,
      ``BlaschkeLebesgue.Certificates.ClippedHull.all_baseline_checks,
      ``BlaschkeLebesgue.Certificates.ClippedHull.all_secant_checks,
      ``BlaschkeLebesgue.Certificates.ProjectiveSuite.completion_affine_lower] do
    unless env.contains name do
      throwError "Missing final endpoint {name}"
  logInfo m!"Final unconditional axiom audit passed for {checked} project declarations."

#print axioms BlaschkeLebesgue.constantWidth_volume_gt
#check BlaschkeLebesgue.constantWidth_volume_gt
