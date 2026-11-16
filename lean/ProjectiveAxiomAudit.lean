module

import BlaschkeLebesgue.Certificates.Generated.ProjectiveSuite
import Lean.Util.CollectAxioms

/-! Audit the complete projective suite after all kernel shards are assembled. -/

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
  for name in #[``BlaschkeLebesgue.Certificates.ProjectiveSuite.boxes_verified,
      ``BlaschkeLebesgue.Certificates.ProjectiveSuite.all_verified,
      ``BlaschkeLebesgue.Certificates.ProjectiveSuite.completion_affine_lower] do
    unless env.contains name do
      throwError "Missing projective endpoint {name}"
  logInfo m!"Complete projective axiom audit passed for {checked} project declarations."
