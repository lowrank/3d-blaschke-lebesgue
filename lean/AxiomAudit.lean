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
      ``BlaschkeLebesgue.ConstantWidthVolumeBound] do
    unless env.contains name do
      throwError "Missing required declaration {name}"
  if checked == 0 then
    throwError "No project declarations were audited"
  logInfo m!"Axiom audit passed for {checked} project declarations."
