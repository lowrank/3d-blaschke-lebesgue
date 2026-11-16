module

import BlaschkeLebesgue.Certificates.Generated.HullSecantSuite
import BlaschkeLebesgue.Certificates.ClippedHullSecantSoundness
import Lean.Util.CollectAxioms

/-! Audit the complete secant certificate after its 32 kernel jobs pass. -/

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
  unless env.contains ``BlaschkeLebesgue.Certificates.ClippedHull.all_secant_checks do
    throwError "Missing complete secant certificate"
  logInfo m!"Complete secant axiom audit passed for {checked} project declarations."

namespace BlaschkeLebesgue.Certificates.ClippedHull

example (i : Fin 512) : 0 < secantSlope i 512 ∧ 259 / 625 < secantBound i 512 :=
  secantCheck_sound_512 i (all_secant_checks i)

end BlaschkeLebesgue.Certificates.ClippedHull

#print axioms BlaschkeLebesgue.Certificates.ClippedHull.all_secant_checks
