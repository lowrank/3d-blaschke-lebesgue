module

import BlaschkeLebesgue.Certificates.Generated.HullSignSuite
import BlaschkeLebesgue.Certificates.ClippedHullSigns
import Lean.Util.CollectAxioms

/-! Audit the complete hull derivative sign certificate. -/

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
  for name in #[``BlaschkeLebesgue.Certificates.ClippedHull.all_edge_checks,
      ``BlaschkeLebesgue.Certificates.ClippedHull.all_baseline_checks] do
    unless env.contains name do
      throwError "Missing hull sign endpoint {name}"
  logInfo m!"Complete hull sign axiom audit passed for {checked} project declarations."

namespace BlaschkeLebesgue.Certificates.ClippedHull

example {R x : ℝ} (hR : 60849 / 100000 ≤ R) (hRhi : R ^ 2 ≤ 3 / 8)
    (hx : 23 / 25 ≤ x) (hx1 : x ≤ 1) : ClippedDifferential.combinedDx R x < 0 :=
  (edgeSigns_of_checks all_edge_checks hR hRhi hx hx1).1

example {R : ℝ} (hR : 60849 / 100000 ≤ R) (hRhi : R ^ 2 ≤ 3 / 8) :
    ∃ d, HasDerivAt ClippedFormula.combinedBaseline d R ∧ 0 < d :=
  baselineSign_of_checks all_baseline_checks hR hRhi

end BlaschkeLebesgue.Certificates.ClippedHull

#print axioms BlaschkeLebesgue.Certificates.ClippedHull.all_edge_checks
#print axioms BlaschkeLebesgue.Certificates.ClippedHull.all_baseline_checks
