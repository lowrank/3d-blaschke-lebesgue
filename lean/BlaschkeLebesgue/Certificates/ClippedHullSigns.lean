module

public import BlaschkeLebesgue.Certificates.ClippedHullGrid
public import BlaschkeLebesgue.Certificates.ClippedHullSignSoundness

/-! # Assembly of the clipped-hull derivative cover

The computational premises are discharged only by the complete kernel suite.
-/

public noncomputable section

namespace BlaschkeLebesgue.Certificates.ClippedHull

open ClippedDifferential

theorem edgeSigns_of_checks
    (checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true)
    {R x : ℝ} (hR : 60849 / 100000 ≤ R) (hRhi : R ^ 2 ≤ 3 / 8)
    (hx : 23 / 25 ≤ x) (hx1 : x ≤ 1) :
    combinedDx R x < 0 ∧
      (∃ d, HasDerivAt (combinedDx R) d x ∧ d < 0) ∧
      (∃ d, HasDerivAt (fun t ↦ combinedDx t x) d R ∧ 0 < d) := by
  obtain ⟨i, hi⟩ := radius_grid_cover hR hRhi
  obtain ⟨j, hj⟩ := edge_grid_cover hx hx1
  exact edgeSigns_sound (checks i j) hi hj

theorem baselineSign_of_checks
    (checks : ∀ i : Fin 32, baselineSignCheck 128 64 i 32 = true)
    {R : ℝ} (hR : 60849 / 100000 ≤ R) (hRhi : R ^ 2 ≤ 3 / 8) :
    ∃ d, HasDerivAt ClippedFormula.combinedBaseline d R ∧ 0 < d := by
  obtain ⟨i, hi⟩ := radius_grid_cover hR hRhi
  exact baselineSign_sound (checks i) hi (by linarith)

end BlaschkeLebesgue.Certificates.ClippedHull
