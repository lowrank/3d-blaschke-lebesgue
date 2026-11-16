module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantAnalytic

/-! # The six-edge secant lower bound for the actual weighted clipped volumes -/

public noncomputable section

namespace BlaschkeLebesgue.BalancedContacts

open Certificates.ClippedHull

variable (c : BalancedContacts 4 Space)

theorem sixEdgeSum_mono {f g : ℝ → ℝ}
    (h : ∀ i j : Fin 4, i ≠ j → f ‖c.point j - c.point i‖ ≤ g ‖c.point j - c.point i‖) :
    c.sixEdgeSum f ≤ c.sixEdgeSum g := by
  unfold sixEdgeSum
  linarith only [h 0 1 (by decide), h 0 2 (by decide), h 0 3 (by decide),
    h 1 2 (by decide), h 1 3 (by decide), h 2 3 (by decide)]

theorem sixEdgeSum_deficit : c.sixEdgeSum (fun s ↦ 1 - s ^ 2) = c.totalDeficit := by
  simp only [sixEdgeSum, totalDeficit, edgeDeficit, norm_sub_rev]

theorem sixEdgeSum_mul_deficit (m : ℝ) :
    c.sixEdgeSum (fun s ↦ m * (1 - s ^ 2)) = m * c.totalDeficit := by
  rw [← c.sixEdgeSum_deficit]
  unfold sixEdgeSum
  ring

theorem clipped_volume_combination_ge_secant
    (checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true)
    {S E : ℝ} (hR : 60849 / 100000 ≤ c.radius) (hRS : c.radius ≤ S)
    (hS : S ^ 2 ≤ 3 / 8) (hE : 0 < E) (hEhi : E ≤ 2 / 25)
    (hAE : c.totalDeficit ≤ E)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hR1 : c.radius ≤ 1) :
    ClippedFormula.combinedBaseline c.radius +
      ((ClippedFormula.combinedEdge S E - ClippedFormula.combinedEdge S 0) / E) * c.totalDeficit ≤
      (47 * bodyVolume (clippedInnerBody c.radius (Set.range c.point) hne hR1) -
        bodyVolume (clippedOuterBody c.radius (Set.range c.point) hne)) / 46 := by
  rw [c.clipped_volume_combination_eq_manuscript (hAE.trans hEhi) hR1]
  apply add_le_add le_rfl
  rw [← c.sixEdgeSum_mul_deficit]
  apply c.sixEdgeSum_mono
  intro i j hij
  have hnon := c.edgeDeficit_nonneg j i
  have hu := (c.edgeDeficit_le_totalDeficit (Ne.symm hij)).trans hAE
  exact combinedEdge_increment_secant checks hR hRS hS hE hEhi hnon hu

theorem clipped_volume_combination_ge_bucket
    (checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true)
    (baselineChecks : ∀ i : Fin 32, baselineSignCheck 128 64 i 32 = true)
    {R0 S E L : ℝ} (hR0 : 60849 / 100000 ≤ R0) (hR0R : R0 ≤ c.radius)
    (hRS : c.radius ≤ S) (hS : S ^ 2 ≤ 3 / 8) (hE : 0 < E) (hEhi : E ≤ 2 / 25)
    (hAE : c.totalDeficit ≤ E) (hLA : L ≤ c.totalDeficit)
    (hm : 0 ≤ (ClippedFormula.combinedEdge S E - ClippedFormula.combinedEdge S 0) / E)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hR1 : c.radius ≤ 1) :
    ClippedFormula.combinedBaseline R0 +
      ((ClippedFormula.combinedEdge S E - ClippedFormula.combinedEdge S 0) / E) * L ≤
      (47 * bodyVolume (clippedInnerBody c.radius (Set.range c.point) hne hR1) -
        bodyVolume (clippedOuterBody c.radius (Set.range c.point) hne)) / 46 := by
  have hv := c.clipped_volume_combination_ge_secant (hne := hne) checks (hR0.trans hR0R) hRS hS hE hEhi hAE hR1
  have hbase := combinedBaseline_mono baselineChecks hR0 hR0R (c.radius_sq_le (by decide))
  have hmul := mul_le_mul_of_nonneg_left hLA hm
  exact (add_le_add hbase hmul).trans hv

end BlaschkeLebesgue.BalancedContacts
