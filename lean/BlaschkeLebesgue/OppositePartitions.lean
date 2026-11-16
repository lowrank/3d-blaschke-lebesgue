module

public import BlaschkeLebesgue.OppositeEdgeBounds
public import BlaschkeLebesgue.CompletionRegion

/-! # The three coupled opposite-edge partitions of one tetrahedron -/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

/-- The labelings `01|23`, `02|13`, and `03|21`. Reversing the last edge
does not change either budget. -/
@[expose] def partition (j : Fin 3) : Equiv.Perm (Fin 4) := Equiv.swap 1 j.succ

@[expose] def pairEdgeBudget (j : Fin 3) : ℝ := edgeBudget (c.relabel (partition j))
@[expose] def pairCrossBudget (j : Fin 3) : ℝ := crossBudget (c.relabel (partition j))

theorem pair_budgets_sum (j : Fin 3) :
    pairEdgeBudget c j + pairCrossBudget c j = c.totalDeficit := by
  exact (budgets_sum (c.relabel (partition j))).trans (c.totalDeficit_relabel _)

theorem sum_pairEdgeBudget : ∑ j, pairEdgeBudget c j = c.totalDeficit := by
  norm_num [pairEdgeBudget, partition, edgeBudget, edgeDeficit_relabel,
    Fin.sum_univ_succ, Fin.succ, Equiv.swap_apply_def]
  rw [c.edgeDeficit_symm 2 1]
  unfold totalDeficit
  ring

theorem sum_pairCrossBudget : ∑ j, pairCrossBudget c j = 2 * c.totalDeficit := by
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ ↦ pair_budgets_sum c j)
  rw [Finset.sum_add_distrib, sum_pairEdgeBudget] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  norm_num at hsum
  linarith

/-- All scalar parameters have their certified domain bounds for each of the
three actual partitions, including zero deficits. -/
theorem pair_rectangle_bounds (hA : c.totalDeficit ≤ 2 / 25) (j : Fin 3) :
    let a := pairEdgeBudget c j
    let b := pairCrossBudget c j
    0 ≤ a ∧ 0 ≤ b ∧ a + b = c.totalDeficit ∧
      0 ≤ Completion.obliquity a b ∧ Completion.obliquity a b ≤ 1 / 25 ∧
      0 ≤ Completion.midpointError a b ∧ Completion.midpointError a b < 1 / 16 ∧
      1 / 2 < Completion.rectangleRadius a b ∧
      Completion.rectangleRadius a b ≤ 1 / Real.sqrt 2 := by
  dsimp only
  have ha := edgeBudget_nonneg (c.relabel (partition j))
  have hb := crossBudget_nonneg (c.relabel (partition j))
  have hab : pairEdgeBudget c j + pairCrossBudget c j ≤ 2 / 25 := by
    rw [pair_budgets_sum]
    exact hA
  have hc := Completion.obliquity_bounds ha hb hab
  have he := Completion.midpointError_bounds ha hb hab
  have hT := Completion.rectangleRadius_bounds ha hb hab
  exact ⟨ha, hb, pair_budgets_sum c j, hc.1, hc.2, he.1, he.2, hT.1, hT.2.1⟩

/-- The eventual affine integral certificate is summed with the exact shared
budgets; its three pair inputs cannot be replaced by independent worst cases. -/
theorem sum_pair_affine_bounds {F : Fin 3 → ℝ}
    (hF : ∀ j, 153 / 100000 - 601 / 100000 * pairEdgeBudget c j +
      317 / 20000 * pairCrossBudget c j < F j) :
    459 / 100000 + 2569 / 100000 * c.totalDeficit < ∑ j, F j := by
  have ha := sum_pairEdgeBudget c
  have hb := sum_pairCrossBudget c
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, ← add_assoc] at ha hb ⊢
  apply Completion.sum_affine_bounds
    (a₀ := pairEdgeBudget c 0) (a₁ := pairEdgeBudget c 1) (a₂ := pairEdgeBudget c 2)
    (b₀ := pairCrossBudget c 0) (b₁ := pairCrossBudget c 1) (b₂ := pairCrossBudget c 2)
  · simpa [Fin.succ, add_assoc] using ha
  · simpa [Fin.succ, add_assoc] using hb
  · exact hF 0
  · exact hF 1
  · exact hF 2

end BlaschkeLebesgue.BalancedContacts.Opposite
