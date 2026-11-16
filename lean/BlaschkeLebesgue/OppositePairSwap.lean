module

public import BlaschkeLebesgue.ContactRelabeling
public import BlaschkeLebesgue.OppositeEdges
public import BlaschkeLebesgue.InnerOuter

/-! # Exchanging the two edges of an opposite pair preserves the clipped body -/

public noncomputable section

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[expose] def pairSwap : Equiv.Perm (Fin 4) := (Equiv.swap 0 2).trans (Equiv.swap 1 3)
@[expose] def swapped (c : BalancedContacts 4 E) : BalancedContacts 4 E := c.relabel pairSwap

variable (c : BalancedContacts 4 E)

theorem swapped_radius : (swapped c).radius = c.radius := rfl
theorem swapped_firstEdge : firstEdge (swapped c) = secondEdge c := by
  simp [firstEdge, secondEdge, swapped, relabel, pairSwap, Equiv.swap_apply_def]
theorem swapped_secondEdge : secondEdge (swapped c) = firstEdge c := by
  simp [firstEdge, secondEdge, swapped, relabel, pairSwap, Equiv.swap_apply_def]
theorem swapped_firstMidpoint : firstMidpoint (swapped c) = secondMidpoint c := by
  simp [firstMidpoint, secondMidpoint, swapped, relabel, pairSwap, Equiv.swap_apply_def]
theorem swapped_secondMidpoint : secondMidpoint (swapped c) = firstMidpoint c := by
  simp [firstMidpoint, secondMidpoint, swapped, relabel, pairSwap, Equiv.swap_apply_def]
theorem swapped_firstAxis : firstAxis (swapped c) = secondAxis c := by
  simp only [firstAxis, secondAxis, swapped_firstEdge]
theorem swapped_secondAxis : secondAxis (swapped c) = firstAxis c := by
  simp only [firstAxis, secondAxis, swapped_secondEdge]
theorem swapped_totalDeficit : (swapped c).totalDeficit = c.totalDeficit := c.totalDeficit_relabel pairSwap

theorem swapped_edgeBudget : edgeBudget (swapped c) = edgeBudget c := by
  simp only [edgeBudget, swapped, edgeDeficit_relabel]
  norm_num [pairSwap, Equiv.swap_apply_def]
  ring

theorem swapped_crossBudget : crossBudget (swapped c) = crossBudget c := by
  have h := budgets_sum (swapped c)
  rw [swapped_edgeBudget, swapped_totalDeficit] at h
  linarith [budgets_sum c]

theorem swapped_point_range : Set.range (swapped c).point = Set.range c.point := by
  change Set.range (c.point ∘ pairSwap) = _
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨pairSwap i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨pairSwap.symm i, by simp⟩

theorem swapped_clippedOuter :
    clippedOuter (swapped c).radius (Set.range (swapped c).point) =
      clippedOuter c.radius (Set.range c.point) := by rw [swapped_radius, swapped_point_range]

end BlaschkeLebesgue.BalancedContacts.Opposite
