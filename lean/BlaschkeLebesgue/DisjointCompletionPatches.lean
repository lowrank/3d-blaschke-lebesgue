module

public import BlaschkeLebesgue.ActiveSupportLabels
public import BlaschkeLebesgue.OppositePartitions

/-! # The three actual opposite-edge patch pairs are disjoint -/

public noncomputable section

open Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

@[expose] def partitionEdgeLabels (j : Fin 3) (opposite : Bool) : Set (Fin 4) :=
  partition j '' (if opposite then {2, 3} else {0, 1})

theorem partitionEdgeLabels_ne {j k : Fin 3} (hjk : j ≠ k) (s t : Bool) :
    partitionEdgeLabels j s ≠ partitionEdgeLabels k t := by
  fin_cases j <;> fin_cases k
  all_goals try exact (hjk rfl).elim
  all_goals cases s <;> cases t <;>
    norm_num [partitionEdgeLabels, partition, Fin.succ, Equiv.swap_apply_def, Set.ext_iff, Fin.forall_fin_succ]

variable (c : BalancedContacts 4 Space)

theorem partition_totalDeficit_le (hA : c.totalDeficit ≤ 2 / 25) (j : Fin 3) :
    (c.relabel (partition j)).totalDeficit ≤ 2 / 25 := by
  rwa [c.totalDeficit_relabel]

@[expose] def pairFrame (hA : c.totalDeficit ≤ 2 / 25) (j : Fin 3) : ObliqueFrame :=
  Classical.choose (exists_obliqueFrame (c.relabel (partition j)) (partition_totalDeficit_le c hA j))

theorem pairFrame_spec (hA : c.totalDeficit ≤ 2 / 25) (j : Fin 3) :
    (pairFrame c hA j).axis₁ = firstAxis (c.relabel (partition j)) ∧
      (pairFrame c hA j).axis₂ = secondAxis (c.relabel (partition j)) ∧
      ⟪firstMidpoint (c.relabel (partition j)), (pairFrame c hA j).normal⟫_ℝ < 0 ∧
      0 < ⟪secondMidpoint (c.relabel (partition j)), (pairFrame c hA j).normal⟫_ℝ :=
  Classical.choose_spec (exists_obliqueFrame (c.relabel (partition j)) (partition_totalDeficit_le c hA j))

@[expose] def pairPatches (hA : c.totalDeficit ≤ 2 / 25) (j : Fin 3) : Set UnitSphere :=
  activeAntipodalPatches (c.relabel (partition j)) (pairFrame c hA j)

theorem measurableSet_pairPatches (hA : c.totalDeficit ≤ 2 / 25) (j : Fin 3) :
    MeasurableSet (pairPatches c hA j) := measurableSet_activeAntipodalPatches _ _

theorem pairPatches_supportContactLabels (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {j : Fin 3} {u : UnitSphere} (hu : u ∈ pairPatches c hA j) :
    ∃ s : Bool, c.supportContactLabels (clippedOuterBody c.radius (Set.range c.point) hne) u =
      partitionEdgeLabels j s := by
  have hne' : (clippedOuter (c.relabel (partition j)).radius (Set.range (c.relabel (partition j)).point)).Nonempty := by
    rwa [c.clippedOuter_relabel]
  have hf := pairFrame_spec c hA j
  have h := active_antipodal_supportContactLabels (c.relabel (partition j)) (pairFrame c hA j)
    hf.1 hf.2.1 (partition_totalDeficit_le c hA j) hf.2.2.1 hf.2.2.2 (hne := hne') hbound hu
  rw [c.clippedOuterBody_relabel (partition j) hne' hne] at h
  rcases h with h | h
  · have he := congrArg (fun s : Set (Fin 4) ↦ partition j '' s) h
    rw [c.image_supportContactLabels_relabel] at he
    exact ⟨false, he⟩
  · have he := congrArg (fun s : Set (Fin 4) ↦ partition j '' s) h
    rw [c.image_supportContactLabels_relabel] at he
    exact ⟨true, he⟩

theorem pairPatches_pairwise_disjoint (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1) :
    Pairwise (fun j k : Fin 3 ↦ Disjoint (pairPatches c hA j) (pairPatches c hA k)) := by
  intro j k hjk
  apply Set.disjoint_left.2
  intro u hu hv
  obtain ⟨s, hs⟩ := pairPatches_supportContactLabels c hA (hne := hne) hbound hu
  obtain ⟨t, ht⟩ := pairPatches_supportContactLabels c hA (hne := hne) hbound hv
  exact partitionEdgeLabels_ne hjk s t (hs.symm.trans ht)

end BlaschkeLebesgue.BalancedContacts.Opposite
