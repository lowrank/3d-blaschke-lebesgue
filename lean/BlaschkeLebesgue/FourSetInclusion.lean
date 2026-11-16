module

public import BlaschkeLebesgue.CapBoundaries

/-! # Inclusion-exclusion when no three of four sets overlap -/

public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BlaschkeLebesgue

theorem iUnion_four {α : Type*} (s : Fin 4 → Set α) :
    (⋃ i, s i) = s 0 ∪ s 1 ∪ s 2 ∪ s 3 := by
  ext x
  simp only [mem_iUnion, mem_union, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false]
  change (x ∈ s 0 ∨ x ∈ s 1 ∨ x ∈ s 2 ∨ x ∈ s 3) ↔ _
  tauto

theorem indicator_iUnion_four_of_no_triples {α : Type*} (s : Fin 4 → Set α)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → s i ∩ s j ∩ s k = ∅)
    (f : α → ℝ) :
    (⋃ i, s i).indicator f =
      ((s 0).indicator f + (s 1).indicator f + (s 2).indicator f + (s 3).indicator f) -
      ((s 0 ∩ s 1).indicator f + (s 0 ∩ s 2).indicator f + (s 0 ∩ s 3).indicator f +
        (s 1 ∩ s 2).indicator f + (s 1 ∩ s 3).indicator f + (s 2 ∩ s 3).indicator f) := by
  classical
  funext x
  have h012 : ¬ (x ∈ s 0 ∧ x ∈ s 1 ∧ x ∈ s 2) := by
    rintro ⟨h0, h1, h2⟩
    have h : x ∈ s 0 ∩ s 1 ∩ s 2 := ⟨⟨h0, h1⟩, h2⟩
    rw [ht 0 1 2 (by decide) (by decide) (by decide)] at h
    exact h
  have h013 : ¬ (x ∈ s 0 ∧ x ∈ s 1 ∧ x ∈ s 3) := by
    rintro ⟨h0, h1, h3⟩
    have h : x ∈ s 0 ∩ s 1 ∩ s 3 := ⟨⟨h0, h1⟩, h3⟩
    rw [ht 0 1 3 (by decide) (by decide) (by decide)] at h
    exact h
  have h023 : ¬ (x ∈ s 0 ∧ x ∈ s 2 ∧ x ∈ s 3) := by
    rintro ⟨h0, h2, h3⟩
    have h : x ∈ s 0 ∩ s 2 ∩ s 3 := ⟨⟨h0, h2⟩, h3⟩
    rw [ht 0 2 3 (by decide) (by decide) (by decide)] at h
    exact h
  have h123 : ¬ (x ∈ s 1 ∧ x ∈ s 2 ∧ x ∈ s 3) := by
    rintro ⟨h1, h2, h3⟩
    have h : x ∈ s 1 ∩ s 2 ∩ s 3 := ⟨⟨h1, h2⟩, h3⟩
    rw [ht 1 2 3 (by decide) (by decide) (by decide)] at h
    exact h
  rw [iUnion_four]
  simp only [Pi.sub_apply, Pi.add_apply]
  by_cases h0 : x ∈ s 0 <;> by_cases h1 : x ∈ s 1 <;>
    by_cases h2 : x ∈ s 2 <;> by_cases h3 : x ∈ s 3 <;>
    simp_all only [indicator, mem_inter_iff, mem_union, and_self, or_self,
      false_and, and_false, or_true, or_false, not_true_eq_false,
      not_false_eq_true, ↓reduceIte] <;> ring

theorem integral_iUnion_four_of_no_triples {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Fin 4 → Set α) (hs : ∀ i, MeasurableSet (s i))
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → s i ∩ s j ∩ s k = ∅)
    {f : α → ℝ} (hf : Integrable f μ) :
    (∫ x in ⋃ i, s i, f x ∂μ) =
      ((∫ x in s 0, f x ∂μ) + (∫ x in s 1, f x ∂μ) +
        (∫ x in s 2, f x ∂μ) + (∫ x in s 3, f x ∂μ)) -
      ((∫ x in s 0 ∩ s 1, f x ∂μ) + (∫ x in s 0 ∩ s 2, f x ∂μ) +
        (∫ x in s 0 ∩ s 3, f x ∂μ) + (∫ x in s 1 ∩ s 2, f x ∂μ) +
        (∫ x in s 1 ∩ s 3, f x ∂μ) + (∫ x in s 2 ∩ s 3, f x ∂μ)) := by
  have hi (i : Fin 4) := hf.indicator (hs i)
  have hij (i j : Fin 4) := hf.indicator ((hs i).inter (hs j))
  rw [← integral_indicator (MeasurableSet.iUnion hs), indicator_iUnion_four_of_no_triples s ht f,
    integral_sub' (((hi 0).add (hi 1)).add (hi 2) |>.add (hi 3))
      (((((hij 0 1).add (hij 0 2)).add (hij 0 3)).add (hij 1 2)).add (hij 1 3) |>.add (hij 2 3))]
  rw [integral_add' (((hi 0).add (hi 1)).add (hi 2)) (hi 3),
    integral_add' ((hi 0).add (hi 1)) (hi 2), integral_add' (hi 0) (hi 1),
    integral_add' (((((hij 0 1).add (hij 0 2)).add (hij 0 3)).add (hij 1 2)).add (hij 1 3)) (hij 2 3),
    integral_add' ((((hij 0 1).add (hij 0 2)).add (hij 0 3)).add (hij 1 2)) (hij 1 3),
    integral_add' (((hij 0 1).add (hij 0 2)).add (hij 0 3)) (hij 1 2),
    integral_add' ((hij 0 1).add (hij 0 2)) (hij 0 3), integral_add' (hij 0 1) (hij 0 2)]
  simp only [integral_indicator (hs 0), integral_indicator (hs 1),
    integral_indicator (hs 2), integral_indicator (hs 3),
    integral_indicator ((hs 0).inter (hs 1)), integral_indicator ((hs 0).inter (hs 2)),
    integral_indicator ((hs 0).inter (hs 3)), integral_indicator ((hs 1).inter (hs 2)),
    integral_indicator ((hs 1).inter (hs 3)), integral_indicator ((hs 2).inter (hs 3))]

theorem measureReal_iUnion_four_of_no_triples {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (s : Fin 4 → Set α) (hs : ∀ i, MeasurableSet (s i))
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → s i ∩ s j ∩ s k = ∅) :
    μ.real (⋃ i, s i) = (∑ i, μ.real (s i)) -
      (μ.real (s 0 ∩ s 1) + μ.real (s 0 ∩ s 2) + μ.real (s 0 ∩ s 3) +
        μ.real (s 1 ∩ s 2) + μ.real (s 1 ∩ s 3) + μ.real (s 2 ∩ s 3)) := by
  simpa only [setIntegral_one_eq_measureReal, Fin.sum_univ_four] using
    integral_iUnion_four_of_no_triples s hs ht (integrable_const (1 : ℝ) : Integrable _ μ)

end BlaschkeLebesgue
