module

public import BlaschkeLebesgue.Basic
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Compact convex hulls in finite dimensions -/

public noncomputable section

open scoped BigOperators

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Carathéodory's representation, reindexed by a finite initial segment. -/
theorem exists_small_positive_convex_combination {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) :
    ∃ n ≤ Module.finrank ℝ E + 1, ∃ (w : Fin n → ℝ) (z : Fin n → E),
      AffineIndependent ℝ z ∧ (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x := by
  classical
  obtain ⟨ι, hι, z, w, hz, haff, hw, hsum, hx⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  let := hι
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, ?_, w ∘ e.symm, z ∘ e.symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact haff.card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  · exact haff.comp_embedding e.symm.toEmbedding
  · exact fun i ↦ hw (e.symm i)
  · simpa only [Function.comp_apply] using (e.symm.sum_comp w).trans hsum
  · exact fun i ↦ hz ⟨e.symm i, rfl⟩
  · simpa only [Function.comp_apply] using
      (e.symm.sum_comp (fun i ↦ w i • z i)).trans hx

theorem exists_small_convex_combination {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) :
    ∃ n ≤ Module.finrank ℝ E + 1, ∃ (w : Fin n → ℝ) (z : Fin n → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x := by
  obtain ⟨n, hn, w, z, _, hw, hsum, hz, hx⟩ :=
    exists_small_positive_convex_combination hx
  exact ⟨n, hn, w, z, fun i ↦ (hw i).le, hsum, hz, hx⟩

omit [FiniteDimensional ℝ E] in
/-- All convex combinations with a fixed number of points in a compact set form a
compact set. The weights lie in a compact cube and have sum one. -/
theorem isCompact_convex_combinations {s : Set E} (hs : IsCompact s) (n : ℕ) :
    IsCompact {x : E | ∃ (w : Fin n → ℝ) (z : Fin n → E),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x} := by
  classical
  let W : Set (Fin n → ℝ) := {w | (∀ i, w i ∈ Set.Icc 0 1) ∧ ∑ i, w i = 1}
  let Z : Set (Fin n → E) := {z | ∀ i, z i ∈ s}
  have hW : IsCompact W :=
    (isCompact_pi_infinite (fun _ ↦ isCompact_Icc)).inter_right
      (isClosed_eq (by fun_prop) continuous_const)
  have hZ : IsCompact Z := isCompact_pi_infinite (fun _ ↦ hs)
  have himage := (hW.prod hZ).image
    (show Continuous (fun p : (Fin n → ℝ) × (Fin n → E) ↦ ∑ i, p.1 i • p.2 i) by
      fun_prop)
  convert himage using 1
  ext x
  constructor
  · rintro ⟨w, z, hw, hsum, hz, hx⟩
    refine ⟨(w, z), ⟨⟨fun i ↦ ⟨hw i, ?_⟩, hsum⟩, hz⟩, hx⟩
    calc
      w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ ↦ hw j) (Finset.mem_univ i)
      _ = 1 := hsum
  · rintro ⟨⟨w, z⟩, ⟨⟨hw, hsum⟩, hz⟩, hx⟩
    exact ⟨w, z, fun i ↦ (hw i).1, hsum, hz, hx⟩

/-- In finite dimensions the convex hull of a compact set is compact. -/
theorem isCompact_convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  let C (n : ℕ) : Set E := {x | ∃ (w : Fin n → ℝ) (z : Fin n → E),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x}
  have heq : convexHull ℝ s = ⋃ n : Fin (Module.finrank ℝ E + 2), C n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, w, z, hw, hsum, hz, hx⟩ := exists_small_convex_combination hx
      exact Set.mem_iUnion.2 ⟨⟨n, by omega⟩, w, z, hw, hsum, hz, hx⟩
    · intro hx
      obtain ⟨n, w, z, hw, hsum, hz, hx⟩ := Set.mem_iUnion.1 hx
      exact mem_convexHull_of_exists_fintype w z hw hsum hz hx
  rw [heq]
  exact isCompact_iUnion (fun n ↦ isCompact_convex_combinations hs n)

end BlaschkeLebesgue
