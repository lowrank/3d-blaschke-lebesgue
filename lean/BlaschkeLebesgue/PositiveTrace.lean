module

public import BlaschkeLebesgue.SpectralBounds

/-!
# Positive operators and trace products

Elementary consequences of the spectral theorem needed to compare mixed
curvature: a positive operator is bounded above by its trace, a positive
contraction is bounded below by its determinant, and the trace of a product
of positive operators is nonnegative.
-/

public noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace BlaschkeLebesgue

theorem positive_trace_id_sub {A : Space →ₗ[ℝ] Space} (hA : A.IsPositive) :
    (LinearMap.trace ℝ Space A • LinearMap.id - A).IsPositive := by
  let b := hA.isSymmetric.eigenvectorBasis space_finrank
  apply (LinearMap.posSemidef_toMatrix_iff b).1
  rw [map_sub, map_smul, LinearMap.toMatrix_id, hA.isSymmetric.toMatrix_eigenvectorBasis]
  simp only [RCLike.ofReal_real_eq_id, Function.comp_def, id_eq]
  have he : LinearMap.trace ℝ Space A • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      Matrix.diagonal (fun i => (hA.isSymmetric.eigenvalues space_finrank i : ℝ)) =
      Matrix.diagonal (fun i => LinearMap.trace ℝ Space A - hA.isSymmetric.eigenvalues space_finrank i) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.smul_apply]
  rw [he, Matrix.posSemidef_diagonal_iff]
  intro i
  apply sub_nonneg.2
  rw [hA.isSymmetric.trace_eq_sum_eigenvalues space_finrank]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact Finset.single_le_sum (fun j _ => hA.nonneg_eigenvalues space_finrank j) (Finset.mem_univ i)

theorem positiveContraction_sub_det_id {A : Space →ₗ[ℝ] Space}
    (hA : A.IsPositive) (hI : (LinearMap.id - A).IsPositive) :
    (A - A.det • LinearMap.id).IsPositive := by
  let b := hA.isSymmetric.eigenvectorBasis space_finrank
  apply (LinearMap.posSemidef_toMatrix_iff b).1
  rw [map_sub, map_smul, LinearMap.toMatrix_id, hA.isSymmetric.toMatrix_eigenvectorBasis]
  simp only [RCLike.ofReal_real_eq_id, Function.comp_def, id_eq]
  have he : Matrix.diagonal (fun i => (hA.isSymmetric.eigenvalues space_finrank i : ℝ)) -
      A.det • (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.diagonal (fun i => hA.isSymmetric.eigenvalues space_finrank i - A.det) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.smul_apply]
  rw [he, Matrix.posSemidef_diagonal_iff]
  intro i
  apply sub_nonneg.2
  rw [hA.isSymmetric.det_eq_prod_eigenvalues space_finrank]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have h := Finset.prod_le_prod_of_subset_of_le_one₀
    (show ({i} : Finset (Fin 3)) ⊆ Finset.univ from Finset.subset_univ _)
    (fun j _ => (positiveContraction_eigenvalues hA hI j).1)
    (fun j _ _ => (positiveContraction_eigenvalues hA hI j).2)
  simpa only [Finset.prod_singleton] using h

theorem trace_comp_nonneg {A B : Space →ₗ[ℝ] Space} (hA : A.IsPositive) (hB : B.IsPositive) :
    0 ≤ LinearMap.trace ℝ Space (A.comp B) := by
  let b := hA.isSymmetric.eigenvectorBasis space_finrank
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_nonneg
  intro i hi
  change 0 ≤ ⟪b i, A (B (b i))⟫_ℝ
  rw [← hA.isSymmetric (b i) (B (b i))]
  change 0 ≤ ⟪A (hA.isSymmetric.eigenvectorBasis space_finrank i), B (b i)⟫_ℝ
  rw [hA.isSymmetric.apply_eigenvectorBasis, real_inner_smul_left]
  exact mul_nonneg (hA.nonneg_eigenvalues space_finrank i) (hB.inner_nonneg_right (b i))

end BlaschkeLebesgue
