module

public import BlaschkeLebesgue.CurvatureOperator
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Scalar bounds for three-dimensional positive contractions

The spectral theorem gives determinant bounds and, when one direction has
eigenvalue one, the two-dimensional trace-determinant inequality.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem space_finrank : Module.finrank ℝ Space = 3 := by simp [Space]

theorem positiveContraction_eigenvalues {A : Space →ₗ[ℝ] Space}
    (hA : A.IsPositive) (hI : (LinearMap.id - A).IsPositive) (i : Fin 3) :
    0 ≤ hA.isSymmetric.eigenvalues space_finrank i ∧
      hA.isSymmetric.eigenvalues space_finrank i ≤ 1 := by
  refine ⟨hA.nonneg_eigenvalues space_finrank i, ?_⟩
  have h := hI.inner_nonneg_left (hA.isSymmetric.eigenvectorBasis space_finrank i)
  simp only [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_left,
    hA.isSymmetric.apply_eigenvectorBasis, real_inner_smul_left,
    real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one,
    RCLike.ofReal_real_eq_id, id_eq] at h
  linarith only [h]

theorem positiveContraction_det_bounds {A : Space →ₗ[ℝ] Space}
    (hA : A.IsPositive) (hI : (LinearMap.id - A).IsPositive) :
    0 ≤ A.det ∧ A.det ≤ 1 := by
  rw [hA.isSymmetric.det_eq_prod_eigenvalues space_finrank]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  constructor
  · exact Finset.prod_nonneg fun i _ => (positiveContraction_eigenvalues hA hI i).1
  · exact Finset.prod_le_one₀ (fun i _ => (positiveContraction_eigenvalues hA hI i).1)
      (fun i _ => (positiveContraction_eigenvalues hA hI i).2)

theorem positiveContraction_trace_le_two_add_det {A : Space →ₗ[ℝ] Space}
    (hA : A.IsPositive) (hI : (LinearMap.id - A).IsPositive)
    {u : Space} (hu : u ≠ 0) (he : A u = u) :
    LinearMap.trace ℝ Space A ≤ 2 + A.det := by
  have heig : Module.End.HasEigenvalue A (1 : ℝ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa only [one_smul] using he), hu⟩
  obtain ⟨i, hi⟩ := hA.isSymmetric.exists_eigenvalues_eq space_finrank heig
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hi
  rw [hA.isSymmetric.trace_eq_sum_eigenvalues space_finrank,
    hA.isSymmetric.det_eq_prod_eigenvalues space_finrank]
  have h0 := (positiveContraction_eigenvalues hA hI 0).2
  have h1 := (positiveContraction_eigenvalues hA hI 1).2
  have h2 := (positiveContraction_eigenvalues hA hI 2).2
  simp only [RCLike.ofReal_real_eq_id, id_eq, Fin.sum_univ_three, Fin.prod_univ_three]
  let a := hA.isSymmetric.eigenvalues space_finrank
  change a i = 1 at hi
  change a 0 + a 1 + a 2 ≤ 2 + a 0 * a 1 * a 2
  change a 0 ≤ 1 at h0
  change a 1 ≤ 1 at h1
  change a 2 ≤ 1 at h2
  fin_cases i
  · change a 0 = 1 at hi
    rw [hi]
    nlinarith only [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  · change a 1 = 1 at hi
    rw [hi]
    nlinarith only [mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h2)]
  · change a 2 = 1 at hi
    rw [hi]
    nlinarith only [mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)]

end BlaschkeLebesgue
