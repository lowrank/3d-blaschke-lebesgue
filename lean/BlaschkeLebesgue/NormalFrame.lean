module

public import BlaschkeLebesgue.CurvatureDensity

/-!
# Orthonormal coordinates adapted to a unit normal

A unit normal extends to an orthonormal basis. In such a basis the normal
projection occupies one diagonal entry and a tangent operator has a zero
first row and column. These facts reduce its determinant identities to two
dimensions without requiring a continuously chosen frame.
-/

public noncomputable section

open Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem exists_normalFrame (u : UnitSphere) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space, b 0 = (u : Space) := by
  let v : Fin 3 → Space := fun _ => u
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    exact fun _ => u.norm_eq_one
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simpa only [Fintype.card_fin] using space_finrank)
  exact ⟨b, hb 0 (by simp)⟩

theorem toMatrix_normalProjection (b : OrthonormalBasis (Fin 3) ℝ Space) :
    LinearMap.toMatrix b.toBasis b.toBasis (normalProjection (b 0)).toLinearMap =
      Matrix.single 0 0 1 := by
  ext i j
  rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply]
  change b.repr (⟪b 0, b j⟫_ℝ • b 0) i = _
  rw [map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, b.repr_self]
  rw [b.inner_eq_ite]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [Matrix.single, hi, hj, eq_comm]

theorem toMatrix_tangent_row_zero (b : OrthonormalBasis (Fin 3) ℝ Space)
    (A : Space →L[ℝ] Space) (hA : ∀ v, ⟪b 0, A v⟫_ℝ = 0) (j : Fin 3) :
    LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap 0 j = 0 := by
  rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply]
  change b.repr (A (b j)) 0 = 0
  rw [b.repr_apply_apply]
  exact hA _

theorem toMatrix_tangent_col_zero (b : OrthonormalBasis (Fin 3) ℝ Space)
    (A : Space →L[ℝ] Space) (hA : A (b 0) = 0) (i : Fin 3) :
    LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap i 0 = 0 := by
  rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply]
  change b.repr (A (b 0)) i = 0
  rw [hA, map_zero]
  rfl

end BlaschkeLebesgue
