module

public import BlaschkeLebesgue.Contacts

/-!
# Excluding triple unit-sphere intersections by the contact balance

The weighted squared-distance identity holds at every point, not only at a
contact. Combined with the contact weight bound it gives a direct proof that
three unit spheres cannot meet inside the enclosing ball. This avoids any
choice of face normals or assumption of tetrahedral incidence.
-/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (c : BalancedContacts n E)

theorem weighted_sq_dist_point (x : E) :
    ∑ j, c.weight j * ‖x - c.point j‖ ^ 2 = ‖x‖ ^ 2 + c.radius ^ 2 := by
  have hinner : ∑ j, c.weight j * ⟪x, c.point j⟫_ℝ = 0 := by
    have h := congrArg (fun v ↦ ⟪x, v⟫_ℝ) c.balance
    simpa [inner_sum, real_inner_smul_right] using h
  calc
    _ = (∑ j, c.weight j) * (‖x‖ ^ 2 + c.radius ^ 2) -
        2 * ∑ j, c.weight j * ⟪x, c.point j⟫_ℝ := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_sub_sq_real, c.on_sphere j]
      ring
    _ = _ := by rw [c.weight_sum, hinner]; ring

/-- A point at distance at least one from all contacts except possibly one
must lie on or outside the enclosing sphere. -/
theorem radius_le_norm_of_unit_constraints (l : Fin n) {x : E}
    (hx : ∀ j ≠ l, 1 ≤ ‖x - c.point j‖) : c.radius ≤ ‖x‖ := by
  classical
  have hsum : 1 - c.weight l ≤ ∑ j, c.weight j * ‖x - c.point j‖ ^ 2 := by
    calc
      _ = ∑ j ∈ Finset.univ.erase l, c.weight j := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ l), c.weight_sum]
      _ ≤ ∑ j ∈ Finset.univ.erase l, c.weight j * ‖x - c.point j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hd := (sq_le_sq₀ zero_le_one (norm_nonneg _)).2 (hx j (Finset.mem_erase.mp hj).1)
        simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_left hd (c.weight_nonneg j)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset l _)
        (fun j _ _ ↦ mul_nonneg (c.weight_nonneg j) (sq_nonneg _))
  rw [c.weighted_sq_dist_point] at hsum
  have hw := c.weight_le l
  nlinarith [norm_nonneg x]

/-- In particular, for four contacts there is no triple unit-sphere
intersection in the open enclosing ball, including zero edge deficits. -/
theorem no_unit_constraints_in_open_ball (l : Fin n) {x : E} (hx : ‖x‖ < c.radius) :
    ¬ ∀ j ≠ l, ‖x - c.point j‖ = 1 := by
  intro h
  exact (not_le_of_gt hx) (c.radius_le_norm_of_unit_constraints l (fun j hj ↦ (h j hj).ge))

theorem weight_lt_of_positive_deficit {l j : Fin n} (hlj : l ≠ j)
    (hwj : 0 < c.weight j) (hej : 0 < c.edgeDeficit l j) :
    c.weight l < 1 - 2 * c.radius ^ 2 := by
  classical
  have hjmem : j ∈ Finset.univ.erase l := by simp [hlj.symm]
  have hle := Finset.single_le_sum (f := fun k ↦ c.weight k * c.edgeDeficit l k)
    (fun k _ ↦ mul_nonneg (c.weight_nonneg k) (c.edgeDeficit_nonneg l k)) hjmem
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ l), c.weighted_deficit,
    c.edgeDeficit_self, mul_one] at hle
  have hp := mul_pos hwj hej
  linarith

/-- A single positive incident deficit with positive weight excludes even the
closed enclosing ball. -/
theorem no_unit_constraints_in_closed_ball {l j : Fin n} (hlj : l ≠ j)
    (hwj : 0 < c.weight j) (hej : 0 < c.edgeDeficit l j) {x : E}
    (hx : ‖x‖ ≤ c.radius) : ¬ ∀ k ≠ l, ‖x - c.point k‖ = 1 := by
  classical
  intro h
  have hsum := c.weighted_sq_dist_point x
  have hrest : (∑ k ∈ Finset.univ.erase l, c.weight k * ‖x - c.point k‖ ^ 2) =
      1 - c.weight l := by
    calc
      _ = ∑ k ∈ Finset.univ.erase l, c.weight k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [h k (Finset.mem_erase.mp hk).1]
        ring
      _ = _ := by rw [Finset.sum_erase_eq_sub (Finset.mem_univ l), c.weight_sum]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ l), hsum] at hrest
  have hw := c.weight_lt_of_positive_deficit hlj hwj hej
  have hnonneg := mul_nonneg (c.weight_nonneg l) (sq_nonneg ‖x - c.point l‖)
  have hs := (sq_le_sq₀ (norm_nonneg x) (le_trans (norm_nonneg x) hx)).2 hx
  nlinarith

end BlaschkeLebesgue.BalancedContacts
