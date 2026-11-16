module

public import BlaschkeLebesgue.ContactBallConstraints

/-!
# Strict separation of the removed spherical caps

In the closed enclosing ball, three unit-ball constraints cannot all fail.
More generally, if three distances are at least one, all three are exactly
one. Thus open forbidden intervals cannot overlap on a contact sphere, even
when some edge deficits vanish.
-/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (c : BalancedContacts n E)

theorem radius_lt_norm_of_strict_unit_constraints (l : Fin n) {x : E}
    (hx : ∀ j ≠ l, 1 ≤ ‖x - c.point j‖) {j : Fin n} (hjl : j ≠ l)
    (hw : 0 < c.weight j) (hj : 1 < ‖x - c.point j‖) : c.radius < ‖x‖ := by
  classical
  have hsum : (∑ k ∈ Finset.univ.erase l, c.weight k) <
      ∑ k ∈ Finset.univ.erase l, c.weight k * ‖x - c.point k‖ ^ 2 := by
    apply Finset.sum_lt_sum
    · intro k hk
      have hdist : 1 ≤ ‖x - c.point k‖ ^ 2 := by
        nlinarith [hx k (Finset.mem_erase.mp hk).1]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdist (c.weight_nonneg k)
    · refine ⟨j, by simp [hjl], ?_⟩
      have hdist : 1 < ‖x - c.point j‖ ^ 2 := by nlinarith
      simpa only [mul_one] using mul_lt_mul_of_pos_left hdist hw
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ l), c.weight_sum,
    Finset.sum_erase_eq_sub (Finset.mem_univ l), c.weighted_sq_dist_point] at hsum
  have hnonneg := mul_nonneg (c.weight_nonneg l) (sq_nonneg ‖x - c.point l‖)
  have hweight := c.weight_le l
  nlinarith [norm_nonneg x]

variable (c : BalancedContacts 4 E)

theorem weight_lower (i : Fin 4) : 6 * c.radius ^ 2 - 2 ≤ c.weight i := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase i)
    (fun j _ ↦ c.weight_le j)
  have hcard : (Finset.univ.erase i : Finset (Fin 4)).card = 3 := by simp
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), c.weight_sum,
    Finset.sum_const, hcard] at hsum
  norm_num only [nsmul_eq_mul, Nat.cast_ofNat] at hsum
  linarith

theorem weight_ge_eleven_fiftieths (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    11 / 50 ≤ c.weight i := by
  linarith [c.deficit_lower, c.weight_lower i]

theorem three_unit_constraints_eq_one (hA : c.totalDeficit ≤ 2 / 25)
    (l : Fin 4) {x : E} (hx : ‖x‖ ≤ c.radius)
    (hcons : ∀ j ≠ l, 1 ≤ ‖x - c.point j‖) :
    ∀ j ≠ l, ‖x - c.point j‖ = 1 := by
  intro j hj
  apply le_antisymm _ (hcons j hj)
  by_contra! hbad
  have hw : 0 < c.weight j := lt_of_lt_of_le (by norm_num) (c.weight_ge_eleven_fiftieths hA j)
  exact (not_lt_of_ge hx) (c.radius_lt_norm_of_strict_unit_constraints l hcons hj hw hbad)

theorem no_three_strict_unit_constraints (hA : c.totalDeficit ≤ 2 / 25)
    (l : Fin 4) {x : E} (hx : ‖x‖ ≤ c.radius) :
    ¬ ∀ j ≠ l, 1 < ‖x - c.point j‖ := by
  intro h
  obtain ⟨j, hj⟩ := exists_ne l
  have heq := c.three_unit_constraints_eq_one hA l hx (fun k hk ↦ (h k hk).le) j hj
  exact (ne_of_gt (h j hj)) heq

theorem point_injective_of_small_deficit (hA : c.totalDeficit ≤ 2 / 25) :
    Function.Injective c.point := by
  classical
  intro i j he
  by_contra hij
  have hed : c.edgeDeficit i j = 1 := by simp [edgeDeficit, he]
  have hs : c.weight i + c.weight j ≤ 1 - 2 * c.radius ^ 2 := by
    calc
      _ = ∑ k ∈ ({i, j} : Finset (Fin 4)), c.weight k * c.edgeDeficit i k := by
        rw [Finset.sum_pair hij, c.edgeDeficit_self, hed, mul_one, mul_one]
      _ ≤ ∑ k, c.weight k * c.edgeDeficit i k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ ↦ mul_nonneg (c.weight_nonneg k) (c.edgeDeficit_nonneg i k))
      _ = _ := c.weighted_deficit i
  linarith [c.weight_ge_eleven_fiftieths hA i, c.weight_ge_eleven_fiftieths hA j,
    c.deficit_lower]

end BlaschkeLebesgue.BalancedContacts
