module

public import BlaschkeLebesgue.Basic

/-!
# Balanced contacts and edge deficits

The configuration here consists of actual points on a sphere, nonnegative balancing
weights, and pairwise distances at most one. `ContactExistence.lean` constructs such
configurations from actual minimum enclosing balls. The statements below prove the
algebraic consequences in §3 without taking any deficit estimate as a hypothesis.
-/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite balanced contacts on a common sphere, with diameter at most one. -/
structure BalancedContacts (n : ℕ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  point : Fin n → E
  weight : Fin n → ℝ
  radius : ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  balance : ∑ i, weight i • point i = 0
  on_sphere : ∀ i, ‖point i‖ = radius
  diameter_le : ∀ i j, ‖point i - point j‖ ≤ 1

namespace BalancedContacts

variable {n : ℕ} (c : BalancedContacts n E)

theorem weighted_sq_dist (i : Fin n) :
    ∑ j, c.weight j * ‖c.point i - c.point j‖ ^ 2 = 2 * c.radius ^ 2 := by
  have hinner : ∑ j, c.weight j * ⟪c.point i, c.point j⟫_ℝ = 0 := by
    have h := congrArg (fun v ↦ ⟪c.point i, v⟫_ℝ) c.balance
    simpa [inner_sum, real_inner_smul_right] using h
  calc
    _ = (∑ j, c.weight j) * (2 * c.radius ^ 2) -
        2 * ∑ j, c.weight j * ⟪c.point i, c.point j⟫_ℝ := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_sub_sq_real, c.on_sphere i, c.on_sphere j]
      ring
    _ = _ := by rw [c.weight_sum, hinner]; ring

theorem weight_le (i : Fin n) : c.weight i ≤ 1 - 2 * c.radius ^ 2 := by
  classical
  have hle : 2 * c.radius ^ 2 ≤ 1 - c.weight i := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, c.weight j * ‖c.point i - c.point j‖ ^ 2 := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), c.weighted_sq_dist]
        simp
      _ ≤ ∑ j ∈ Finset.univ.erase i, c.weight j := by
        apply Finset.sum_le_sum
        intro j _
        have hs := (sq_le_sq₀ (norm_nonneg (c.point i - c.point j)) zero_le_one).2
          (c.diameter_le i j)
        simpa using mul_le_mul_of_nonneg_left hs (c.weight_nonneg j)
      _ = _ := by rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), c.weight_sum]
  linarith

/-- The finite balanced-contact form of Jung's upper bound. -/
theorem radius_sq_le (hn : n ≤ 4) : c.radius ^ 2 ≤ 3 / 8 := by
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ c.weight_le i
  simp only [c.weight_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hpos : 0 < (n : ℝ) := by
    by_contra! h
    have : n = 0 := by exact_mod_cast (le_antisymm h (Nat.cast_nonneg n))
    subst n
    simpa using c.weight_sum
  have hcast : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  have hfactor : 0 ≤ 1 - 2 * c.radius ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hcast hfactor]

/-- A squared-edge deficit. The diagonal is not an edge and is excluded from totals. -/
@[expose] def edgeDeficit (i j : Fin n) : ℝ := 1 - ‖c.point i - c.point j‖ ^ 2

theorem edgeDeficit_nonneg (i j : Fin n) : 0 ≤ c.edgeDeficit i j := by
  have hs := (sq_le_sq₀ (norm_nonneg (c.point i - c.point j)) zero_le_one).2
    (c.diameter_le i j)
  simpa [edgeDeficit] using sub_nonneg.mpr hs

theorem edgeDeficit_symm (i j : Fin n) : c.edgeDeficit i j = c.edgeDeficit j i := by
  simp only [edgeDeficit, norm_sub_rev]

@[simp] theorem edgeDeficit_self (i : Fin n) : c.edgeDeficit i i = 1 := by
  simp [edgeDeficit]

theorem weighted_deficit (i : Fin n) :
    ∑ j, c.weight j * c.edgeDeficit i j = 1 - 2 * c.radius ^ 2 := by
  simp only [edgeDeficit, mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [c.weight_sum, c.weighted_sq_dist]

variable (c : BalancedContacts 4 E)

/-- The sum of the six distinct squared-edge deficits. -/
@[expose] def totalDeficit : ℝ :=
  c.edgeDeficit 0 1 + c.edgeDeficit 0 2 + c.edgeDeficit 0 3 +
    c.edgeDeficit 1 2 + c.edgeDeficit 1 3 + c.edgeDeficit 2 3

theorem totalDeficit_nonneg : 0 ≤ c.totalDeficit := by
  unfold totalDeficit
  linarith [c.edgeDeficit_nonneg 0 1, c.edgeDeficit_nonneg 0 2,
    c.edgeDeficit_nonneg 0 3, c.edgeDeficit_nonneg 1 2,
    c.edgeDeficit_nonneg 1 3, c.edgeDeficit_nonneg 2 3]

/-- The unscaled centroid identity, equivalent to equation (3.5). -/
theorem totalDeficit_eq :
    c.totalDeficit = 6 - 16 * c.radius ^ 2 +
      ‖c.point 0 + c.point 1 + c.point 2 + c.point 3‖ ^ 2 := by
  simp only [totalDeficit, edgeDeficit, norm_sub_sq_real, norm_add_sq_real,
    inner_add_left, c.on_sphere]
  ring

theorem deficit_lower : 16 * (3 / 8 - c.radius ^ 2) ≤ c.totalDeficit := by
  rw [c.totalDeficit_eq]
  nlinarith [sq_nonneg ‖c.point 0 + c.point 1 + c.point 2 + c.point 3‖]

theorem weighted_totalDeficit :
    (c.weight 0 + c.weight 1) * c.edgeDeficit 0 1 +
      (c.weight 0 + c.weight 2) * c.edgeDeficit 0 2 +
      (c.weight 0 + c.weight 3) * c.edgeDeficit 0 3 +
      (c.weight 1 + c.weight 2) * c.edgeDeficit 1 2 +
      (c.weight 1 + c.weight 3) * c.edgeDeficit 1 3 +
      (c.weight 2 + c.weight 3) * c.edgeDeficit 2 3 = 3 - 8 * c.radius ^ 2 := by
  have h₀ := c.weighted_deficit 0
  have h₁ := c.weighted_deficit 1
  have h₂ := c.weighted_deficit 2
  have h₃ := c.weighted_deficit 3
  have hs := c.weight_sum
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h₀ h₁ h₂ h₃ hs
  norm_num [Fin.succ, c.edgeDeficit_self] at h₀ h₁ h₂ h₃ hs
  rw [c.edgeDeficit_symm 1 0] at h₁
  rw [c.edgeDeficit_symm 2 0, c.edgeDeficit_symm 2 1] at h₂
  rw [c.edgeDeficit_symm 3 0, c.edgeDeficit_symm 3 1, c.edgeDeficit_symm 3 2] at h₃
  nlinarith

/-- The weighted lower bound for the total deficit, before division. -/
theorem deficit_upper_mul :
    (4 * c.radius ^ 2 - 1) * c.totalDeficit ≤ 3 - 8 * c.radius ^ 2 := by
  have hs := c.weight_sum
  norm_num [Fin.sum_univ_succ] at hs
  have hw₀ := c.weight_le 0
  have hw₁ := c.weight_le 1
  have hw₂ := c.weight_le 2
  have hw₃ := c.weight_le 3
  have hp₀₁ : 4 * c.radius ^ 2 - 1 ≤ c.weight 0 + c.weight 1 := by linarith
  have hp₀₂ : 4 * c.radius ^ 2 - 1 ≤ c.weight 0 + c.weight 2 := by linarith
  have hp₀₃ : 4 * c.radius ^ 2 - 1 ≤ c.weight 0 + c.weight 3 := by linarith
  have hp₁₂ : 4 * c.radius ^ 2 - 1 ≤ c.weight 1 + c.weight 2 := by linarith
  have hp₁₃ : 4 * c.radius ^ 2 - 1 ≤ c.weight 1 + c.weight 3 := by linarith
  have hp₂₃ : 4 * c.radius ^ 2 - 1 ≤ c.weight 2 + c.weight 3 := by linarith
  have h₀₁ := mul_le_mul_of_nonneg_right hp₀₁ (c.edgeDeficit_nonneg 0 1)
  have h₀₂ := mul_le_mul_of_nonneg_right hp₀₂ (c.edgeDeficit_nonneg 0 2)
  have h₀₃ := mul_le_mul_of_nonneg_right hp₀₃ (c.edgeDeficit_nonneg 0 3)
  have h₁₂ := mul_le_mul_of_nonneg_right hp₁₂ (c.edgeDeficit_nonneg 1 2)
  have h₁₃ := mul_le_mul_of_nonneg_right hp₁₃ (c.edgeDeficit_nonneg 1 3)
  have h₂₃ := mul_le_mul_of_nonneg_right hp₂₃ (c.edgeDeficit_nonneg 2 3)
  have htotal := c.weighted_totalDeficit
  unfold totalDeficit
  nlinarith

/-- The full deficit budget (3.4), in the range needed by the clipped-body branch. -/
theorem deficit_budget (hR : 60849 / 100000 ≤ c.radius) :
    16 * (3 / 8 - c.radius ^ 2) ≤ c.totalDeficit ∧
      c.totalDeficit ≤ 16 * (3 / 8 - c.radius ^ 2) /
        (1 - 8 * (3 / 8 - c.radius ^ 2)) ∧ c.totalDeficit < 2 / 25 := by
  have hsq : (60849 / 100000 : ℝ) ^ 2 ≤ c.radius ^ 2 := by
    nlinarith [sq_nonneg (c.radius - 60849 / 100000)]
  have hden : 0 < 1 - 8 * (3 / 8 - c.radius ^ 2) := by nlinarith
  have hu := c.deficit_upper_mul
  have hupper : c.totalDeficit ≤ 16 * (3 / 8 - c.radius ^ 2) /
      (1 - 8 * (3 / 8 - c.radius ^ 2)) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  refine ⟨c.deficit_lower, hupper, hupper.trans_lt ?_⟩
  apply (div_lt_iff₀ hden).2
  nlinarith

end BalancedContacts

end BlaschkeLebesgue
