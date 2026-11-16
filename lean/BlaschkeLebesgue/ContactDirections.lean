module

public import BlaschkeLebesgue.ContactExistence

/-! # Angular separation derived from the balanced contacts -/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (c : BalancedContacts n E)

@[expose] def direction (i : Fin n) : E := c.radius⁻¹ • c.point i

theorem direction_norm (hR : 0 < c.radius) (i : Fin n) : ‖c.direction i‖ = 1 := by
  simp [direction, norm_smul, c.on_sphere i, abs_of_pos hR, hR.ne']

theorem radius_smul_direction (hR : 0 < c.radius) (i : Fin n) :
    c.radius • c.direction i = c.point i := by
  simp [direction, smul_smul, hR.ne']

theorem direction_balance : ∑ i, c.weight i • c.direction i = 0 := by
  calc
    _ = c.radius⁻¹ • ∑ i, c.weight i • c.point i := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun i _ ↦ smul_comm _ _ _)
    _ = 0 := by rw [c.balance, smul_zero]

theorem direction_inner_scale (i j : Fin n) :
    ⟪c.direction i, c.direction j⟫_ℝ =
      c.radius⁻¹ ^ 2 * ⟪c.point i, c.point j⟫_ℝ := by
  simp only [direction, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Diameter one gives the lower scalar-product bound for any radius interval. -/
theorem direction_inner_lower (hR : 0 < c.radius) {η : ℝ}
    (hbudget : 1 ≤ 2 * c.radius ^ 2 * (1 + η)) (i j : Fin n) :
    -η ≤ ⟪c.direction i, c.direction j⟫_ℝ := by
  have hdist := (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 (c.diameter_le i j)
  rw [norm_sub_sq_real, c.on_sphere i, c.on_sphere j] at hdist
  have hscale : c.radius ^ 2 * ⟪c.direction i, c.direction j⟫_ℝ =
      ⟪c.point i, c.point j⟫_ℝ := by
    rw [c.direction_inner_scale]
    field_simp
  have hprod : 0 ≤ c.radius ^ 2 * (⟪c.direction i, c.direction j⟫_ℝ + η) := by
    nlinarith
  have hsum := nonneg_of_mul_nonneg_right hprod (sq_pos_of_pos hR)
  linarith

theorem weight_le_of_radius_budget {η : ℝ} (hη : 0 ≤ η)
    (hbudget : 1 ≤ 2 * c.radius ^ 2 * (1 + η)) (i : Fin n) :
    c.weight i ≤ η / (1 + η) := by
  apply (le_div_iff₀ (by positivity)).2
  have h := mul_le_mul_of_nonneg_right (c.weight_le i) (show 0 ≤ 1 + η by positivity)
  nlinarith

/-- The upper scalar-product bound `eq:contactupper` follows jointly from the
four balancing weights and the lower bounds for the other scalar products. -/
theorem direction_inner_upper (c : BalancedContacts 4 E) (hR : 0 < c.radius)
    {η : ℝ} (hη : 0 ≤ η) (hη' : η < 1)
    (hbudget : 1 ≤ 2 * c.radius ^ 2 * (1 + η))
    (i j : Fin 4) (hij : i ≠ j) :
    ⟪c.direction i, c.direction j⟫_ℝ ≤ 4 * η ^ 2 / (1 - η) - 1 := by
  classical
  let S := (Finset.univ.erase i).erase j
  let t := ⟪c.direction i, c.direction j⟫_ℝ
  let A := c.weight i + c.weight j
  have hjmem : j ∈ Finset.univ.erase i := by simp [hij.symm]
  have hcard : S.card = 2 := by
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ i)]
    norm_num
  have hweights : ∑ k ∈ S, c.weight k = 1 - A := by
    rw [Finset.sum_erase_eq_sub hjmem, Finset.sum_erase_eq_sub (Finset.mem_univ i),
      c.weight_sum]
    dsimp [A]
    ring
  have hsmall := Finset.sum_le_sum (s := S)
    (fun k _ ↦ c.weight_le_of_radius_budget hη hbudget k)
  rw [hweights, Finset.sum_const, hcard, nsmul_eq_mul] at hsmall
  have hA : 1 - η ≤ A * (1 + η) := by
    have hh := (le_div_iff₀ (show 0 < 1 + η by positivity)).1
      (show 1 - A ≤ 2 * η / (1 + η) by simpa [mul_div_assoc] using hsmall)
    nlinarith
  let f := fun k ↦ c.weight k * ⟪c.direction i + c.direction j, c.direction k⟫_ℝ
  have hsum : ∑ k, f k = 0 := by
    have hh := congrArg (fun v ↦ ⟪c.direction i + c.direction j, v⟫_ℝ) c.direction_balance
    simpa [f, inner_sum, real_inner_smul_right] using hh
  have hfi : f i = c.weight i * (1 + t) := by
    dsimp [f, t]
    rw [inner_add_left, real_inner_self_eq_norm_sq, c.direction_norm hR i,
      real_inner_comm (c.direction i) (c.direction j)]
    norm_num
  have hfj : f j = c.weight j * (1 + t) := by
    dsimp [f, t]
    rw [inner_add_left, real_inner_self_eq_norm_sq, c.direction_norm hR j]
    ring
  have hrest : ∑ k ∈ S, f k = -A * (1 + t) := by
    rw [Finset.sum_erase_eq_sub hjmem, Finset.sum_erase_eq_sub (Finset.mem_univ i),
      hsum, hfi, hfj]
    dsimp [A]
    ring
  have hpair := Finset.sum_le_sum (s := S) (fun k _ ↦
    mul_le_mul_of_nonneg_left
      (show -2 * η ≤ ⟪c.direction i + c.direction j, c.direction k⟫_ℝ by
        rw [inner_add_left]
        linarith [c.direction_inner_lower hR hbudget i k,
          c.direction_inner_lower hR hbudget j k]) (c.weight_nonneg k))
  change (∑ k ∈ S, c.weight k * (-2 * η)) ≤ ∑ k ∈ S, f k at hpair
  rw [← Finset.sum_mul, hweights, hrest] at hpair
  have ht : 0 ≤ 1 + t + 2 * η := by
    have hh := c.direction_inner_lower hR hbudget i j
    change -η ≤ t at hh
    linarith
  have hleft := mul_le_mul_of_nonneg_right hA ht
  have hright := mul_le_mul_of_nonneg_right
    (show A * (1 + t + 2 * η) ≤ 2 * η by nlinarith [hpair])
      (show 0 ≤ 1 + η by positivity)
  have hfinal : (t + 1) * (1 - η) ≤ 4 * η ^ 2 := by nlinarith [hleft, hright]
  have hh := (le_div_iff₀ (sub_pos.mpr hη')).2 hfinal
  change t ≤ _
  linarith

end BlaschkeLebesgue.BalancedContacts
