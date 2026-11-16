module

public import BlaschkeLebesgue.TwoAxisProjection
public import BlaschkeLebesgue.OppositePartitions

/-! # An oriented common normal for the actual opposite contact edges -/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

theorem weight_lower (i : Fin 4) : 6 * c.radius ^ 2 - 2 ≤ c.weight i := by
  have hs := Finset.sum_le_sum (s := Finset.univ.erase i)
    (fun j _ ↦ c.weight_le j)
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), c.weight_sum] at hs
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  norm_num at hs
  linarith

theorem weight_pos_of_small_deficit (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    0 < c.weight i := by
  have h := c.weight_lower i
  have hR := c.deficit_lower
  linarith

namespace Opposite

theorem common_normal_exists (hA : c.totalDeficit ≤ 2 / 25) :
    ∃ z : E, ‖z‖ = 1 ∧ ⟪z, firstAxis c⟫_ℝ = 0 ∧ ⟪z, secondAxis c⟫_ℝ = 0 ∧
      0 < ⟪separation c, z⟫_ℝ := by
  have ha := edgeBudget_nonneg c
  have hb := crossBudget_nonneg c
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by
    rw [budgets_sum]
    exact hA
  have ha1 : edgeBudget c < 1 := by linarith
  have hc : |⟪firstAxis c, secondAxis c⟫_ℝ| ≤ 1 / 25 :=
    (axes_inner_abs c ha1).trans (Completion.obliquity_bounds ha hb hab).2
  have hroot : (4 / 5 : ℝ) ≤ Real.sqrt (1 - edgeBudget c) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hrootpos : 0 < Real.sqrt (1 - edgeBudget c) := by linarith
  have hsmall : crossBudget c / (4 * Real.sqrt (1 - edgeBudget c)) ≤ 1 / 40 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  apply exists_common_normal (firstAxis_norm c ha1) (secondAxis_norm c ha1) hc
    ((separation_inner_firstAxis_abs c ha1).trans hsmall)
    ((separation_inner_secondAxis_abs c ha1).trans hsmall)
  rw [separation_norm_sq]
  linarith

/-- Projecting the actual contact balance onto a common normal places the two
edge midpoints strictly on opposite sides of the origin. -/
theorem midpoint_signs_of_common_normal (hA : c.totalDeficit ≤ 2 / 25) {z : E}
    (h1 : ⟪z, firstAxis c⟫_ℝ = 0) (h2 : ⟪z, secondAxis c⟫_ℝ = 0)
    (hw : 0 < ⟪separation c, z⟫_ℝ) :
    ⟪firstMidpoint c, z⟫_ℝ < 0 ∧ 0 < ⟪secondMidpoint c, z⟫_ℝ := by
  have h1' : ⟪firstEdge c, z⟫_ℝ = 0 := by
    rw [← NormedSpace.norm_smul_normalize (firstEdge c), real_inner_smul_left,
      real_inner_comm]
    change ‖firstEdge c‖ * ⟪z, firstAxis c⟫_ℝ = 0
    rw [h1, mul_zero]
  have h2' : ⟪secondEdge c, z⟫_ℝ = 0 := by
    rw [← NormedSpace.norm_smul_normalize (secondEdge c), real_inner_smul_left,
      real_inner_comm]
    change ‖secondEdge c‖ * ⟪z, secondAxis c⟫_ℝ = 0
    rw [h2, mul_zero]
  have h10 : ⟪c.point 1, z⟫_ℝ = ⟪c.point 0, z⟫_ℝ := by
    simpa only [firstEdge, inner_sub_left, sub_eq_zero] using h1'
  have h32 : ⟪c.point 3, z⟫_ℝ = ⟪c.point 2, z⟫_ℝ := by
    simpa only [secondEdge, inner_sub_left, sub_eq_zero] using h2'
  have hm1 : ⟪firstMidpoint c, z⟫_ℝ = ⟪c.point 0, z⟫_ℝ := by
    simp only [firstMidpoint, real_inner_smul_left, inner_add_left, h10]
    ring
  have hm2 : ⟪secondMidpoint c, z⟫_ℝ = ⟪c.point 2, z⟫_ℝ := by
    simp only [secondMidpoint, real_inner_smul_left, inner_add_left, h32]
    ring
  have hbalance := congrArg (fun x ↦ ⟪x, z⟫_ℝ) c.balance
  simp only [sum_inner, real_inner_smul_left, inner_zero_left] at hbalance
  norm_num [Fin.sum_univ_succ, Fin.succ] at hbalance
  rw [h10, h32] at hbalance
  rw [separation, inner_sub_left, hm1, hm2] at hw
  rw [hm1, hm2]
  have hp : 0 < c.weight 0 + c.weight 1 :=
    add_pos (c.weight_pos_of_small_deficit hA 0) (c.weight_pos_of_small_deficit hA 1)
  have hq : 0 < c.weight 2 + c.weight 3 :=
    add_pos (c.weight_pos_of_small_deficit hA 2) (c.weight_pos_of_small_deficit hA 3)
  constructor
  · by_contra! hh
    have hh' : 0 < ⟪c.point 2, z⟫_ℝ := by linarith
    have hp' := mul_nonneg hp.le hh
    have hq' := mul_pos hq hh'
    nlinarith
  · by_contra! hh
    have hh' : ⟪c.point 0, z⟫_ℝ < 0 := by linarith
    have hp' := mul_neg_of_pos_of_neg hp hh'
    have hq' := mul_nonpos_of_nonneg_of_nonpos hq.le hh
    nlinarith

theorem oriented_common_normal (hA : c.totalDeficit ≤ 2 / 25) :
    ∃ z : E, ‖z‖ = 1 ∧ ⟪z, firstAxis c⟫_ℝ = 0 ∧ ⟪z, secondAxis c⟫_ℝ = 0 ∧
      ⟪firstMidpoint c, z⟫_ℝ < 0 ∧ 0 < ⟪secondMidpoint c, z⟫_ℝ := by
  obtain ⟨z, hz, h1, h2, hw⟩ := common_normal_exists c hA
  exact ⟨z, hz, h1, h2, midpoint_signs_of_common_normal c hA h1 h2 hw⟩

end Opposite
end BlaschkeLebesgue.BalancedContacts
