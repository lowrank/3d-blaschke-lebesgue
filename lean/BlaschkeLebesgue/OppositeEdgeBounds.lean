module

public import BlaschkeLebesgue.OppositeEdges

/-! # Normalized opposite-edge and midpoint estimates -/

public noncomputable section

open scoped InnerProductSpace
open NormedSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

theorem firstEdge_norm_lower : Real.sqrt (1 - edgeBudget c) ≤ ‖firstEdge c‖ := by
  apply (Real.sqrt_le_left (norm_nonneg _)).2
  rw [firstEdge_norm_sq]
  have h := c.edgeDeficit_nonneg 2 3
  unfold edgeBudget
  linarith

theorem secondEdge_norm_lower : Real.sqrt (1 - edgeBudget c) ≤ ‖secondEdge c‖ := by
  apply (Real.sqrt_le_left (norm_nonneg _)).2
  rw [secondEdge_norm_sq]
  have h := c.edgeDeficit_nonneg 0 1
  unfold edgeBudget
  linarith

theorem firstEdge_ne_zero (ha : edgeBudget c < 1) : firstEdge c ≠ 0 := by
  have h := firstEdge_norm_lower c
  have hp := Real.sqrt_pos.2 (sub_pos.mpr ha)
  exact norm_pos_iff.mp (lt_of_lt_of_le hp h)

theorem secondEdge_ne_zero (ha : edgeBudget c < 1) : secondEdge c ≠ 0 := by
  have h := secondEdge_norm_lower c
  have hp := Real.sqrt_pos.2 (sub_pos.mpr ha)
  exact norm_pos_iff.mp (lt_of_lt_of_le hp h)

theorem firstAxis_norm (ha : edgeBudget c < 1) : ‖firstAxis c‖ = 1 :=
  norm_normalize (firstEdge_ne_zero c ha)

theorem secondAxis_norm (ha : edgeBudget c < 1) : ‖secondAxis c‖ = 1 :=
  norm_normalize (secondEdge_ne_zero c ha)

theorem axes_inner_abs (ha : edgeBudget c < 1) :
    |⟪firstAxis c, secondAxis c⟫_ℝ| ≤ crossBudget c / (2 * (1 - edgeBudget c)) := by
  have hp : 0 < 1 - edgeBudget c := sub_pos.mpr ha
  have hnorms : 1 - edgeBudget c ≤ ‖firstEdge c‖ * ‖secondEdge c‖ := by
    calc
      _ = Real.sqrt (1 - edgeBudget c) * Real.sqrt (1 - edgeBudget c) :=
        (Real.mul_self_sqrt hp.le).symm
      _ ≤ _ := mul_le_mul (firstEdge_norm_lower c) (secondEdge_norm_lower c)
        (Real.sqrt_nonneg _) (norm_nonneg _)
  have heq : |⟪firstAxis c, secondAxis c⟫_ℝ| =
      |⟪firstEdge c, secondEdge c⟫_ℝ| / (‖firstEdge c‖ * ‖secondEdge c‖) := by
    simp only [firstAxis, secondAxis, NormedSpace.normalize, real_inner_smul_left,
      real_inner_smul_right, abs_mul, abs_inv, abs_norm, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  calc
    _ ≤ (crossBudget c / 2) / (1 - edgeBudget c) :=
      div_le_div₀ (div_nonneg (crossBudget_nonneg c) (by norm_num)) (edges_inner_abs c) hp hnorms
    _ = _ := by rw [div_div]

theorem separation_inner_firstAxis_abs (ha : edgeBudget c < 1) :
    |⟪separation c, firstAxis c⟫_ℝ| ≤
      crossBudget c / (4 * Real.sqrt (1 - edgeBudget c)) := by
  have hp := Real.sqrt_pos.2 (sub_pos.mpr ha)
  have heq : |⟪separation c, firstAxis c⟫_ℝ| =
      |⟪separation c, firstEdge c⟫_ℝ| / ‖firstEdge c‖ := by
    simp [firstAxis, NormedSpace.normalize, real_inner_smul_right, abs_mul, div_eq_mul_inv,
      mul_comm]
  rw [heq]
  calc
    _ ≤ (crossBudget c / 4) / Real.sqrt (1 - edgeBudget c) :=
      div_le_div₀ (div_nonneg (crossBudget_nonneg c) (by norm_num)) (separation_inner_firstEdge_abs c) hp
        (firstEdge_norm_lower c)
    _ = _ := by rw [div_div]

theorem separation_inner_secondAxis_abs (ha : edgeBudget c < 1) :
    |⟪separation c, secondAxis c⟫_ℝ| ≤
      crossBudget c / (4 * Real.sqrt (1 - edgeBudget c)) := by
  have hp := Real.sqrt_pos.2 (sub_pos.mpr ha)
  have heq : |⟪separation c, secondAxis c⟫_ℝ| =
      |⟪separation c, secondEdge c⟫_ℝ| / ‖secondEdge c‖ := by
    simp [secondAxis, NormedSpace.normalize, real_inner_smul_right, abs_mul, div_eq_mul_inv,
      mul_comm]
  rw [heq]
  calc
    _ ≤ (crossBudget c / 4) / Real.sqrt (1 - edgeBudget c) :=
      div_le_div₀ (div_nonneg (crossBudget_nonneg c) (by norm_num)) (separation_inner_secondEdge_abs c) hp
        (secondEdge_norm_lower c)
    _ = _ := by rw [div_div]

theorem firstMidpoint_inner_axis : ⟪firstMidpoint c, firstAxis c⟫_ℝ = 0 := by
  simp [firstAxis, NormedSpace.normalize, real_inner_smul_right, firstMidpoint_inner_edge]

theorem secondMidpoint_inner_axis : ⟪secondMidpoint c, secondAxis c⟫_ℝ = 0 := by
  simp [secondAxis, NormedSpace.normalize, real_inner_smul_right, secondMidpoint_inner_edge]

theorem firstMidpoint_norm_sq_lower :
    1 / 8 - c.totalDeficit / 16 ≤ ‖firstMidpoint c‖ ^ 2 := by
  rw [firstMidpoint_norm_sq, firstEdge_norm_sq]
  have h := c.deficit_lower
  have he := c.edgeDeficit_nonneg 0 1
  linarith

theorem secondMidpoint_norm_sq_lower :
    1 / 8 - c.totalDeficit / 16 ≤ ‖secondMidpoint c‖ ^ 2 := by
  rw [secondMidpoint_norm_sq, secondEdge_norm_sq]
  have h := c.deficit_lower
  have he := c.edgeDeficit_nonneg 2 3
  linarith

end BlaschkeLebesgue.BalancedContacts.Opposite
