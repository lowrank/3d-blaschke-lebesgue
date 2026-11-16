module

public import BlaschkeLebesgue.ContactRelabeling
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Exact geometry of opposite contact edges

The formulas are proved for the partition `01|23`. `relabel` applies them to
every partition of the same four actual contact points. In particular, the two
deficit budgets below are sums of disjoint subsets of the six actual deficits.
-/

public noncomputable section

open scoped InnerProductSpace BigOperators
open NormedSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

@[expose] def firstEdge : E := c.point 1 - c.point 0
@[expose] def secondEdge : E := c.point 3 - c.point 2
@[expose] def firstMidpoint : E := (1 / 2 : ℝ) • (c.point 0 + c.point 1)
@[expose] def secondMidpoint : E := (1 / 2 : ℝ) • (c.point 2 + c.point 3)
@[expose] def separation : E := secondMidpoint c - firstMidpoint c
@[expose] def firstAxis : E := normalize (firstEdge c)
@[expose] def secondAxis : E := normalize (secondEdge c)
@[expose] def edgeBudget : ℝ := c.edgeDeficit 0 1 + c.edgeDeficit 2 3
@[expose] def crossBudget : ℝ :=
  c.edgeDeficit 0 2 + c.edgeDeficit 0 3 + c.edgeDeficit 1 2 + c.edgeDeficit 1 3

theorem edgeBudget_nonneg : 0 ≤ edgeBudget c :=
  add_nonneg (c.edgeDeficit_nonneg 0 1) (c.edgeDeficit_nonneg 2 3)

theorem crossBudget_nonneg : 0 ≤ crossBudget c := by
  unfold crossBudget
  linarith [c.edgeDeficit_nonneg 0 2, c.edgeDeficit_nonneg 0 3,
    c.edgeDeficit_nonneg 1 2, c.edgeDeficit_nonneg 1 3]

theorem budgets_sum : edgeBudget c + crossBudget c = c.totalDeficit := by
  unfold edgeBudget crossBudget totalDeficit
  ring

theorem firstEdge_norm_sq : ‖firstEdge c‖ ^ 2 = 1 - c.edgeDeficit 0 1 := by
  simp [firstEdge, edgeDeficit, norm_sub_rev]

theorem secondEdge_norm_sq : ‖secondEdge c‖ ^ 2 = 1 - c.edgeDeficit 2 3 := by
  simp [secondEdge, edgeDeficit, norm_sub_rev]

theorem separation_norm_sq :
    ‖separation c‖ ^ 2 = 1 / 2 + (edgeBudget c - crossBudget c) / 4 := by
  simp only [separation, firstMidpoint, secondMidpoint, edgeBudget, crossBudget,
    edgeDeficit, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm (c.point 1) (c.point 0),
    real_inner_comm (c.point 2) (c.point 0), real_inner_comm (c.point 3) (c.point 0),
    real_inner_comm (c.point 2) (c.point 1), real_inner_comm (c.point 3) (c.point 1),
    real_inner_comm (c.point 3) (c.point 2)]
  ring

/-- The constant terms cancel in the alternating sum of four cross distances. -/
theorem edges_inner :
    2 * ⟪firstEdge c, secondEdge c⟫_ℝ =
      c.edgeDeficit 0 2 - c.edgeDeficit 0 3 - c.edgeDeficit 1 2 +
        c.edgeDeficit 1 3 := by
  simp only [firstEdge, secondEdge, edgeDeficit, norm_sub_sq_real,
    inner_sub_left, inner_sub_right]
  ring

theorem separation_inner_firstEdge :
    4 * ⟪separation c, firstEdge c⟫_ℝ =
      c.edgeDeficit 1 2 + c.edgeDeficit 1 3 - c.edgeDeficit 0 2 -
        c.edgeDeficit 0 3 := by
  simp only [separation, firstMidpoint, secondMidpoint, firstEdge, edgeDeficit,
    norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_add_left,
    real_inner_smul_left]
  simp only [real_inner_comm (c.point 2) (c.point 0),
    real_inner_comm (c.point 3) (c.point 0), real_inner_comm (c.point 2) (c.point 1),
    real_inner_comm (c.point 3) (c.point 1), real_inner_comm (c.point 1) (c.point 0),
    real_inner_self_eq_norm_sq, c.on_sphere]
  ring

theorem separation_inner_secondEdge :
    4 * ⟪separation c, secondEdge c⟫_ℝ =
      c.edgeDeficit 0 2 + c.edgeDeficit 1 2 - c.edgeDeficit 0 3 -
        c.edgeDeficit 1 3 := by
  simp only [separation, firstMidpoint, secondMidpoint, secondEdge, edgeDeficit,
    norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_add_left,
    real_inner_smul_left]
  simp only [real_inner_comm (c.point 3) (c.point 2),
    real_inner_self_eq_norm_sq, c.on_sphere]
  ring

theorem edges_inner_abs :
    |⟪firstEdge c, secondEdge c⟫_ℝ| ≤ crossBudget c / 2 := by
  have h := edges_inner c
  have h02 := c.edgeDeficit_nonneg 0 2
  have h03 := c.edgeDeficit_nonneg 0 3
  have h12 := c.edgeDeficit_nonneg 1 2
  have h13 := c.edgeDeficit_nonneg 1 3
  rw [abs_le]
  unfold crossBudget
  constructor <;> linarith

theorem separation_inner_firstEdge_abs :
    |⟪separation c, firstEdge c⟫_ℝ| ≤ crossBudget c / 4 := by
  have h := separation_inner_firstEdge c
  have h02 := c.edgeDeficit_nonneg 0 2
  have h03 := c.edgeDeficit_nonneg 0 3
  have h12 := c.edgeDeficit_nonneg 1 2
  have h13 := c.edgeDeficit_nonneg 1 3
  rw [abs_le]
  unfold crossBudget
  constructor <;> linarith

theorem separation_inner_secondEdge_abs :
    |⟪separation c, secondEdge c⟫_ℝ| ≤ crossBudget c / 4 := by
  have h := separation_inner_secondEdge c
  have h02 := c.edgeDeficit_nonneg 0 2
  have h03 := c.edgeDeficit_nonneg 0 3
  have h12 := c.edgeDeficit_nonneg 1 2
  have h13 := c.edgeDeficit_nonneg 1 3
  rw [abs_le]
  unfold crossBudget
  constructor <;> linarith

theorem firstMidpoint_inner_edge : ⟪firstMidpoint c, firstEdge c⟫_ℝ = 0 := by
  simp only [firstMidpoint, firstEdge, real_inner_smul_left, inner_add_left,
    inner_sub_right, real_inner_comm (c.point 1) (c.point 0),
    real_inner_self_eq_norm_sq, c.on_sphere]
  ring

theorem secondMidpoint_inner_edge : ⟪secondMidpoint c, secondEdge c⟫_ℝ = 0 := by
  simp only [secondMidpoint, secondEdge, real_inner_smul_left, inner_add_left,
    inner_sub_right, real_inner_comm (c.point 3) (c.point 2),
    real_inner_self_eq_norm_sq, c.on_sphere]
  ring

theorem firstMidpoint_norm_sq :
    ‖firstMidpoint c‖ ^ 2 = c.radius ^ 2 - ‖firstEdge c‖ ^ 2 / 4 := by
  simp only [firstMidpoint, firstEdge, norm_smul, mul_pow, Real.norm_eq_abs, norm_add_sq_real,
    norm_sub_sq_real, c.on_sphere, real_inner_comm (c.point 1) (c.point 0)]
  norm_num
  ring

theorem secondMidpoint_norm_sq :
    ‖secondMidpoint c‖ ^ 2 = c.radius ^ 2 - ‖secondEdge c‖ ^ 2 / 4 := by
  simp only [secondMidpoint, secondEdge, norm_smul, mul_pow, Real.norm_eq_abs, norm_add_sq_real,
    norm_sub_sq_real, c.on_sphere, real_inner_comm (c.point 3) (c.point 2)]
  norm_num
  ring

end BlaschkeLebesgue.BalancedContacts.Opposite
