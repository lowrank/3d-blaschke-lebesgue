module

public import BlaschkeLebesgue.OppositePartitions

/-!
# The radius and clipping angle of a contact circle

The circle is the intersection of the two unit spheres centered at the first
contact pair. All its scalar bounds follow from the actual edge deficit and
the previously proved total deficit budget, without a monotonicity assumption.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

@[expose] def circleRadius : ℝ := Real.sqrt (1 - ‖firstEdge c‖ ^ 2 / 4)
@[expose] def circlePoint (v : E) : E := firstMidpoint c + circleRadius c • v
@[expose] def clippingCos : ℝ :=
  (1 - ‖firstEdge c‖ ^ 2 / 2) / (2 * circleRadius c * ‖firstMidpoint c‖)

theorem firstEdge_norm_sq_le_one : ‖firstEdge c‖ ^ 2 ≤ 1 := by
  rw [firstEdge_norm_sq]
  linarith [c.edgeDeficit_nonneg 0 1]

theorem circleRadius_sq : circleRadius c ^ 2 = 1 - ‖firstEdge c‖ ^ 2 / 4 := by
  apply Real.sq_sqrt
  linarith [firstEdge_norm_sq_le_one c]

theorem circleRadius_pos : 0 < circleRadius c := by
  apply Real.sqrt_pos.2
  linarith [firstEdge_norm_sq_le_one c]

theorem firstMidpoint_norm_pos (hA : c.totalDeficit ≤ 2 / 25) :
    0 < ‖firstMidpoint c‖ := by
  have h := firstMidpoint_norm_sq_lower c
  nlinarith [norm_nonneg (firstMidpoint c)]

/-- The exact nondegeneracy identity for the circle clipped by the radius-R ball. -/
theorem clipping_discriminant :
    4 * circleRadius c ^ 2 * ‖firstMidpoint c‖ ^ 2 - (1 - ‖firstEdge c‖ ^ 2 / 2) ^ 2 =
      c.radius ^ 2 * (4 - ‖firstEdge c‖ ^ 2) - 1 := by
  rw [circleRadius_sq, firstMidpoint_norm_sq]
  ring

theorem clipping_discriminant_lower :
    1 / 8 - 3 * c.totalDeficit / 16 ≤
      c.radius ^ 2 * (4 - ‖firstEdge c‖ ^ 2) - 1 := by
  have hR := c.deficit_lower
  have he := firstEdge_norm_sq_le_one c
  have hp := mul_nonneg (sq_nonneg c.radius) (show 0 ≤ 1 - ‖firstEdge c‖ ^ 2 by linarith)
  nlinarith

theorem clippingCos_bounds (hA : c.totalDeficit ≤ 2 / 25) :
    0 < clippingCos c ∧ clippingCos c < 1 := by
  have hr := circleRadius_pos c
  have hm := firstMidpoint_norm_pos c hA
  have he := firstEdge_norm_sq_le_one c
  have hd := clipping_discriminant c
  have hl := clipping_discriminant_lower c
  have hden : 0 < 2 * circleRadius c * ‖firstMidpoint c‖ := by positivity
  constructor
  · exact div_pos (by linarith) hden
  · apply (div_lt_one hden).2
    nlinarith [sq_nonneg (2 * circleRadius c * ‖firstMidpoint c‖ -
      (1 - ‖firstEdge c‖ ^ 2 / 2))]

/-- A factored polynomial proves the worst-case clipping-angle bound directly;
no differentiation of the angle formula or numerical endpoint test is needed. -/
theorem clippingCos_le_arcCos (hA : c.totalDeficit ≤ 2 / 25) :
    clippingCos c ≤ Completion.arcCos (edgeBudget c) (crossBudget c) := by
  have ha := edgeBudget_nonneg c
  have hb := crossBudget_nonneg c
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have hC := Completion.arcCos_bounds ha hb hab
  have hCsq := Completion.arcCos_sq hab
  rw [show 2 - edgeBudget c - crossBudget c = 2 - c.totalDeficit by
    linarith [budgets_sum c]] at hCsq
  have hR := c.deficit_lower
  have he := firstEdge_norm_sq_le_one c
  have hAn := c.totalDeficit_nonneg
  have hx := sq_nonneg ‖firstEdge c‖
  have hfactor : 0 ≤ 2 * c.totalDeficit +
      (1 / 2 - 3 * c.totalDeficit / 4) * ‖firstEdge c‖ ^ 2 :=
    add_nonneg (by linarith) (mul_nonneg (by linarith) hx)
  have hbase := mul_nonneg (show 0 ≤ 1 - ‖firstEdge c‖ ^ 2 by linarith) hfactor
  have hinc := mul_nonneg (show 0 ≤ 4 - ‖firstEdge c‖ ^ 2 by linarith)
    (show 0 ≤ 4 * c.radius ^ 2 - 3 / 2 + c.totalDeficit / 4 by linarith)
  have hpoly : 3 * (2 - c.totalDeficit) * (1 - ‖firstEdge c‖ ^ 2 / 2) ^ 2 ≤
      16 * circleRadius c ^ 2 * ‖firstMidpoint c‖ ^ 2 := by
    rw [circleRadius_sq, firstMidpoint_norm_sq]
    nlinarith
  have hd : 0 < 2 * circleRadius c * ‖firstMidpoint c‖ :=
    mul_pos (mul_pos (by norm_num) (circleRadius_pos c)) (firstMidpoint_norm_pos c hA)
  have hsq : clippingCos c ^ 2 ≤ Completion.arcCos (edgeBudget c) (crossBudget c) ^ 2 := by
    rw [clippingCos, div_pow, hCsq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) (show 0 < 3 * (2 - c.totalDeficit) by linarith)).2
    nlinarith
  nlinarith [(clippingCos_bounds c hA).1]

end BlaschkeLebesgue.BalancedContacts.Opposite
