module

public import BlaschkeLebesgue.ProjectivePairSupport
public import BlaschkeLebesgue.RadiusAllocation

/-! # The coupled radius estimates for the actual opposite-edge circles -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem circleRadius_eq_edgeRadius : circleRadius c = Completion.edgeRadius (c.edgeDeficit 0 1) := by
  rw [circleRadius, firstEdge_norm_sq, Completion.edgeRadius]
  congr 1
  ring

theorem swapped_circleRadius_eq_edgeRadius :
    circleRadius (swapped c) = Completion.edgeRadius (c.edgeDeficit 2 3) := by
  rw [circleRadius, swapped_firstEdge, secondEdge_norm_sq, Completion.edgeRadius]
  congr 1
  ring

theorem separation_norm : ‖separation c‖ = Completion.separationUpper (edgeBudget c) (crossBudget c) := by
  rw [Completion.separationUpper, ← separation_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem separation_normal_le :
    ⟪separation c, f.normal⟫_ℝ ≤ Completion.separationUpper (edgeBudget c) (crossBudget c) := by
  have h := real_inner_le_norm (separation c) f.normal
  simpa only [f.normal_norm, mul_one, separation_norm c] using h

theorem projective_allocation_lower (x y : ℝ) :
    Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y ≤
      circleRadius c * Real.sqrt (1 + x ^ 2) + circleRadius (swapped c) * Real.sqrt (1 + y ^ 2) -
        ⟪separation c, f.normal⟫_ℝ := by
  have h := Completion.radius_allocation_lower (c.edgeDeficit_nonneg 0 1) (c.edgeDeficit_nonneg 2 3) x y
  rw [← circleRadius_eq_edgeRadius c, ← swapped_circleRadius_eq_edgeRadius c] at h
  have hw := separation_normal_le c f
  change _ - Completion.separationUpper (edgeBudget c) (crossBudget c) ≤ _
  change Completion.edgeRadius 0 * Real.sqrt (1 + max (x ^ 2) (y ^ 2)) +
    Completion.edgeRadius (edgeBudget c) * Real.sqrt (1 + min (x ^ 2) (y ^ 2)) ≤ _ at h
  linarith

@[expose] def projectiveDetLower (x y : ℝ) : ℝ :=
  1 - Completion.determinantFactor (edgeBudget c) x y * Real.sqrt (f.W x y)

theorem projectiveRadiusTerm_neg (x y : ℝ) :
    projectiveRadiusTerm c f (-x) (-y) = projectiveRadiusTerm c f x y := by
  simp only [projectiveRadiusTerm, f.W_neg, neg_sq]

theorem projectiveDetLower_neg (x y : ℝ) :
    projectiveDetLower c f (-x) (-y) = projectiveDetLower c f x y := by
  simp only [projectiveDetLower, Completion.determinantFactor_neg, f.W_neg]

theorem projectiveDetLower_le_first (x y : ℝ) :
    projectiveDetLower c f x y ≤ 1 - projectiveRadiusTerm c f x y := by
  have he : c.edgeDeficit 0 1 ≤ edgeBudget c := by
    unfold edgeBudget
    linarith [c.edgeDeficit_nonneg 2 3]
  have h := mul_le_mul_of_nonneg_right
    (Completion.radius_factor_le (edgeBudget_nonneg c) he x y) (Real.sqrt_nonneg (f.W x y))
  rw [← circleRadius_eq_edgeRadius c] at h
  unfold projectiveDetLower projectiveRadiusTerm
  calc
    _ ≤ 1 - circleRadius c / Real.sqrt (1 + x ^ 2) * Real.sqrt (f.W x y) := by linarith
    _ = _ := by ring

theorem projectiveDetLower_le_second (x y : ℝ) :
    projectiveDetLower c f x y ≤ 1 - projectiveRadiusTerm (swapped c) f.swap y x := by
  have he : c.edgeDeficit 2 3 ≤ edgeBudget c := by
    unfold edgeBudget
    linarith [c.edgeDeficit_nonneg 0 1]
  have h := mul_le_mul_of_nonneg_right
    (Completion.radius_factor_le (edgeBudget_nonneg c) he y x) (Real.sqrt_nonneg (f.W x y))
  rw [← swapped_circleRadius_eq_edgeRadius c, Completion.determinantFactor_swap] at h
  unfold projectiveDetLower projectiveRadiusTerm
  rw [f.swap_W]
  calc
    _ ≤ 1 - circleRadius (swapped c) / Real.sqrt (1 + y ^ 2) * Real.sqrt (f.W x y) := by linarith
    _ = _ := by ring

theorem projectiveDetLower_lt_one_fifth (x y : ℝ) : projectiveDetLower c f x y < 1 / 5 := by
  have ha := edgeBudget_nonneg c
  have hr := Completion.edgeRadius_pos ha
  have hrs := Completion.edgeRadius_sq ha
  have hrmin : 4 / 5 < Completion.edgeRadius (edgeBudget c) := by nlinarith
  have hmin : 0 ≤ min (x ^ 2) (y ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
  have hd : 0 < Real.sqrt (1 + min (x ^ 2) (y ^ 2)) := Real.sqrt_pos.2 (by linarith)
  have hW : Real.sqrt (1 + min (x ^ 2) (y ^ 2)) ≤ Real.sqrt (f.W x y) := by
    apply Real.sqrt_le_sqrt
    linarith [min_le_left (x ^ 2) (y ^ 2), f.W_ge_one_add_first_sq x y]
  have h := mul_le_mul_of_nonneg_left hW (div_nonneg hr.le hd.le)
  have he : Completion.edgeRadius (edgeBudget c) / Real.sqrt (1 + min (x ^ 2) (y ^ 2)) *
      Real.sqrt (1 + min (x ^ 2) (y ^ 2)) = Completion.edgeRadius (edgeBudget c) := by
    field_simp
  rw [he] at h
  unfold projectiveDetLower Completion.determinantFactor
  linarith

theorem projective_q_nonneg (x y : ℝ) :
    0 ≤ Completion.q (max (projectiveDetLower c f x y) 0) := by
  apply Completion.q_nonneg (le_max_right _ _)
  exact max_le (projectiveDetLower_lt_one_fifth c f x y).le (by norm_num)

end BlaschkeLebesgue.BalancedContacts.Opposite
