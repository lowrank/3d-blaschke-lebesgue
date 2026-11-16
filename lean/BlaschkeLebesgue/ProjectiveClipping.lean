module

public import BlaschkeLebesgue.ContactFrameBounds
public import BlaschkeLebesgue.RectangleClipping
public import BlaschkeLebesgue.ProjectiveCoordinates
public import BlaschkeLebesgue.OppositePairSwap
public import BlaschkeLebesgue.ContactArcIncidence

/-!
# The common-normal rectangle lies inside both actual clipped circle arcs

The first arc is valid throughout the strip `|x| < T`, and the opposite second
arc throughout `|y| < T`. The two-ball normal-cone condition is deliberately
kept separate: it will be supplied by a positive determinant lower bound.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem projective_circleDirection (h1 : f.axis₁ = firstAxis c) (x y : ℝ) :
    circleDirection c (f.projectiveNormal x y) =
      NormedSpace.normalize (f.normal + x • f.transverse₁) := by
  change NormedSpace.normalize (tangentProjection (firstAxis c) (f.projectiveNormal x y)) = _
  rw [← h1, f.projectiveNormal_first_projection]
  exact NormedSpace.normalize_smul_of_pos
    (inv_pos.mpr (Real.sqrt_pos.2 (f.W_pos x y))) _

theorem projective_circleDirection_norm (h1 : f.axis₁ = firstAxis c) (x y : ℝ) :
    ‖circleDirection c (f.projectiveNormal x y)‖ = 1 := by
  rw [projective_circleDirection c f h1]
  apply NormedSpace.norm_normalize
  apply norm_ne_zero_iff.mp
  rw [f.normal_add_transverse₁_norm]
  positivity

/-- The angular estimates imply strict radius clipping of the first actual
circle candidate, independently of the other projective coordinate. -/
theorem projective_circleCandidate_inside_radius (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : ⟪firstMidpoint c, f.normal⟫_ℝ < 0) {x : ℝ}
    (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) (y : ℝ) :
    ‖circleCandidate c (f.projectiveNormal x y)‖ < c.radius := by
  let e := -NormedSpace.normalize (firstMidpoint c)
  let η := Completion.midpointError (edgeBudget c) (crossBudget c)
  let R := Real.sqrt (1 - η ^ 2)
  have hnormal : R ≤ ⟪f.normal, e⟫_ℝ := firstMidpoint_normal_alignment c f h1 h2 hA hside
  have htrans : |⟪f.transverse₁, e⟫_ℝ| ≤ η :=
    (normalized_midpoint_transverse_bounds c f h1 h2 hA).1
  have hprodabs : |x * ⟪f.transverse₁, e⟫_ℝ| ≤ |x| * η := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left htrans (abs_nonneg x)
  have hprod : -η * |x| ≤ x * ⟪f.transverse₁, e⟫_ℝ := by
    have h := neg_abs_le (x * ⟪f.transverse₁, e⟫_ℝ)
    nlinarith
  have hinner : ⟪circleDirection c (f.projectiveNormal x y), e⟫_ℝ =
      (⟪f.normal, e⟫_ℝ + x * ⟪f.transverse₁, e⟫_ℝ) / Real.sqrt (1 + x ^ 2) := by
    rw [projective_circleDirection c f h1, NormedSpace.normalize,
      real_inner_smul_left, inner_add_left, real_inner_smul_left, f.normal_add_transverse₁_norm]
    ring
  have hlower : (R - η * |x|) / Real.sqrt (1 + x ^ 2) ≤
      ⟪circleDirection c (f.projectiveNormal x y), e⟫_ℝ := by
    rw [hinner]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    linarith
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have hmargin := Completion.rectangle_projection_margin (edgeBudget_nonneg c)
    (crossBudget_nonneg c) hab hx
  have hclipping : clippingCos c < ⟪circleDirection c (f.projectiveNormal x y), e⟫_ℝ :=
    (clippingCos_le_arcCos c hA).trans_lt (hmargin.trans_le hlower)
  have hmem := (circlePoint_mem_radius_openBall_iff c hA
    (projective_circleDirection_norm c f h1 x y)).2 hclipping
  simpa only [Metric.mem_ball, dist_zero_right, circleCandidate] using hmem

theorem projective_opposite_circleCandidate_inside_radius (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ) {y : ℝ}
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) (x : ℝ) :
    ‖circleCandidate (swapped c) (-f.projectiveNormal x y)‖ < c.radius := by
  have h1' : f.swap.axis₁ = firstAxis (swapped c) := by rw [swapped_firstAxis]; exact h2
  have h2' : f.swap.axis₂ = secondAxis (swapped c) := by rw [swapped_secondAxis]; exact h1
  have hA' : (swapped c).totalDeficit ≤ 2 / 25 := by rw [swapped_totalDeficit]; exact hA
  have hside' : ⟪firstMidpoint (swapped c), f.swap.normal⟫_ℝ < 0 := by
    rw [swapped_firstMidpoint]
    change ⟪secondMidpoint c, -f.normal⟫_ℝ < 0
    rw [inner_neg_right]
    linarith
  have hy' : |y| < Completion.rectangleRadius (edgeBudget (swapped c)) (crossBudget (swapped c)) := by
    simpa only [swapped_edgeBudget, swapped_crossBudget] using hy
  simpa only [f.swap_projectiveNormal, swapped_radius] using
    projective_circleCandidate_inside_radius (swapped c) f.swap h1' h2' hA' hside' hy' x

/-- Full actual membership in the clipped intersection follows from the proved
arc incidence, not an additional feasibility assumption. -/
theorem projective_circleCandidate_mem_clippedOuter (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : ⟪firstMidpoint c, f.normal⟫_ℝ < 0) {x : ℝ}
    (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) (y : ℝ) :
    circleCandidate c (f.projectiveNormal x y) ∈ clippedOuter c.radius (Set.range c.point) := by
  have hR := projective_circleCandidate_inside_radius c f h1 h2 hA hside hx y
  have hv := projective_circleDirection_norm c f h1 x y
  have hperp : ⟪firstEdge c, circleDirection c (f.projectiveNormal x y)⟫_ℝ = 0 := by
    rw [← NormedSpace.norm_smul_normalize (firstEdge c), real_inner_smul_left]
    change ‖firstEdge c‖ * ⟪firstAxis c, circleDirection c (f.projectiveNormal x y)⟫_ℝ = 0
    rw [← h1, projective_circleDirection c f h1]
    simp only [NormedSpace.normalize, real_inner_smul_right, inner_add_right,
      real_inner_comm f.normal f.axis₁, f.normal_inner_axis₁,
      f.axis₁_inner_transverse₁, mul_zero, add_zero]
  exact (circlePoint_mem_clippedOuter_iff c hA hv hperp).2 hR.le

end BlaschkeLebesgue.BalancedContacts.Opposite
