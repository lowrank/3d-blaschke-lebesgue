module

public import BlaschkeLebesgue.ProjectiveFourSigns

/-!
# Restricting the completion contribution to the valid circle regions

Positive common curvature proves both strict circle normal-cone conditions.
The contribution outside that region is discarded before adding edge pairs.
The paired and four-sign lower bounds survive this restriction because the
scalar minorant vanishes whenever the common curvature is nonpositive.
-/

public noncomputable section

open Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

@[expose] def projectiveRectangle : Set (ℝ × ℝ) :=
  {q | |q.1| < Completion.rectangleRadius (edgeBudget c) (crossBudget c) ∧
    |q.2| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)}

@[expose] def positiveProjectiveCurvature : Set (ℝ × ℝ) :=
  {q | 0 < projectiveDetLower c f q.1 q.2}

@[expose] def activeProjectiveRegion : Set (ℝ × ℝ) :=
  projectiveRectangle c ∩ positiveProjectiveCurvature c f

@[expose] def activeProjectiveIntegrand (D : ConvexBody Space) (x y : ℝ) : ℝ :=
  (positiveProjectiveCurvature c f).indicator
    (fun q : ℝ × ℝ ↦ projectiveCompletionIntegrand D f q.1 q.2) (x, y)

theorem continuous_projectiveDetLower :
    Continuous (fun q : ℝ × ℝ ↦ projectiveDetLower c f q.1 q.2) := by
  unfold projectiveDetLower Completion.determinantFactor ObliqueFrame.W
  apply Continuous.sub continuous_const
  apply Continuous.mul
  · apply Continuous.div continuous_const
    · fun_prop
    · intro q
      apply ne_of_gt (Real.sqrt_pos.2 _)
      have h := le_min (sq_nonneg q.1) (sq_nonneg q.2)
      linarith
  · fun_prop

theorem measurableSet_projectiveRectangle : MeasurableSet (projectiveRectangle c) := by
  exact ((isOpen_lt (continuous_fst.abs) continuous_const).inter
    (isOpen_lt (continuous_snd.abs) continuous_const)).measurableSet

theorem measurableSet_positiveProjectiveCurvature :
    MeasurableSet (positiveProjectiveCurvature c f) :=
  (isOpen_lt continuous_const (continuous_projectiveDetLower c f)).measurableSet

theorem measurableSet_activeProjectiveRegion : MeasurableSet (activeProjectiveRegion c f) :=
  (measurableSet_projectiveRectangle c).inter (measurableSet_positiveProjectiveCurvature c f)

theorem active_projective_pair_density_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space))
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    2 * Completion.phi (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
        (Completion.determinantFactor (edgeBudget c) x y) (f.W x y) / f.sine ≤
      activeProjectiveIntegrand c f D x y + activeProjectiveIntegrand c f D (-x) (-y) := by
  dsimp only
  by_cases hp : 0 < projectiveDetLower c f x y
  · simpa only [activeProjectiveIntegrand, positiveProjectiveCurvature, Set.mem_ofPred_eq,
      projectiveDetLower_neg, hp, Set.indicator_of_mem, Prod.fst, Prod.snd] using
      projective_completion_pair_density_lower c f h1 h2 hA hside1 hside2 hbound hK hDK hx hy
  · have hz : max (projectiveDetLower c f x y) 0 = 0 := max_eq_right (le_of_not_gt hp)
    have hphi : Completion.phi (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
        (Completion.determinantFactor (edgeBudget c) x y) (f.W x y) = 0 := by
      unfold Completion.phi
      change max _ 0 * Completion.q (max (projectiveDetLower c f x y) 0) / _ = 0
      rw [hz, Completion.q]
      ring
    simp [activeProjectiveIntegrand, positiveProjectiveCurvature, projectiveDetLower_neg, hp, hphi]

theorem active_projective_four_sign_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hDK : (clippedInnerBody c.radius (Set.range c.point) hne hbound : Set Space) ⊆ (K : Set Space))
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c)) :
    let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
    4 * Completion.phi (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
        (Completion.determinantFactor (edgeBudget c) x y) (Completion.uniformW (edgeBudget c) (crossBudget c) x y) ≤
      activeProjectiveIntegrand c f D x y + activeProjectiveIntegrand c f D (-x) (-y) +
        activeProjectiveIntegrand c f D x (-y) + activeProjectiveIntegrand c f D (-x) y := by
  have hp := active_projective_pair_density_lower c f h1 h2 hA hside1 hside2 hbound hK hDK hx hy
  have hy' : |-y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c) := by simpa using hy
  have hn := active_projective_pair_density_lower c f h1 h2 hA hside1 hside2 hbound hK hDK hx hy'
  dsimp only at hp hn ⊢
  rw [neg_neg, Completion.allocationNumerator_neg_right, Completion.determinantFactor_neg_right] at hn
  have hj := div_le_div_of_nonneg_right (projective_phi_sign_average_lower c f h1 h2 hA x y) f.sine_pos.le
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have ho := Completion.obliquity_bounds (edgeBudget_nonneg c) (crossBudget_nonneg c) hab
  have hgeo : 1 + max (x ^ 2) (y ^ 2) ≤ Completion.uniformW (edgeBudget c) (crossBudget c) x y := by
    apply Completion.averagedW_ge
    rw [abs_of_nonneg ho.1]
    linarith [ho.2]
  have hnonneg := Completion.phi_nonneg
    (N := Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
    (Completion.determinantFactor_sqrt_lower (edgeBudget_nonneg c) x y hgeo)
  have hs1 : f.sine ≤ 1 := by nlinarith [f.sine_sq, sq_nonneg f.chi, f.sine_pos]
  have hunit := (le_div_iff₀ f.sine_pos).2 (mul_le_of_le_one_right hnonneg hs1)
  simp only [add_div, mul_div_assoc] at hp hn hj
  linarith only [hp, hn, hj, hunit]

end BlaschkeLebesgue.BalancedContacts.Opposite
