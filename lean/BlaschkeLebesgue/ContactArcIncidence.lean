module

public import BlaschkeLebesgue.ContactArcCenter
public import BlaschkeLebesgue.SphericalCapPath
public import BlaschkeLebesgue.CurvatureReflection

/-!
# The clipped unit-unit arcs lie in the remaining balls

A normalized chord joins every interior arc point to its inward center while
remaining inside the enclosing ball and on both unit spheres. The contact
balance excludes a third unit-sphere intersection along this path. Since the
center is strictly inside both other balls, the intermediate value theorem
keeps the entire open arc inside them. This proof includes zero deficits and
does not use a continuation in the deficit parameters.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

theorem circlePoint_ne_other_unit_sphere {v : E} (hv : ‖v‖ = 1)
    (hperp : ⟪firstEdge c, v⟫_ℝ = 0) (hR : ‖circlePoint c v‖ < c.radius)
    (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : ‖circlePoint c v - c.point i‖ ≠ 1 := by
  have hsphere := circlePoint_mem_unit_spheres c hv hperp
  have hs0 : ‖circlePoint c v - c.point 0‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hsphere.1
  have hs1 : ‖circlePoint c v - c.point 1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hsphere.2
  intro hi
  fin_cases i
  · exact hi0 rfl
  · exact hi1 rfl
  · apply c.no_unit_constraints_in_open_ball 3 hR
    intro j hj
    fin_cases j
    · exact hs0
    · exact hs1
    · exact hi
    · exact (hj rfl).elim
  · apply c.no_unit_constraints_in_open_ball 2 hR
    intro j hj
    fin_cases j
    · exact hs0
    · exact hs1
    · exact (hj rfl).elim
    · exact hi

/-- Every point of the open clipped arc is strictly inside both remaining
unit balls, for each configuration in the full closed deficit domain. -/
theorem circlePoint_mem_other_openBall (hA : c.totalDeficit ≤ 2 / 25)
    {v : E} (hv : ‖v‖ = 1) (hperp : ⟪firstEdge c, v⟫_ℝ = 0)
    (hR : ‖circlePoint c v‖ < c.radius) (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    ‖circlePoint c v - c.point i‖ < 1 := by
  let e := arcCenterDirection c
  have he : ‖e‖ = 1 := arcCenterDirection_norm c hA
  have hh := clippingCos_bounds c hA
  have hvh : clippingCos c < ⟪v, e⟫_ℝ :=
    (circlePoint_mem_radius_openBall_iff c hA hv).1
      (by simpa only [Metric.mem_ball, dist_zero_right] using hR)
  have hc := capPath_continuousOn he hh.1.le hh.2 hvh
  have hcirc : ContinuousOn (fun t ↦ circlePoint c (capPath e v t)) (Set.Icc 0 1) :=
    continuousOn_const.add (hc.const_smul (circleRadius c))
  have hf : ContinuousOn (fun t ↦ ‖circlePoint c (capPath e v t) - c.point i‖) (Set.Icc 0 1) :=
    (hcirc.sub continuousOn_const).norm
  by_contra! hbad
  have hstart : ‖circlePoint c (capPath e v 0) - c.point i‖ < 1 := by
    rw [capPath_zero he]
    exact arcCenter_mem_other_ball c hA i hi0 hi1
  have hend : 1 ≤ ‖circlePoint c (capPath e v 1) - c.point i‖ := by
    rw [capPath_one hv]
    exact hbad
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf ⟨hstart.le, hend⟩
  have htnorm : ‖capPath e v t‖ = 1 := capPath_norm he hh.1.le hh.2 hvh ht
  have htperp : ⟪firstEdge c, capPath e v t⟫_ℝ = 0 :=
    capPath_inner_zero (arcCenterDirection_inner_edge c) hperp t
  have htR : ‖circlePoint c (capPath e v t)‖ < c.radius := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (circlePoint_mem_radius_openBall_iff c hA htnorm).2
        (capPath_inner_gt he hv hh.1.le hh.2 hvh ht)
  exact circlePoint_ne_other_unit_sphere c htnorm htperp htR i hi0 hi1 heq

/-- The endpoints also lie in the remaining closed balls. This follows by
continuity along the same arc, without perturbing the contact configuration. -/
theorem circlePoint_mem_other_closedBall (hA : c.totalDeficit ≤ 2 / 25)
    {v : E} (hv : ‖v‖ = 1) (hperp : ⟪firstEdge c, v⟫_ℝ = 0)
    (hR : ‖circlePoint c v‖ ≤ c.radius) (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    ‖circlePoint c v - c.point i‖ ≤ 1 := by
  let e := arcCenterDirection c
  have he : ‖e‖ = 1 := arcCenterDirection_norm c hA
  have hh := clippingCos_bounds c hA
  have hvh : clippingCos c ≤ ⟪v, e⟫_ℝ :=
    (circlePoint_mem_radius_ball_iff c hA hv).1
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hR)
  have hhalf0 : 0 ≤ clippingCos c / 2 := by linarith
  have hhalf1 : clippingCos c / 2 < 1 := by linarith
  have hvhalf : clippingCos c / 2 < ⟪v, e⟫_ℝ := by linarith
  have hc := capPath_continuousOn he hhalf0 hhalf1 hvhalf
  have hcirc : ContinuousOn (fun t ↦ circlePoint c (capPath e v t)) (Set.Icc 0 1) :=
    continuousOn_const.add (hc.const_smul (circleRadius c))
  have hf : ContinuousOn (fun t ↦ ‖circlePoint c (capPath e v t) - c.point i‖) (Set.Icc 0 1) :=
    (hcirc.sub continuousOn_const).norm
  have hle : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖circlePoint c (capPath e v t) - c.point i‖ ≤ 1 := by
    intro t ht
    have htnorm := capPath_norm he hhalf0 hhalf1 hvhalf ⟨ht.1, ht.2.le⟩
    have htperp := capPath_inner_zero (arcCenterDirection_inner_edge c) hperp t
    have htR : ‖circlePoint c (capPath e v t)‖ < c.radius := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        (circlePoint_mem_radius_openBall_iff c hA htnorm).2
          (capPath_inner_gt_before_endpoint he hv hh.1.le hh.2 hvh ht)
    exact (circlePoint_mem_other_openBall c hA htnorm htperp htR i hi0 hi1).le
  have hclosure : closure (Set.Ico (0 : ℝ) 1) = Set.Icc 0 1 := closure_Ico (by norm_num)
  have hend := le_on_closure hle (by rw [hclosure]; exact hf) continuousOn_const
    (show (1 : ℝ) ∈ closure (Set.Ico (0 : ℝ) 1) by rw [hclosure]; norm_num)
  simpa only [capPath_one hv] using hend

/-- The whole closed radius-clipped circle is an actual boundary arc of the
four-ball clipped intersection. There are no additional cuts by the other balls. -/
theorem circlePoint_mem_clippedOuter_iff (hA : c.totalDeficit ≤ 2 / 25)
    {v : E} (hv : ‖v‖ = 1) (hperp : ⟪firstEdge c, v⟫_ℝ = 0) :
    circlePoint c v ∈ clippedOuter c.radius (Set.range c.point) ↔
      ‖circlePoint c v‖ ≤ c.radius := by
  constructor
  · intro hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
  · intro hR
    refine ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hR, ?_⟩
    have hsphere := circlePoint_mem_unit_spheres c hv hperp
    rintro y ⟨i, rfl⟩
    fin_cases i
    · exact le_of_eq (by simpa [Metric.mem_sphere, dist_eq_norm] using hsphere.1)
    · exact le_of_eq (by simpa [Metric.mem_sphere, dist_eq_norm] using hsphere.2)
    · exact circlePoint_mem_other_closedBall c hA hv hperp hR 2 (by decide) (by decide)
    · exact circlePoint_mem_other_closedBall c hA hv hperp hR 3 (by decide) (by decide)

theorem unit_spheres_mem_clippedOuter (hA : c.totalDeficit ≤ 2 / 25) {x : E}
    (h0 : x ∈ Metric.sphere (c.point 0) 1) (h1 : x ∈ Metric.sphere (c.point 1) 1)
    (hR : ‖x‖ ≤ c.radius) : x ∈ clippedOuter c.radius (Set.range c.point) := by
  obtain ⟨v, hv, hperp, rfl⟩ := unit_spheres_circle_parametrization c h0 h1
  exact (circlePoint_mem_clippedOuter_iff c hA hv hperp).2 hR

variable (c : BalancedContacts 4 Space)

/-- The other-ball constraints in the local curvature theorem now follow
from the clipping condition and the contact geometry. -/
theorem clipped_circle_curvature_of_inside_radius (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (n : UnitSphere)
    (hcone : |⟪firstAxis c, (n : Space)⟫_ℝ| < ‖firstEdge c‖ / 2)
    (hR : ‖circleCandidate c n‖ < c.radius) :
    curvatureTrace (clippedOuterBody c.radius (Set.range c.point) hne) n =
      circleRadius c / Real.sqrt (1 - ⟪firstAxis c, (n : Space)⟫_ℝ ^ 2) ∧
    curvatureDet (clippedOuterBody c.radius (Set.range c.point) hne) n = 0 := by
  have ha : edgeBudget c < 1 := by
    have h := crossBudget_nonneg c
    have hs := budgets_sum c
    linarith
  have hf := circleDirection_frame c ha n.norm_eq_one hcone.le
  apply clipped_circle_curvature c ha n hcone hR
  · exact circlePoint_mem_other_openBall c hA hf.1 hf.2.1 hR 2 (by decide) (by decide)
  · exact circlePoint_mem_other_openBall c hA hf.1 hf.2.1 hR 3 (by decide) (by decide)

theorem clipped_circle_complement_det_of_inside_radius (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    (n : UnitSphere) (hcone : |⟪firstAxis c, (n : Space)⟫_ℝ| < ‖firstEdge c‖ / 2)
    (hR : ‖circleCandidate c n‖ < c.radius) :
    curvatureDet (clippedInnerBody c.radius (Set.range c.point) hne hbound) (sphereAntipode n) =
      1 - circleRadius c / Real.sqrt (1 - ⟪firstAxis c, (n : Space)⟫_ℝ ^ 2) := by
  have ha : edgeBudget c < 1 := by
    have h := crossBudget_nonneg c
    have hs := budgets_sum c
    linarith
  have hf := circleDirection_frame c ha n.norm_eq_one hcone.le
  apply clipped_circle_complement_det c ha hbound n hcone hR
  · exact circlePoint_mem_other_openBall c hA hf.1 hf.2.1 hR 2 (by decide) (by decide)
  · exact circlePoint_mem_other_openBall c hA hf.1 hf.2.1 hR 3 (by decide) (by decide)

end BlaschkeLebesgue.BalancedContacts.Opposite
