module

public import BlaschkeLebesgue.ClippedRelabeling
public import BlaschkeLebesgue.AntipodalPatchIntegral

/-!
# Exactly two unit-ball constraints are active on each retained patch

The actual support point lies on the two defining unit spheres and strictly
inside the other two unit balls. The antipodal patch selects the opposite edge.
These exact contact labels will distinguish all six edge patches.
-/

public noncomputable section

open Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem projective_supportContactLabels (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hx : |x| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive : 0 < 1 - projectiveRadiusTerm c f x y) :
    c.supportContactLabels (clippedOuterBody c.radius (Set.range c.point) hne)
      (f.projectiveNormal x y) = {0, 1} := by
  have ha : edgeBudget c < 1 := by linarith [budgets_sum c, crossBudget_nonneg c]
  have hcone := projective_normalCone_of_positive c f h1 hA hpositive
  have hR := projective_circleCandidate_inside_radius c f h1 h2 hA hside hx y
  have hmem := projective_circleCandidate_mem_clippedOuter c f h1 h2 hA hside hx y
  have hsupp := normalSupport_circleCandidate c ha
    (clippedBodies_complement c.radius (Set.range c.point) hne hbound)
    (f.projectiveNormal_norm x y) hcone.le
    (fun _ hz ↦ hz.2 _ ⟨0, rfl⟩) (fun _ hz ↦ hz.2 _ ⟨1, rfl⟩) hmem
  have hframe := circleDirection_frame c ha (f.projectiveNormal_norm x y) hcone.le
  have hsphere := circlePoint_mem_unit_spheres c hframe.1 hframe.2.1
  have h0 : ‖circleCandidate c (f.projectiveNormal x y) - c.point 0‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, circleCandidate] using hsphere.1
  have h1' : ‖circleCandidate c (f.projectiveNormal x y) - c.point 1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, circleCandidate] using hsphere.2
  have h2' := circlePoint_mem_other_openBall c hA hframe.1 hframe.2.1 hR 2 (by decide) (by decide)
  have h3' := circlePoint_mem_other_openBall c hA hframe.1 hframe.2.1 hR 3 (by decide) (by decide)
  change ‖circleCandidate c (f.projectiveNormal x y) - c.point 2‖ < 1 at h2'
  change ‖circleCandidate c (f.projectiveNormal x y) - c.point 3‖ < 1 at h3'
  ext i
  simp only [supportContactLabels, mem_ofPred_eq, hsupp]
  fin_cases i <;> simp [h0, h1', ne_of_lt h2', ne_of_lt h3']

theorem projective_opposite_supportContactLabels (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {x y : ℝ} (hy : |y| < Completion.rectangleRadius (edgeBudget c) (crossBudget c))
    (hpositive : 0 < 1 - projectiveRadiusTerm (swapped c) f.swap y x) :
    c.supportContactLabels (clippedOuterBody c.radius (Set.range c.point) hne)
      (-f.projectiveNormal x y) = {2, 3} := by
  have hne' : (clippedOuter (swapped c).radius (Set.range (swapped c).point)).Nonempty := by
    rw [swapped_clippedOuter]; exact hne
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
  have h := projective_supportContactLabels (swapped c) f.swap h1' h2' hA' hside'
    (hne := hne') hbound hy' hpositive
  rw [clippedOuterBody_swapped c hne' hne, f.swap_projectiveNormal] at h
  have himage := congrArg (fun s : Set (Fin 4) ↦ pairSwap '' s) h
  rw [show swapped c = c.relabel pairSwap from rfl, c.image_supportContactLabels_relabel] at himage
  simpa [pairSwap, Equiv.swap_apply_def] using himage

theorem active_patch_supportContactLabels (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : ⟪firstMidpoint c, f.normal⟫_ℝ < 0)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {u : UnitSphere} (hu : u ∈ f.projectivePatch (activeProjectiveRegion c f)) :
    c.supportContactLabels (clippedOuterBody c.radius (Set.range c.point) hne) u = {0, 1} := by
  rw [f.projectivePatch_eq_image] at hu
  rcases hu with ⟨p, hp, rfl⟩
  exact projective_supportContactLabels c f h1 h2 hA hside hbound hp.1.1
    (lt_of_lt_of_le hp.2 (projectiveDetLower_le_first c f p.1 p.2))

theorem active_patch_opposite_supportContactLabels (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {u : UnitSphere} (hu : u ∈ f.projectivePatch (activeProjectiveRegion c f)) :
    c.supportContactLabels (clippedOuterBody c.radius (Set.range c.point) hne) (sphereAntipode u) = {2, 3} := by
  rw [f.projectivePatch_eq_image] at hu
  rcases hu with ⟨p, hp, rfl⟩
  exact projective_opposite_supportContactLabels c f h1 h2 hA hside hbound hp.1.2
    (lt_of_lt_of_le hp.2 (projectiveDetLower_le_second c f p.1 p.2))

theorem active_antipodal_supportContactLabels (h1 : f.axis₁ = firstAxis c)
    (h2 : f.axis₂ = secondAxis c) (hA : c.totalDeficit ≤ 2 / 25)
    (hside1 : ⟪firstMidpoint c, f.normal⟫_ℝ < 0) (hside2 : 0 < ⟪secondMidpoint c, f.normal⟫_ℝ)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    {u : UnitSphere} (hu : u ∈ activeAntipodalPatches c f) :
    c.supportContactLabels (clippedOuterBody c.radius (Set.range c.point) hne) u = {0, 1} ∨
      c.supportContactLabels (clippedOuterBody c.radius (Set.range c.point) hne) u = {2, 3} := by
  rcases hu with hu | ⟨v, hv, rfl⟩
  · exact Or.inl (active_patch_supportContactLabels c f h1 h2 hA hside1 hbound hu)
  · exact Or.inr (active_patch_opposite_supportContactLabels c f h1 h2 hA hside2 hbound hv)

end BlaschkeLebesgue.BalancedContacts.Opposite
