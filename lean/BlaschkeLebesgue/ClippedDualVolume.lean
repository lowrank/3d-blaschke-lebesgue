module

public import BlaschkeLebesgue.ClippedMeanCurvature

/-! # An explicit six-edge formula for the actual forced inner body's volume -/

public noncomputable section

open Set

namespace BlaschkeLebesgue

namespace ClippedLens

@[expose] def dualVolumeBase (R : ℝ) : ℝ :=
  4 * Real.pi / 3 - meanBase R + R ^ 2 * radiusBaseArea R - 8 * baseArea R - volumeBase R

@[expose] def dualVolumeEdge (R s : ℝ) : ℝ :=
  -meanEdge R s + R ^ 2 * radiusArea R s + 2 * unitArea R s - volumeEdge R s

end ClippedLens

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)

theorem bodyVolume_clippedInner_eq_six_lens_terms (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} (hR1 : c.radius ≤ 1) :
    bodyVolume (clippedInnerBody c.radius (range c.point) hne hR1) =
      ClippedLens.dualVolumeBase c.radius + c.sixEdgeSum (ClippedLens.dualVolumeEdge c.radius) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  have hR0 : 0 < c.radius := by linarith
  have hRlt : c.radius < 1 := by nlinarith [c.radius_sq_le (by decide)]
  have h := (complementary_volume_coefficients
    (clippedBodies_complement c.radius (range c.point) hne hR1)
    (c.clippedOuter_zero_mem_interior hR0)
    (clippedInnerBody_zero_mem_interior c.radius (range c.point) hne hRlt)).1
  rw [c.parallelQuadratic_clipped_eq_six_lens_terms hA,
    c.parallelLinear_clipped_eq_lens_terms hA, c.bodyVolume_clipped_eq_six_lens_terms hA] at h
  rw [h]
  simp only [ClippedLens.dualVolumeBase, ClippedLens.dualVolumeEdge, sixEdgeSum]
  ring

end BalancedContacts
end BlaschkeLebesgue
