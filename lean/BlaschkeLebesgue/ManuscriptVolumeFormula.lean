module

public import BlaschkeLebesgue.ClippedScalarAngles

/-! # The manuscript's separable formulas for the actual clipped volumes -/

public noncomputable section

open Set

namespace BlaschkeLebesgue

namespace ClippedFormula

@[expose] def smallF (s : ℝ) : ℝ :=
  s / 2 - s ^ 3 / 24 - ClippedEdge.radius s * Real.arcsin (s / 2)
@[expose] def z (R : ℝ) : ℝ := R ^ 2 - R - R ^ 3 / 3
@[expose] def b (R : ℝ) : ℝ :=
  1 / 2 - 3 / (8 * R) - ClippingCircle.radius R * ClippedEdge.normalAngle R / 2 - z R
@[expose] def outerBase (R : ℝ) : ℝ := 8 * Real.pi / 3 - Real.pi / R
@[expose] def innerBase (R : ℝ) : ℝ :=
  8 * Real.pi / 3 - 3 * Real.pi / R -
    4 * Real.pi * ClippingCircle.radius R * ClippedEdge.normalAngle R

@[expose] def outerEdgeLength (R s : ℝ) : ℝ :=
  (-4 * ClippedEdge.unitFaceAngle R s - 2 * R ^ 3 * ClippedEdge.radiusFaceAngle R s +
    (-3 * s / 2 + s ^ 3 / 8) * ClippedEdge.arcAngle R s + ClippedEdge.radical R s / 2 +
    (4 * R ^ 3 + 3 / (2 * R)) * ClippedEdge.cutAngle R s) / 3

@[expose] def innerEdgeLength (R s : ℝ) : ℝ :=
  4 / 3 * ClippedEdge.unitFaceAngle R s - 2 * z R * ClippedEdge.radiusFaceAngle R s +
    ClippedEdge.arcAngle R s * smallF s - ClippedEdge.radical R s / 6 -
    4 * b R * ClippedEdge.cutAngle R s

@[expose] def outerEdge (R e : ℝ) : ℝ := outerEdgeLength R (Real.sqrt (1 - e))
@[expose] def innerEdge (R e : ℝ) : ℝ := innerEdgeLength R (Real.sqrt (1 - e))

@[expose] def combinedEdge (R e : ℝ) : ℝ := (47 * innerEdge R e - outerEdge R e) / 46
@[expose] def combinedBaseline (R : ℝ) : ℝ :=
  (47 * innerBase R - outerBase R) / 46 + 6 * combinedEdge R 0

@[expose] def outerOffset (R : ℝ) : ℝ :=
  (4 * Real.pi - 2 * Real.pi / R - 2 * R * ClippingCircle.radius R ^ 2 * Real.pi +
    2 * R ^ 3 * Real.pi) / 3
@[expose] def innerOffset (R : ℝ) : ℝ := 2 * Real.pi * (R ^ 2 - R) - outerOffset R

theorem volumeEdge_eq_outerEdgeLength {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    ClippedLens.volumeEdge R s = outerEdgeLength R s + outerOffset R := by
  have hR0 : 0 < R := by linarith
  have hr : ClippedEdge.radius s ^ 2 = 1 - s ^ 2 / 4 := Real.sq_sqrt (by nlinarith)
  rw [ClippedLens.volumeEdge, ClippedLens.unitArea_eq_angles hR hs hs1,
    ClippedLens.unitMoment_eq_angles hR hs hs1, ClippedLens.radiusArea_eq_angles hR hs hs1]
  unfold outerEdgeLength outerOffset ClippedLens.radiusHeight
  rw [ClippingCircle.radius_sq hR, hr]
  field_simp
  ring

theorem dualVolumeEdge_eq_innerEdgeLength {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    ClippedLens.dualVolumeEdge R s = innerEdgeLength R s + innerOffset R := by
  have hR0 : 0 < R := by linarith
  rw [ClippedLens.dualVolumeEdge, ClippedLens.meanEdge, volumeEdge_eq_outerEdgeLength hR hs hs1,
    ClippedLens.unitArea_eq_angles hR hs hs1, ClippedLens.radiusArea_eq_angles hR hs hs1]
  unfold innerEdgeLength innerOffset outerEdgeLength smallF b z ClippedEdge.unitMean
    ClippedLens.radiusHeight
  field_simp
  ring

theorem volumeBase_add_six_outerOffset {R : ℝ} (hR : 1 / 2 < R) :
    ClippedLens.volumeBase R + 6 * outerOffset R = outerBase R := by
  have hR0 : 0 < R := by linarith
  unfold ClippedLens.volumeBase ClippedLens.baseArea ClippedLens.baseMoment
    ClippedLens.radiusBaseArea outerOffset outerBase
  rw [ClippingCircle.radius_sq hR]
  field_simp
  ring

theorem dualVolumeBase_add_six_innerOffset {R : ℝ} (hR : 1 / 2 < R) :
    ClippedLens.dualVolumeBase R + 6 * innerOffset R = innerBase R := by
  have hR0 : 0 < R := by linarith
  unfold ClippedLens.dualVolumeBase ClippedLens.meanBase ClippedLens.volumeBase
    ClippedLens.baseArea ClippedLens.baseMoment ClippedLens.radiusBaseArea
    innerOffset outerOffset innerBase
  rw [ClippingCircle.radius_sq hR]
  field_simp
  ring

theorem outerEdge_deficit (R s : ℝ) (hs : 0 ≤ s) : outerEdge R (1 - s ^ 2) = outerEdgeLength R s := by
  rw [outerEdge, sub_sub_cancel, Real.sqrt_sq hs]

theorem innerEdge_deficit (R s : ℝ) (hs : 0 ≤ s) : innerEdge R (1 - s ^ 2) = innerEdgeLength R s := by
  rw [innerEdge, sub_sub_cancel, Real.sqrt_sq hs]

end ClippedFormula

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)

theorem sixEdgeSum_eq_add_constant {f g : ℝ → ℝ} {B : ℝ}
    (h : ∀ i j : Fin 4, i ≠ j → f ‖c.point j - c.point i‖ = g ‖c.point j - c.point i‖ + B) :
    c.sixEdgeSum f = c.sixEdgeSum g + 6 * B := by
  unfold sixEdgeSum
  rw [h 0 1 (by decide), h 0 2 (by decide), h 0 3 (by decide),
    h 1 2 (by decide), h 1 3 (by decide), h 2 3 (by decide)]
  ring

theorem bodyVolume_clipped_eq_manuscript (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} :
    bodyVolume (clippedOuterBody c.radius (range c.point) hne) =
      ClippedFormula.outerBase c.radius +
        c.sixEdgeSum (fun s ↦ ClippedFormula.outerEdge c.radius (1 - s ^ 2)) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  rw [c.bodyVolume_clipped_eq_six_lens_terms hA]
  have he : c.sixEdgeSum (ClippedLens.volumeEdge c.radius) =
      c.sixEdgeSum (fun s ↦ ClippedFormula.outerEdge c.radius (1 - s ^ 2)) +
        6 * ClippedFormula.outerOffset c.radius := by
    apply c.sixEdgeSum_eq_add_constant
    intro i j hij
    obtain ⟨_, _, _, hs, hs1, _⟩ := c.clipped_lens_parameter_bounds hA hij
    rw [ClippedFormula.outerEdge_deficit _ _ (norm_nonneg _)]
    exact ClippedFormula.volumeEdge_eq_outerEdgeLength hR hs hs1
  rw [he]
  linarith only [ClippedFormula.volumeBase_add_six_outerOffset hR]

theorem bodyVolume_clippedInner_eq_manuscript (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} (hR1 : c.radius ≤ 1) :
    bodyVolume (clippedInnerBody c.radius (range c.point) hne hR1) =
      ClippedFormula.innerBase c.radius +
        c.sixEdgeSum (fun s ↦ ClippedFormula.innerEdge c.radius (1 - s ^ 2)) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  rw [c.bodyVolume_clippedInner_eq_six_lens_terms hA hR1]
  have he : c.sixEdgeSum (ClippedLens.dualVolumeEdge c.radius) =
      c.sixEdgeSum (fun s ↦ ClippedFormula.innerEdge c.radius (1 - s ^ 2)) +
        6 * ClippedFormula.innerOffset c.radius := by
    apply c.sixEdgeSum_eq_add_constant
    intro i j hij
    obtain ⟨_, _, _, hs, hs1, _⟩ := c.clipped_lens_parameter_bounds hA hij
    rw [ClippedFormula.innerEdge_deficit _ _ (norm_nonneg _)]
    exact ClippedFormula.dualVolumeEdge_eq_innerEdgeLength hR hs hs1
  rw [he]
  linarith only [ClippedFormula.dualVolumeBase_add_six_innerOffset hR]

theorem clipped_volume_combination_eq_manuscript (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} (hR1 : c.radius ≤ 1) :
    (47 * bodyVolume (clippedInnerBody c.radius (range c.point) hne hR1) -
      bodyVolume (clippedOuterBody c.radius (range c.point) hne)) / 46 =
      ClippedFormula.combinedBaseline c.radius + c.sixEdgeSum (fun s ↦
        ClippedFormula.combinedEdge c.radius (1 - s ^ 2) -
          ClippedFormula.combinedEdge c.radius 0) := by
  rw [c.bodyVolume_clipped_eq_manuscript hA, c.bodyVolume_clippedInner_eq_manuscript hA hR1]
  unfold ClippedFormula.combinedBaseline sixEdgeSum ClippedFormula.combinedEdge
  ring

end BalancedContacts
end BlaschkeLebesgue
