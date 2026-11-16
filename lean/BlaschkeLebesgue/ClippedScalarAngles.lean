module

public import BlaschkeLebesgue.ClippedDualVolume

/-! # Identifying the scalar lens expressions with the manuscript's edge angles -/

public noncomputable section

namespace BlaschkeLebesgue

namespace ClippedEdge

@[expose] def unitFaceAngle (R s : ℝ) : ℝ :=
  Real.arccos (s / (4 * R * radius s * ClippingCircle.radius R))
@[expose] def radiusFaceAngle (R s : ℝ) : ℝ :=
  Real.arccos (1 - s ^ 2 / (2 * ClippingCircle.radius R ^ 2))
@[expose] def radical (R s : ℝ) : ℝ := s * Real.sqrt (R ^ 2 * (4 - s ^ 2) - 1)

theorem radii_pos {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    0 < ClippingCircle.radius R ∧ 0 < radius s ∧ 0 < midpointNorm R s := by
  refine ⟨ClippingCircle.radius_pos hR, Real.sqrt_pos.2 ?_, Real.sqrt_pos.2 ?_⟩ <;> nlinarith

end ClippedEdge

namespace ClippedLens

theorem sqrt_unitHeight (R : ℝ) :
    Real.sqrt (1 - unitHeight R ^ 2) = ClippingCircle.radius R := by
  unfold unitHeight ClippingCircle.radius
  congr 1
  ring

theorem sqrt_neighborHeight (s : ℝ) :
    Real.sqrt (1 - neighborHeight s ^ 2) = ClippedEdge.radius s := by
  unfold neighborHeight ClippedEdge.radius
  congr 1
  ring

theorem sqrt_unitAxisInner {R : ℝ} (hR : 0 < R) (s : ℝ) :
    Real.sqrt (1 - unitAxisInner R s ^ 2) = ClippedEdge.midpointNorm R s / R := by
  have he : 1 - unitAxisInner R s ^ 2 = (R ^ 2 - s ^ 2 / 4) / R ^ 2 := by
    unfold unitAxisInner
    field_simp
    ring
  rw [he, Real.sqrt_div' _ (sq_nonneg R), Real.sqrt_sq hR.le]
  rfl

theorem sqrt_radiusHeight {R : ℝ} (hR : 0 < R) :
    Real.sqrt (1 - radiusHeight R ^ 2) = ClippingCircle.radius R / R := by
  have he : 1 - radiusHeight R ^ 2 = (1 - 1 / (4 * R ^ 2)) / R ^ 2 := by
    unfold radiusHeight
    field_simp
    ring
  rw [he, Real.sqrt_div' _ (sq_nonneg R), Real.sqrt_sq hR.le]
  rfl

theorem sqrt_radiusAxisInner {R s : ℝ} (hR : 0 < R) (hs : 0 ≤ s) :
    Real.sqrt (1 - radiusAxisInner R s ^ 2) = s * ClippedEdge.midpointNorm R s / R ^ 2 := by
  have he : 1 - radiusAxisInner R s ^ 2 = s ^ 2 * (R ^ 2 - s ^ 2 / 4) / (R ^ 2) ^ 2 := by
    unfold radiusAxisInner
    field_simp
    ring
  rw [he, Real.sqrt_div' _ (sq_nonneg (R ^ 2)), Real.sqrt_mul (sq_nonneg s),
    Real.sqrt_sq hs, Real.sqrt_sq (sq_nonneg R)]
  rfl

theorem sqrt_unit_gram {R : ℝ} (hR : 0 < R) (s : ℝ) :
    Real.sqrt (lensGram (unitHeight R) (neighborHeight s) (unitAxisInner R s)) =
      Real.sqrt (R ^ 2 * (4 - s ^ 2) - 1) / (2 * R) := by
  rw [unit_gram R s hR.ne', show 4 * R ^ 2 = (2 * R) ^ 2 by ring,
    Real.sqrt_div' _ (sq_nonneg (2 * R)), Real.sqrt_sq (by positivity : 0 ≤ 2 * R)]

theorem unit_outer_angle {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.arccos (latitudeCapThreshold (neighborHeight s) (unitAxisInner R s) (unitHeight R)) =
      Real.pi - ClippedEdge.cutAngle R s := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hκ, _, hm⟩ := ClippedEdge.radii_pos hR hs hs1
  have he : latitudeCapThreshold (neighborHeight s) (unitAxisInner R s) (unitHeight R) =
      -((1 - 2 * R ^ 2) * s / (4 * R * ClippingCircle.radius R * ClippedEdge.midpointNorm R s)) := by
    rw [latitudeCapThreshold, sqrt_unitAxisInner hR0 s, sqrt_unitHeight]
    unfold neighborHeight unitAxisInner unitHeight
    field_simp
    ring
  rw [he, Real.arccos_neg]
  rfl

theorem unit_neighbor_angle {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.arccos (latitudeCapThreshold (unitHeight R) (unitAxisInner R s) (neighborHeight s)) =
      ClippedEdge.arcAngle R s / 2 := by
  have hR0 : 0 < R := by linarith
  obtain ⟨_, hr, hm⟩ := ClippedEdge.radii_pos hR hs hs1
  have he : latitudeCapThreshold (unitHeight R) (unitAxisInner R s) (neighborHeight s) =
      (1 - s ^ 2 / 2) / (2 * ClippedEdge.radius s * ClippedEdge.midpointNorm R s) := by
    rw [latitudeCapThreshold, sqrt_unitAxisInner hR0 s, sqrt_neighborHeight]
    unfold unitHeight unitAxisInner neighborHeight
    field_simp
  rw [he, ClippedEdge.arcAngle]
  ring

theorem unit_vertex_angle {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.arccos (latitudeCapThreshold (unitAxisInner R s) (neighborHeight s) (unitHeight R)) =
      ClippedEdge.unitFaceAngle R s := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hκ, hr, _⟩ := ClippedEdge.radii_pos hR hs hs1
  unfold ClippedEdge.unitFaceAngle
  congr 1
  rw [latitudeCapThreshold, sqrt_neighborHeight, sqrt_unitHeight]
  unfold unitAxisInner neighborHeight unitHeight
  field_simp
  ring

theorem radius_outer_angle {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.arccos (latitudeCapThreshold (radiusHeight R) (radiusAxisInner R s) (radiusHeight R)) =
      ClippedEdge.cutAngle R s := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hκ, _, hm⟩ := ClippedEdge.radii_pos hR hs hs1
  unfold ClippedEdge.cutAngle
  congr 1
  rw [latitudeCapThreshold, sqrt_radiusAxisInner hR0 hs.le, sqrt_radiusHeight hR0]
  unfold radiusHeight radiusAxisInner
  field_simp
  ring

theorem radius_vertex_angle {R s : ℝ} (hR : 1 / 2 < R) (_hs : 0 < s) (_hs1 : s ≤ 1) :
    Real.arccos (latitudeCapThreshold (radiusAxisInner R s) (radiusHeight R) (radiusHeight R)) =
      ClippedEdge.radiusFaceAngle R s := by
  have hR0 : 0 < R := by linarith
  have hκ := ClippingCircle.radius_pos hR
  have hκsq := ClippingCircle.radius_sq hR
  unfold ClippedEdge.radiusFaceAngle
  congr 1
  rw [latitudeCapThreshold, sqrt_radiusHeight hR0]
  unfold radiusAxisInner radiusHeight
  field_simp
  rw [hκsq]
  field_simp
  ring

theorem unitArea_eq_angles {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    unitArea R s = 2 * Real.pi - 2 * ClippedEdge.unitFaceAngle R s - Real.pi / R +
      ClippedEdge.cutAngle R s / R - s * ClippedEdge.arcAngle R s / 2 := by
  rw [unitArea, lensAreaExpression, unit_vertex_angle hR hs hs1,
    unit_outer_angle hR hs hs1, unit_neighbor_angle hR hs hs1]
  unfold unitHeight neighborHeight
  ring

theorem unitMoment_eq_angles {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    unitMoment R s = -R * ClippingCircle.radius R ^ 2 * Real.pi +
      R * ClippingCircle.radius R ^ 2 * ClippedEdge.cutAngle R s -
      s * ClippedEdge.radius s ^ 2 * ClippedEdge.arcAngle R s / 4 + ClippedEdge.radical R s / 4 := by
  have hR0 : 0 < R := by linarith
  have hr : ClippedEdge.radius s ^ 2 = 1 - s ^ 2 / 4 := Real.sq_sqrt (by nlinarith)
  rw [unitMoment, lensMomentExpression, unit_outer_angle hR hs hs1,
    unit_neighbor_angle hR hs hs1, sqrt_unit_gram hR0 s, ClippingCircle.radius_sq hR, hr]
  unfold unitHeight neighborHeight unitAxisInner ClippedEdge.radical
  field_simp
  ring

theorem radiusArea_eq_angles {R s : ℝ} (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    radiusArea R s = 2 * Real.pi - 2 * ClippedEdge.radiusFaceAngle R s -
      4 * radiusHeight R * ClippedEdge.cutAngle R s := by
  rw [radiusArea, lensAreaExpression, radius_vertex_angle hR hs hs1, radius_outer_angle hR hs hs1]
  ring

end ClippedLens
end BlaschkeLebesgue
