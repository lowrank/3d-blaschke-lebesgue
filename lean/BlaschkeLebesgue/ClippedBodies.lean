module

public import BlaschkeLebesgue.ComplementaryBodies
public import BlaschkeLebesgue.InnerOuter

/-!
# The actual clipped outer body and forced inner body

Bundle `RB ∩ B(Y)` and its ball transform as compact convex bodies. The support
and parallel-volume identities apply to these actual sets, including their
interior and the sandwich around the original constant-width body.
-/

public noncomputable section

open Set Metric MeasureTheory

namespace BlaschkeLebesgue

@[expose] def clippedOuterBody (R : ℝ) (Y : Set Space)
    (hne : (clippedOuter R Y).Nonempty) : ConvexBody Space where
  carrier := clippedOuter R Y
  convex' := (convex_closedBall 0 R).inter (convex_ballTransform Y)
  isCompact' := (isCompact_closedBall 0 R).inter_right (isClosed_ballTransform Y)
  nonempty' := hne

theorem clippedOuterBody_norm_le {R : ℝ} {Y : Set Space}
    {hne : (clippedOuter R Y).Nonempty} {x : Space} (hx : x ∈ clippedOuterBody R Y hne) :
    ‖x‖ ≤ R := by
  simpa only [mem_closedBall, dist_zero_right] using hx.1

theorem ballTransform_innerBall {C : Set Space} {R : ℝ} (hR : ∀ x ∈ C, ‖x‖ ≤ R) :
    closedBall (0 : Space) (1 - R) ⊆ ballTransform C := by
  intro x hx y hy
  have hx' : ‖x‖ ≤ 1 - R := by simpa only [mem_closedBall, dist_zero_right] using hx
  have h := norm_sub_le x y
  linarith only [hx', hR y hy, h]

theorem zero_mem_interior_ballTransform {C : Set Space} {R : ℝ}
    (hR : R < 1) (hbound : ∀ x ∈ C, ‖x‖ ≤ R) :
    (0 : Space) ∈ interior (ballTransform C) := by
  rw [mem_interior_iff_mem_nhds]
  apply Metric.mem_nhds_iff.2
  exact ⟨1 - R, sub_pos.2 hR,
    ball_subset_closedBall.trans (ballTransform_innerBall hbound)⟩

@[expose] def clippedInnerBody (R : ℝ) (Y : Set Space)
    (hne : (clippedOuter R Y).Nonempty) (hR : R ≤ 1) : ConvexBody Space :=
  ballTransformBody (clippedOuterBody R Y hne) ⟨0, by
    intro y hy
    simpa only [zero_sub, norm_neg] using (clippedOuterBody_norm_le hy).trans hR⟩

@[expose] def clippingCenter (Y : Set Space) : Option Y → Space
  | none => 0
  | some y => y

@[expose] def clippingRadius (Y : Set Space) (R : ℝ) : Option Y → ℝ
  | none => R
  | some _ => 1

theorem clippedOuterBody_representation (R : ℝ) (Y : Set Space)
    (hne : (clippedOuter R Y).Nonempty) :
    (clippedOuterBody R Y hne : Set Space) =
      ⋂ i : Option Y, closedBall (clippingCenter Y i) (clippingRadius Y R i) := by
  ext x
  simp only [mem_iInter]
  change (x ∈ closedBall 0 R ∧ ∀ y ∈ Y, ‖x - y‖ ≤ 1) ↔ _
  constructor
  · intro hx i
    cases i with
    | none => exact hx.1
    | some y =>
      change x ∈ closedBall (y : Space) 1
      simpa only [mem_closedBall, dist_eq_norm] using hx.2 y y.property
  · intro hx
    refine ⟨hx none, ?_⟩
    intro y hy
    simpa only [clippingCenter, clippingRadius, mem_closedBall, dist_eq_norm] using
      hx (some ⟨y, hy⟩)

/-- The clipped outer body and the reflection of its actual ball transform add to the unit ball. -/
theorem clippedBodies_complement (R : ℝ) (Y : Set Space)
    (hne : (clippedOuter R Y).Nonempty) (hR : R ≤ 1) :
    clippedOuterBody R Y hne + reflectBody (clippedInnerBody R Y hne hR) = unitBallBody := by
  apply smallBallIntersection_add_complement (clippingCenter Y) (clippingRadius Y R)
    _ (clippedOuterBody_representation R Y hne) rfl
  intro i
  cases i with
  | none => exact hR
  | some _ => exact le_rfl

theorem clippedInnerBody_zero_mem_interior (R : ℝ) (Y : Set Space)
    (hne : (clippedOuter R Y).Nonempty) (hR : R < 1) :
    (0 : Space) ∈ interior (clippedInnerBody R Y hne hR.le : Set Space) :=
  zero_mem_interior_ballTransform hR (fun _ hx => clippedOuterBody_norm_le hx)

theorem HasConstantWidth.clippedOuter_nonempty {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) {R : ℝ} {Y : Set Space}
    (hY : Y ⊆ (K : Set Space)) (hbound : ∀ x ∈ K, ‖x‖ ≤ R) :
    (clippedOuter R Y).Nonempty := K.nonempty.mono (hK.clipped_sandwich hY hbound).2

theorem HasConstantWidth.clippedBodies_sandwich {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) {R : ℝ} {Y : Set Space}
    (hY : Y ⊆ (K : Set Space)) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hne : (clippedOuter R Y).Nonempty) (hR : R ≤ 1) :
    (clippedInnerBody R Y hne hR : Set Space) ⊆ (K : Set Space) ∧
      (K : Set Space) ⊆ (clippedOuterBody R Y hne : Set Space) :=
  hK.clipped_sandwich hY hbound

theorem HasConstantWidth.clippedBodies_volume_sandwich {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) {R : ℝ} {Y : Set Space}
    (hY : Y ⊆ (K : Set Space)) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hne : (clippedOuter R Y).Nonempty) (hR : R ≤ 1) :
    bodyVolume (clippedInnerBody R Y hne hR) ≤ bodyVolume K ∧
      bodyVolume K ≤ bodyVolume (clippedOuterBody R Y hne) := by
  have h := hK.clippedBodies_sandwich hY hbound hne hR
  exact ⟨bodyVolume_mono h.1, bodyVolume_mono h.2⟩

theorem HasConstantWidth.clippedOuterBody_zero_mem_interior {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) {R : ℝ} {Y : Set Space}
    (hY : Y ⊆ (K : Set Space)) (hbound : ∀ x ∈ K, ‖x‖ ≤ R) (hR : R < 1)
    (hne : (clippedOuter R Y).Nonempty) :
    (0 : Space) ∈ interior (clippedOuterBody R Y hne : Set Space) :=
  interior_mono (hK.clipped_sandwich hY hbound).2 (hK.center_mem_interior hR hbound)

/-- Both clipped bodies have interior and satisfy the proved complementary volume identities. -/
theorem HasConstantWidth.clippedBodies_volume_coefficients {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) {R : ℝ} {Y : Set Space}
    (hY : Y ⊆ (K : Set Space)) (hbound : ∀ x ∈ K, ‖x‖ ≤ R) (hR : R < 1)
    (hne : (clippedOuter R Y).Nonempty) :
    let C := clippedOuterBody R Y hne
    let D := clippedInnerBody R Y hne hR.le
    bodyVolume D = 4 * Real.pi / 3 - parallelQuadratic C + parallelLinear C - bodyVolume C ∧
      parallelLinear D = 4 * Real.pi - 2 * parallelQuadratic C + parallelLinear C ∧
      parallelQuadratic C + parallelQuadratic D = 4 * Real.pi :=
  complementary_volume_coefficients (clippedBodies_complement R Y hne hR.le)
    (hK.clippedOuterBody_zero_mem_interior hY hbound hR hne)
    (clippedInnerBody_zero_mem_interior R Y hne hR)

end BlaschkeLebesgue
