module

public import BlaschkeLebesgue.ClippedCurvatureDecomposition
public import BlaschkeLebesgue.ClippedVolumeLenses

/-! # The actual mean-curvature coefficient as six explicit scalar terms -/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue

namespace ClippedEdge

@[expose] def radius (s : ℝ) : ℝ := Real.sqrt (1 - s ^ 2 / 4)
@[expose] def midpointNorm (R s : ℝ) : ℝ := Real.sqrt (R ^ 2 - s ^ 2 / 4)
@[expose] def arcAngle (R s : ℝ) : ℝ :=
  2 * Real.arccos ((1 - s ^ 2 / 2) / (2 * radius s * midpointNorm R s))
@[expose] def cutAngle (R s : ℝ) : ℝ :=
  Real.arccos ((1 - 2 * R ^ 2) * s / (4 * R * ClippingCircle.radius R * midpointNorm R s))
@[expose] def normalAngle (R : ℝ) : ℝ := Real.arccos (1 / (2 * R))
@[expose] def unitMean (R s : ℝ) : ℝ := radius s * arcAngle R s * Real.arcsin (s / 2)

end ClippedEdge

namespace ClippedLens

@[expose] def meanBase (R : ℝ) : ℝ :=
  -8 * baseArea R + R * radiusBaseArea R + 4 * Real.pi * ClippingCircle.radius R * ClippedEdge.normalAngle R

@[expose] def meanEdge (R s : ℝ) : ℝ :=
  2 * unitArea R s + R * radiusArea R s + ClippedEdge.unitMean R s -
    2 * ClippingCircle.radius R * ClippedEdge.normalAngle R * ClippedEdge.cutAngle R s

end ClippedLens

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)
  {hne : (clippedOuter c.radius (range c.point)).Nonempty}

theorem integral_curvatureTrace_unitFaceNormals (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    (∫ u in c.unitFaceNormals i,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      2 * sphereMeasure.real (c.unitFaceNormals i) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  have he : (∫ u in c.unitFaceNormals i,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      ∫ _ in c.unitFaceNormals i, (2 : ℝ) ∂sphereMeasure := by
    apply integral_congr_ae
    apply (ae_restrict_iff' (c.measurableSet_unitFaceNormals i)).2
    filter_upwards [c.clipped_unitFace_curvature_ae (hne := hne) hA
      (by linarith : 0 < c.radius) i] with u hu huS
    exact (hu huS).1
  rw [he, setIntegral_const, smul_eq_mul, mul_comm]

theorem integral_curvatureTrace_radiusFaceNormals (hR : 0 < c.radius) :
    (∫ u in c.radiusFaceNormals,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      2 * c.radius * sphereMeasure.real c.radiusFaceNormals := by
  have he : (∫ u in c.radiusFaceNormals,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      ∫ _ in c.radiusFaceNormals, 2 * c.radius ∂sphereMeasure := by
    apply integral_congr_ae
    apply (ae_restrict_iff' (c.measurableSet_radiusFaceNormals hR)).2
    filter_upwards [c.clipped_radiusFace_curvature_ae (hne := hne) hR] with u hu huS
    exact (hu huS).1
  rw [he, setIntegral_const, smul_eq_mul, mul_comm]

theorem firstMidpoint_norm_eq_scalar :
    ‖Opposite.firstMidpoint c‖ = ClippedEdge.midpointNorm c.radius ‖Opposite.firstEdge c‖ := by
  rw [ClippedEdge.midpointNorm, ← Opposite.firstMidpoint_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem integral_curvatureTrace_unitEdgeNormals (hA : c.totalDeficit ≤ 2 / 25) (k : Fin 6) :
    (∫ u in c.unitEdgeNormals k,
      curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u ∂sphereMeasure) =
      2 * ClippedEdge.unitMean c.radius
        ‖c.point (contactEdgePermutation k 1) - c.point (contactEdgePermutation k 0)‖ := by
  let e := contactEdgePermutation k
  have hne' : (clippedOuter (c.relabel e).radius (range (c.relabel e).point)).Nonempty := by
    simpa only [c.clippedOuter_relabel e] using hne
  have h := Opposite.integral_unitCircleNormals_curvatureTrace (c.relabel e)
    (by simpa only [c.totalDeficit_relabel] using hA) (hne := hne')
  rw [c.clippedOuterBody_relabel e hne' hne, Opposite.clippingCos,
    (c.relabel e).firstMidpoint_norm_eq_scalar] at h
  change (∫ u in c.unitEdgeNormals k, curvatureTrace _ u ∂sphereMeasure) = _ at h
  rw [h]
  simp only [ClippedEdge.unitMean, ClippedEdge.arcAngle, ClippedEdge.radius,
    Opposite.circleRadius, Opposite.firstEdge, relabel, e]
  ring

theorem sum_contactEdgePermutation (f : ℝ → ℝ) :
    (∑ k : Fin 6, f ‖c.point (contactEdgePermutation k 1) - c.point (contactEdgePermutation k 0)‖) =
      c.sixEdgeSum f := by
  simp [Fin.sum_univ_succ, contactEdgePermutation, Equiv.swap_apply_def, sixEdgeSum]
  ring

theorem pairMidpoint_norm_eq_scalar (i j : Fin 4) :
    ‖(1 / 2 : ℝ) • (c.point i + c.point j)‖ =
      ClippedEdge.midpointNorm c.radius ‖c.point j - c.point i‖ := by
  have hs : ‖(1 / 2 : ℝ) • (c.point i + c.point j)‖ ^ 2 =
      c.radius ^ 2 - ‖c.point j - c.point i‖ ^ 2 / 4 := by
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, norm_add_sq_real,
      norm_sub_sq_real, c.on_sphere, real_inner_comm (c.point j) (c.point i)]
    norm_num
    ring
  rw [ClippedEdge.midpointNorm, ← hs, Real.sqrt_sq (norm_nonneg _)]

theorem clippingPairAngle_eq_scalar {i j : Fin 4} (hij : i ≠ j) :
    c.clippingPairAngle i j = ClippedEdge.cutAngle c.radius ‖c.point j - c.point i‖ := by
  rw [clippingPairAngle, ite_eq_right hij, clippingPairCos, c.pairMidpoint_norm_eq_scalar]
  rfl

theorem sum_clippingPairAngles :
    (∑ i : Fin 4, ∑ j : Fin 4, c.clippingPairAngle i j) =
      2 * c.sixEdgeSum (ClippedEdge.cutAngle c.radius) := by
  have he (i : Fin 4) : (∑ j : Fin 4, c.clippingPairAngle i j) =
      ∑ j ∈ Finset.univ.erase i, ClippedEdge.cutAngle c.radius ‖c.point j - c.point i‖ := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have hd : c.clippingPairAngle i i = 0 := by simp [clippingPairAngle]
    rw [hd, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    exact c.clippingPairAngle_eq_scalar (Ne.symm (Finset.mem_erase.1 hj).1)
  simp_rw [he]
  exact c.sum_pair_lengths (ClippedEdge.cutAngle c.radius)

theorem parallelQuadratic_clipped_eq_face_edge_terms (hA : c.totalDeficit ≤ 2 / 25) :
    parallelQuadratic (clippedOuterBody c.radius (range c.point) hne) =
      (∑ i, sphereMeasure.real (c.unitFaceNormals i)) +
      c.radius * sphereMeasure.real c.radiusFaceNormals +
      c.sixEdgeSum (ClippedEdge.unitMean c.radius) +
      ClippingCircle.radius c.radius * ClippedEdge.normalAngle c.radius *
        (4 * Real.pi - 2 * c.sixEdgeSum (ClippedEdge.cutAngle c.radius)) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  have hR0 : 0 < c.radius := by linarith
  have hR1 : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  have h := c.integral_curvatureTrace_clipped_eq_patch_sum (hne := hne) hA
  rw [integral_curvatureTrace (clippedBodies_complement c.radius (range c.point) hne hR1)
    (c.clippedOuter_zero_mem_interior hR0)] at h
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_option] at h
  simp only [patchNormalRegion] at h
  rw [c.integral_curvatureTrace_radiusFaceNormals hR0] at h
  simp_rw [c.integral_curvatureTrace_unitFaceNormals hA,
    c.integral_curvatureTrace_unitEdgeNormals hA,
    c.integral_radiusCircleNormals_curvatureTrace hA] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum, c.sum_contactEdgePermutation] at h
  have hs : (∑ i : Fin 4, ClippingCircle.radius c.radius *
      (2 * Real.pi - 2 * ∑ j, c.clippingPairAngle i j) * Real.arccos (1 / (2 * c.radius))) =
      2 * ClippingCircle.radius c.radius * ClippedEdge.normalAngle c.radius *
        (4 * Real.pi - 2 * c.sixEdgeSum (ClippedEdge.cutAngle c.radius)) := by
    simp_rw [mul_sub, sub_mul, mul_assoc]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [c.sum_clippingPairAngles]
    unfold ClippedEdge.normalAngle
    ring
  rw [hs] at h
  linarith only [h]

theorem parallelQuadratic_clipped_eq_six_lens_terms (hA : c.totalDeficit ≤ 2 / 25) :
    parallelQuadratic (clippedOuterBody c.radius (range c.point) hne) =
      ClippedLens.meanBase c.radius + c.sixEdgeSum (ClippedLens.meanEdge c.radius) := by
  rw [c.parallelQuadratic_clipped_eq_face_edge_terms hA, c.sum_unitFaceNormals_area_lenses hA,
    c.sphereMeasure_real_radiusFaceNormals_lenses hA]
  simp only [ClippedLens.meanBase, ClippedLens.meanEdge, sixEdgeSum]
  ring

end BalancedContacts
end BlaschkeLebesgue
