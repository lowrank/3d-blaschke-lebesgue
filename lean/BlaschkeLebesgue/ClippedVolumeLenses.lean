module

public import BlaschkeLebesgue.ClippedLensFaces
public import BlaschkeLebesgue.ClippedSurfaceIntegrals

/-! # The actual clipped-body volume as six explicit scalar lens terms -/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue

namespace ClippedLens

@[expose] def baseArea (R : ℝ) : ℝ := 2 * Real.pi * (1 - 1 / (2 * R))
@[expose] def baseMoment (R : ℝ) : ℝ := -R * Real.pi * (1 - 1 / (4 * R ^ 2))
@[expose] def unitArea (R s : ℝ) : ℝ :=
  lensAreaExpression (unitHeight R) (neighborHeight s) (unitAxisInner R s)
@[expose] def unitMoment (R s : ℝ) : ℝ :=
  -R * lensMomentExpression (unitHeight R) (neighborHeight s) (unitAxisInner R s)
@[expose] def radiusArea (R s : ℝ) : ℝ :=
  lensAreaExpression (radiusHeight R) (radiusHeight R) (radiusAxisInner R s)
@[expose] def radiusBaseArea (R : ℝ) : ℝ :=
  4 * Real.pi - 8 * Real.pi * (2 - 1 / (2 * R ^ 2))

@[expose] def volumeBase (R : ℝ) : ℝ :=
  (-8 * baseArea R - 8 * baseMoment R + R ^ 3 * radiusBaseArea R) / 3
@[expose] def volumeEdge (R s : ℝ) : ℝ :=
  (2 * unitArea R s + 2 * unitMoment R s + R ^ 3 * radiusArea R s) / 3

end ClippedLens

theorem subtract_sum_four_of_zero_diagonal (i : Fin 4) (B : ℝ) (r l : Fin 4 → ℝ)
    (hi : r i = 0) (h : ∀ j ≠ i, r j = B - l j) :
    B - ∑ j, r j = -2 * B + ∑ j ∈ Finset.univ.erase i, l j := by
  classical
  have he : (∑ j, r j) = ∑ j ∈ Finset.univ.erase i, r j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hi, sub_zero]
  rw [he]
  have he' : (∑ j ∈ Finset.univ.erase i, r j) =
      ∑ j ∈ Finset.univ.erase i, (B - l j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact h j (Finset.mem_erase.1 hj).1
  rw [he', Finset.sum_sub_distrib, Finset.sum_const]
  have hn : (Finset.univ.erase i : Finset (Fin 4)).card = 3 := by simp
  rw [hn]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)

@[expose] def sixEdgeSum (f : ℝ → ℝ) : ℝ :=
  f ‖c.point 1 - c.point 0‖ + f ‖c.point 2 - c.point 0‖ + f ‖c.point 3 - c.point 0‖ +
    f ‖c.point 2 - c.point 1‖ + f ‖c.point 3 - c.point 1‖ + f ‖c.point 3 - c.point 2‖

theorem sum_pair_lengths (f : ℝ → ℝ) :
    (∑ i : Fin 4, ∑ j ∈ Finset.univ.erase i, f ‖c.point j - c.point i‖) = 2 * c.sixEdgeSum f := by
  classical
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_four, sixEdgeSum,
    norm_sub_rev]
  ring

theorem sphereMeasure_real_unitFaceNormals_lenses (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    sphereMeasure.real (c.unitFaceNormals i) = -2 * ClippedLens.baseArea c.radius +
      ∑ j ∈ Finset.univ.erase i, ClippedLens.unitArea c.radius ‖c.point j - c.point i‖ := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  rw [c.sphereMeasure_real_unitFaceNormals hA, c.sphereMeasure_real_unitFaceCap hR.le]
  apply subtract_sum_four_of_zero_diagonal
  · rw [c.unitRemovedCap_self, measureReal_empty]
  · intro j hji
    rw [c.sphereMeasure_real_unitRemovedCap, c.sphereMeasure_real_unitFaceCap hR.le,
      c.sphereMeasure_real_unitFaceCap_inter hA (Ne.symm hji)]
    rfl

theorem integral_unitFaceNormals_inner_lenses (hA : c.totalDeficit ≤ 2 / 25) (i : Fin 4) :
    (∫ n in c.unitFaceNormals i, ⟪c.point i, (n : Space)⟫_ℝ ∂sphereMeasure) =
      -2 * ClippedLens.baseMoment c.radius +
        ∑ j ∈ Finset.univ.erase i, ClippedLens.unitMoment c.radius ‖c.point j - c.point i‖ := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  rw [c.integral_unitFaceNormals hA i (integrable_sphere_inner (c.point i)),
    c.integral_unitFaceCap_inner hR]
  apply subtract_sum_four_of_zero_diagonal
  · rw [c.unitRemovedCap_self, setIntegral_empty]
  · intro j hji
    rw [c.integral_unitRemovedCap_inner, c.integral_unitFaceCap_inner hR,
      c.integral_unitFaceCap_inter_inner hA (Ne.symm hji)]
    rfl

theorem sum_unitFaceNormals_area_lenses (hA : c.totalDeficit ≤ 2 / 25) :
    (∑ i, sphereMeasure.real (c.unitFaceNormals i)) =
      -8 * ClippedLens.baseArea c.radius + 2 * c.sixEdgeSum (ClippedLens.unitArea c.radius) := by
  simp_rw [c.sphereMeasure_real_unitFaceNormals_lenses hA]
  rw [Finset.sum_add_distrib, c.sum_pair_lengths]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem sum_unitFaceNormals_moment_lenses (hA : c.totalDeficit ≤ 2 / 25) :
    (∑ i, ∫ n in c.unitFaceNormals i, ⟪c.point i, (n : Space)⟫_ℝ ∂sphereMeasure) =
      -8 * ClippedLens.baseMoment c.radius + 2 * c.sixEdgeSum (ClippedLens.unitMoment c.radius) := by
  simp_rw [c.integral_unitFaceNormals_inner_lenses hA]
  rw [Finset.sum_add_distrib, c.sum_pair_lengths]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem sphereMeasure_real_radiusFaceNormals_lenses (hA : c.totalDeficit ≤ 2 / 25) :
    sphereMeasure.real c.radiusFaceNormals = ClippedLens.radiusBaseArea c.radius +
      c.sixEdgeSum (ClippedLens.radiusArea c.radius) := by
  rw [c.sphereMeasure_real_radiusFaceNormals hA (Opposite.radius_gt_half_of_small_deficit c hA)]
  rw [c.sphereMeasure_real_radiusExcludedCap_inter hA (by decide : (0 : Fin 4) ≠ 1),
    c.sphereMeasure_real_radiusExcludedCap_inter hA (by decide : (0 : Fin 4) ≠ 2),
    c.sphereMeasure_real_radiusExcludedCap_inter hA (by decide : (0 : Fin 4) ≠ 3),
    c.sphereMeasure_real_radiusExcludedCap_inter hA (by decide : (1 : Fin 4) ≠ 2),
    c.sphereMeasure_real_radiusExcludedCap_inter hA (by decide : (1 : Fin 4) ≠ 3),
    c.sphereMeasure_real_radiusExcludedCap_inter hA (by decide : (2 : Fin 4) ≠ 3)]
  rfl

theorem bodyVolume_clipped_eq_six_lens_terms (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} :
    bodyVolume (clippedOuterBody c.radius (range c.point) hne) =
      ClippedLens.volumeBase c.radius + c.sixEdgeSum (ClippedLens.volumeEdge c.radius) := by
  have h := c.bodyVolume_clipped_eq_face_integrals (hne := hne) hA
    (Opposite.radius_gt_half_of_small_deficit c hA)
  rw [c.sum_unitFaceNormals_area_lenses hA, c.sum_unitFaceNormals_moment_lenses hA,
    c.sphereMeasure_real_radiusFaceNormals_lenses hA] at h
  simp only [ClippedLens.volumeBase, ClippedLens.volumeEdge, sixEdgeSum] at h ⊢
  linear_combination h / 3

theorem parallelLinear_clipped_eq_lens_terms (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} :
    parallelLinear (clippedOuterBody c.radius (range c.point) hne) =
      c.radius ^ 2 * (ClippedLens.radiusBaseArea c.radius + c.sixEdgeSum (ClippedLens.radiusArea c.radius)) -
        8 * ClippedLens.baseArea c.radius + 2 * c.sixEdgeSum (ClippedLens.unitArea c.radius) := by
  rw [c.parallelLinear_clipped_eq_face_areas (hne := hne) hA
      (Opposite.radius_gt_half_of_small_deficit c hA),
    c.sum_unitFaceNormals_area_lenses hA, c.sphereMeasure_real_radiusFaceNormals_lenses hA]
  ring

end BalancedContacts
end BlaschkeLebesgue
