module

public import BlaschkeLebesgue.EquatorMeasure
public import BlaschkeLebesgue.ClippedPairRelabeling

/-! # The exact surviving angular length on each enclosing-sphere circle -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue.BalancedContacts

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

variable (c : BalancedContacts 4 Space)

@[expose] def clippingCircleAnglePoint (i : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space)
    (a : AddCircle (2 * Real.pi)) : Space := c.clippingCirclePoint i (e.symm (equatorPoint a))

@[expose] def radiusCircleLongitudes (i : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) :
    Set (AddCircle (2 * Real.pi)) := {a | ∀ j, ‖c.clippingCircleAnglePoint i e a - c.point j‖ ≤ 1}

@[expose] def radiusCircleExcludedLongitudes (i j : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) :
    Set (AddCircle (2 * Real.pi)) := {a | 1 < ‖c.clippingCircleAnglePoint i e a - c.point j‖}

@[expose] def clippingPairAngle (i j : Fin 4) : ℝ :=
  if i = j then 0 else Real.arccos (c.clippingPairCos i j)

@[fun_prop] theorem continuous_clippingCircleAnglePoint (i : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) :
    Continuous (c.clippingCircleAnglePoint i e) := by
  unfold clippingCircleAnglePoint clippingCirclePoint
  fun_prop

theorem clippingCircleAngleDirection_frame (hR : 0 < c.radius) (i : Fin 4)
    (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (c.clippingCircleAxis i) = coordinatePole)
    (a : AddCircle (2 * Real.pi)) :
    ‖e.symm (equatorPoint a)‖ = 1 ∧ ⟪c.point i, e.symm (equatorPoint a)⟫_ℝ = 0 := by
  refine ⟨by rw [e.symm.norm_map, norm_equatorPoint], ?_⟩
  rw [← c.radius_smul_clippingCircleAxis hR.ne' i, real_inner_smul_left,
    ← e.inner_map_map, e.apply_symm_apply, hek, inner_coordinatePole_equatorPoint, mul_zero]

theorem clippingCircleAnglePoint_mem_spheres (hR : 1 / 2 < c.radius) (i : Fin 4)
    (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (c.clippingCircleAxis i) = coordinatePole)
    (a : AddCircle (2 * Real.pi)) :
    ‖c.clippingCircleAnglePoint i e a‖ = c.radius ∧
      ‖c.clippingCircleAnglePoint i e a - c.point i‖ = 1 := by
  have hf := c.clippingCircleAngleDirection_frame (by linarith : 0 < c.radius) i e hek a
  simpa only [mem_sphere, dist_zero_right, dist_eq_norm, sub_zero, clippingCircleAnglePoint] using
    c.clippingCirclePoint_mem_spheres hR hf.1 hf.2

theorem radiusCircleLongitudes_eq_compl (i : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) :
    c.radiusCircleLongitudes i e = (⋃ j, c.radiusCircleExcludedLongitudes i j e)ᶜ := by
  ext a
  simp only [radiusCircleLongitudes, radiusCircleExcludedLongitudes, mem_ofPred_eq,
    mem_compl_iff, mem_iUnion, not_exists, not_lt]

theorem measurableSet_radiusCircleExcludedLongitudes (i j : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) :
    MeasurableSet (c.radiusCircleExcludedLongitudes i j e) :=
  (isOpen_lt continuous_const
    (((c.continuous_clippingCircleAnglePoint i e).sub continuous_const).norm)).measurableSet

theorem measurableSet_radiusCircleLongitudes (i : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) :
    MeasurableSet (c.radiusCircleLongitudes i e) := by
  rw [c.radiusCircleLongitudes_eq_compl]
  exact (MeasurableSet.iUnion fun j ↦ c.measurableSet_radiusCircleExcludedLongitudes i j e).compl

theorem radiusCircleExcludedLongitudes_self (hR : 1 / 2 < c.radius) (i : Fin 4)
    (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (c.clippingCircleAxis i) = coordinatePole) :
    c.radiusCircleExcludedLongitudes i i e = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro a ha
  have h := (c.clippingCircleAnglePoint_mem_spheres hR i e hek a).2
  change 1 < ‖c.clippingCircleAnglePoint i e a - c.point i‖ at ha
  rw [h] at ha
  exact (lt_irrefl 1) ha

theorem radiusCircleExcludedLongitudes_pairwise_disjoint (hA : c.totalDeficit ≤ 2 / 25)
    (i : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (c.clippingCircleAxis i) = coordinatePole) :
    Pairwise (fun j k ↦ Disjoint (c.radiusCircleExcludedLongitudes i j e)
      (c.radiusCircleExcludedLongitudes i k e)) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  intro j k hjk
  by_cases hji : j = i
  · rw [hji, c.radiusCircleExcludedLongitudes_self hR i e hek]
    exact empty_disjoint _
  by_cases hki : k = i
  · rw [hki, c.radiusCircleExcludedLongitudes_self hR i e hek]
    exact disjoint_empty _
  apply Set.disjoint_left.2
  intro a haj hak
  have hs := c.clippingCircleAnglePoint_mem_spheres hR i e hek a
  have h := c.radius_lt_norm_of_three_distances hA hjk hji hki haj hak.le hs.2.ge
  rw [hs.1] at h
  exact (lt_irrefl c.radius) h

theorem volume_real_radiusCircleExcludedLongitudes (hA : c.totalDeficit ≤ 2 / 25)
    (i j : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (c.clippingCircleAxis i) = coordinatePole) :
    volume.real (c.radiusCircleExcludedLongitudes i j e) = 2 * c.clippingPairAngle i j := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  have hR0 : 0 < c.radius := by linarith
  by_cases hij : i = j
  · subst j
    rw [c.radiusCircleExcludedLongitudes_self hR i e hek]
    simp [clippingPairAngle]
  have he : c.radiusCircleExcludedLongitudes i j e =
      {a : AddCircle (2 * Real.pi) | c.clippingPairCos i j <
        ⟪e (c.clippingPairDirection i j), equatorPoint a⟫_ℝ} := by
    ext a
    have hf := c.clippingCircleAngleDirection_frame hR0 i e hek a
    have h := c.clippingCircle_excluded_pair_iff hA hij hf.1 hf.2
    change (1 < ‖c.clippingCirclePoint i (e.symm (equatorPoint a)) - c.point j‖) ↔ _
    rw [h, ← e.inner_map_map, e.apply_symm_apply]
    rfl
  have hd : ‖e (c.clippingPairDirection i j)‖ = 1 := by
    rw [e.norm_map, c.clippingPairDirection_norm hA hij]
  have hp : ⟪coordinatePole, e (c.clippingPairDirection i j)⟫_ℝ = 0 := by
    rw [← hek, e.inner_map_map, c.clippingPairDirection_inner_axis hR0]
  rw [he, measureReal_def, volume_equator_inner_gt hd hp,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (Real.arccos_nonneg _)),
    clippingPairAngle, ite_eq_right hij]

theorem volume_real_radiusCircleLongitudes (hA : c.totalDeficit ≤ 2 / 25)
    (i : Fin 4) (e : Space ≃ₗᵢ[ℝ] Space) (hek : e (c.clippingCircleAxis i) = coordinatePole) :
    volume.real (c.radiusCircleLongitudes i e) =
      2 * Real.pi - 2 * ∑ j, c.clippingPairAngle i j := by
  rw [c.radiusCircleLongitudes_eq_compl, measureReal_compl,
    measureReal_iUnion_fintype (c.radiusCircleExcludedLongitudes_pairwise_disjoint hA i e hek)
      (fun j ↦ c.measurableSet_radiusCircleExcludedLongitudes i j e)]
  · simp_rw [c.volume_real_radiusCircleExcludedLongitudes hA i _ e hek]
    rw [← Finset.mul_sum, measureReal_def, AddCircle.measure_univ,
      ENNReal.toReal_ofReal (by positivity)]
  · exact MeasurableSet.iUnion fun j ↦ c.measurableSet_radiusCircleExcludedLongitudes i j e

end BlaschkeLebesgue.BalancedContacts
