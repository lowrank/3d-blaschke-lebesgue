module

public import BlaschkeLebesgue.LipschitzJacobian
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual parallel volume as a determinant integral

The inverse estimate forces all positive-radius derivatives to be nonsingular.
A continuous path from the identity fixes their orientation. Thus the absolute
value in the Jacobian formula can be removed on one common full-measure set.
-/

public noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal

namespace BlaschkeLebesgue

theorem det_ne_zero_of_injective (A : Space →L[ℝ] Space) (hA : Function.Injective A) :
    A.det ≠ 0 := by
  intro h
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h) (LinearMap.ker_eq_bot.2 hA)

/-- An everywhere nonsingular positive shift has the orientation of the identity. -/
theorem det_add_smul_id_pos (A : Space →L[ℝ] Space)
    (hA : ∀ t : ℝ, 0 < t → Function.Injective (A + t • ContinuousLinearMap.id ℝ Space))
    {t : ℝ} (ht : 0 < t) : 0 < (A + t • ContinuousLinearMap.id ℝ Space).det := by
  let I := ContinuousLinearMap.id ℝ Space
  let g : ℝ → ℝ := fun s => (s • A + I).det
  have hgc : Continuous g := ContinuousLinearMap.continuous_det.comp
    ((continuous_id.smul continuous_const).add continuous_const)
  have hgne : ∀ s : ℝ, 0 ≤ s → g s ≠ 0 := by
    intro s hs
    rcases hs.eq_or_lt with rfl | hs
    · simp [g, I, ContinuousLinearMap.det]
    · have hid : s • (A + s⁻¹ • I) = s • A + I := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
      dsimp only [g]
      rw [← hid]
      change LinearMap.det (s • (A + s⁻¹ • I).toLinearMap) ≠ 0
      rw [LinearMap.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hs.ne')
        (det_ne_zero_of_injective _ (hA _ (inv_pos.2 hs)))
  have hgpos : ∀ s : ℝ, 0 ≤ s → 0 < g s := by
    intro s hs
    by_contra h
    obtain ⟨r, hr, hgr⟩ := isPreconnected_Ici.intermediate_value hs
      (show (0 : ℝ) ∈ Ici 0 by simp) hgc.continuousOn
      (show (0 : ℝ) ∈ Icc (g s) (g 0) from
        ⟨le_of_not_gt h, by simp [g, I, ContinuousLinearMap.det]⟩)
    exact hgne r hr hgr
  have hid : A + t • I = t • (t⁻¹ • A + I) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  change 0 < (A + t • I).det
  rw [hid]
  change 0 < LinearMap.det (t • (t⁻¹ • A + I).toLinearMap)
  rw [LinearMap.det_smul]
  exact mul_pos (pow_pos ht _) (hgpos _ (inv_nonneg.2 ht.le))

theorem exists_lipschitz_parallelSupport_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (t : ℝ) : ∃ C, LipschitzWith C (parallelSupport K t) := by
  obtain ⟨C, hC⟩ := exists_lipschitz_homogeneousSupport_of_ball_sum hKL
  exact ⟨C + ‖t‖₊, hC.add (lipschitzWith_smul t)⟩

/-- The determinant is a cubic polynomial in the parallel radius at each point. -/
@[expose] def parallelJacobian (K : ConvexBody Space) (t : ℝ) (x : Space) : ℝ :=
  (fderiv ℝ (homogeneousSupport K) x + t • ContinuousLinearMap.id ℝ Space).det

theorem parallelJacobian_ae_pos {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    ∀ᵐ x ∂(volume : Measure Space), ∀ t : ℝ, 0 < t → 0 < parallelJacobian K t x := by
  filter_upwards [parallelSupport_ae_hasFDerivAt hKL] with x hx
  intro t ht
  apply det_add_smul_id_pos _ _ ht
  intro s hs
  obtain ⟨C, hC⟩ := exists_antilipschitz_parallelSupport h0 hs
  exact fderiv_injective_of_antilipschitz hC (hx s)

/-- Change of variables gives actual Lebesgue volume, with no smoothness assumption on the body. -/
theorem parallelJacobian_integral {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    (h0 : (0 : Space) ∈ interior (K : Set Space)) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (parallelJacobian K t) (closedBall 0 1) ∧
      (∫ x in closedBall 0 1, parallelJacobian K t x) = bodyVolume (parallelBody K t) := by
  obtain ⟨C, hC⟩ := exists_lipschitz_parallelSupport_of_ball_sum hKL t
  have hd : ∀ᵐ x ∂(volume : Measure Space), HasFDerivAt (parallelSupport K t)
      (fderiv ℝ (homogeneousSupport K) x + t • ContinuousLinearMap.id ℝ Space) x := by
    filter_upwards [parallelSupport_ae_hasFDerivAt hKL] with x hx using hx t
  obtain ⟨hi, he⟩ := integral_abs_det_of_lipschitz_injective hC
    (parallelSupport_injective h0 ht) (isCompact_closedBall 0 1) hd
  have hae : (fun x => |parallelJacobian K t x|) =ᵐ[volume.restrict (closedBall 0 1)]
      parallelJacobian K t := by
    filter_upwards [ae_restrict_of_ae (parallelJacobian_ae_pos hKL h0)] with x hx
    exact abs_of_pos (hx t ht)
  refine ⟨hi.congr hae, ?_⟩
  rw [← integral_congr_ae hae]
  change (∫ x in closedBall 0 1,
    |(fderiv ℝ (homogeneousSupport K) x + t • ContinuousLinearMap.id ℝ Space).det|) = _
  rw [he, parallelSupport_image_closedBall hKL h0 ht.le]
  rfl

end BlaschkeLebesgue
