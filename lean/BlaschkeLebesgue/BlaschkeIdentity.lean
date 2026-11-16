module

public import BlaschkeLebesgue.ParallelPolynomial

/-!
# Blaschke's identity for actual constant-width bodies

Complementary support maps add to the identity. In dimension three their
determinant polynomials satisfy `P_L(t) = -P_K(-1-t)`. For constant width one,
the complement is the reflected body and has the same parallel volumes.
Two evaluations determine the coefficients and prove Blaschke's identity.
-/

public noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise

namespace BlaschkeLebesgue

theorem reflectBody_smul (K : ConvexBody Space) (t : ℝ) :
    reflectBody (t • K) = t • reflectBody K := by
  exact smul_comm (-1 : ℝ) t K

theorem reflectBody_parallelBody (K : ConvexBody Space) (t : ℝ) :
    reflectBody (parallelBody K t) = parallelBody (reflectBody K) t := by
  rw [parallelBody, reflectBody_add, reflectBody_smul, reflectBody_unitBallBody, parallelBody]

theorem zero_mem_interior_reflectBody {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    (0 : Space) ∈ interior (reflectBody K : Set Space) := by
  change (0 : Space) ∈ interior ((-1 : ℝ) • (K : Set Space))
  rw [interior_smul₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  exact ⟨0, h0, by simp⟩

theorem parallelJacobian_complement_ae {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    ∀ᵐ x ∂(volume : Measure Space), ∀ t : ℝ,
      parallelJacobian L t x = -parallelJacobian K (-1 - t) x := by
  filter_upwards [homogeneousSupport_ae_differentiable_of_ball_sum hKL] with x hx
  have heq : homogeneousSupport L = fun y => y - homogeneousSupport K y := by
    funext y
    have h := homogeneousSupport_add_of_ball_sum hKL y
    exact eq_sub_of_add_eq' h
  have hd : HasFDerivAt (homogeneousSupport L)
      (ContinuousLinearMap.id ℝ Space - fderiv ℝ (homogeneousSupport K) x) x := by
    rw [heq]
    exact (hasFDerivAt_id x).sub hx.hasFDerivAt
  intro t
  rw [parallelJacobian, hd.fderiv]
  have hid : ContinuousLinearMap.id ℝ Space - fderiv ℝ (homogeneousSupport K) x +
      t • ContinuousLinearMap.id ℝ Space =
      -(fderiv ℝ (homogeneousSupport K) x + (-1 - t) • ContinuousLinearMap.id ℝ Space) := by
    module
  rw [hid, ← neg_one_smul ℝ]
  change LinearMap.det ((-1 : ℝ) •
    (fderiv ℝ (homogeneousSupport K) x + (-1 - t) • ContinuousLinearMap.id ℝ Space).toLinearMap) = _
  rw [LinearMap.det_smul]
  norm_num [Space, parallelJacobian, ContinuousLinearMap.det]

theorem parallelPolynomial_complement {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (hK0 : (0 : Space) ∈ interior (K : Set Space))
    (hL0 : (0 : Space) ∈ interior (L : Set Space)) (t : ℝ) :
    parallelPolynomial L t = -parallelPolynomial K (-1 - t) := by
  have hLK : L + K = unitBallBody := by rwa [add_comm]
  rw [parallelPolynomial_eq_integral hLK hL0 t,
    parallelPolynomial_eq_integral hKL hK0 (-1 - t), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (parallelJacobian_complement_ae hKL)] with x hx using hx t

theorem HasConstantWidth.parallelPolynomial_symmetry {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {t : ℝ} (ht : 0 < t) : parallelPolynomial K t = -parallelPolynomial K (-1 - t) := by
  have hL0 := zero_mem_interior_reflectBody h0
  have hLK : reflectBody K + K = unitBallBody := by rw [add_comm]; exact hK.add_reflectBody
  calc
    parallelPolynomial K t = bodyVolume (parallelBody K t) :=
      parallelPolynomial_eq_volume_pos hK.add_reflectBody h0 ht
    _ = bodyVolume (parallelBody (reflectBody K) t) := by
      rw [← reflectBody_parallelBody, bodyVolume_reflectBody]
    _ = parallelPolynomial (reflectBody K) t :=
      (parallelPolynomial_eq_volume_pos hLK hL0 ht).symm
    _ = -parallelPolynomial K (-1 - t) :=
      parallelPolynomial_complement hK.add_reflectBody h0 hL0 t

/-- Blaschke's identity, with the linear coefficient of actual parallel volume. -/
theorem HasConstantWidth.blaschke_identity {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    parallelLinear K = 2 * bodyVolume K + 2 * Real.pi / 3 ∧
      parallelQuadratic K = 2 * Real.pi := by
  have h1 := hK.parallelPolynomial_symmetry h0 (t := 1) (by norm_num)
  have h2 := hK.parallelPolynomial_symmetry h0 (t := 2) (by norm_num)
  simp only [parallelPolynomial, parallelConstant_eq_volume hK.add_reflectBody h0,
    bodyVolume_unitBallBody] at h1 h2
  norm_num at h1 h2
  constructor <;> nlinarith only [h1, h2]

/-- The complete parallel-volume polynomial of a unit-width body. -/
theorem HasConstantWidth.parallelBody_volume {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {t : ℝ} (ht : 0 ≤ t) :
    bodyVolume (parallelBody K t) = bodyVolume K +
      t * (2 * bodyVolume K + 2 * Real.pi / 3) + 2 * Real.pi * t ^ 2 +
        (4 * Real.pi / 3) * t ^ 3 := by
  rw [parallelBody_volume_polynomial hK.add_reflectBody h0 ht,
    (hK.blaschke_identity h0).1, (hK.blaschke_identity h0).2]
  ring

theorem HasConstantWidth.parallelBody_volume_derivative {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    HasDerivWithinAt (fun t => bodyVolume (parallelBody K t))
      (2 * bodyVolume K + 2 * Real.pi / 3) (Ici 0) 0 := by
  rw [← (hK.blaschke_identity h0).1]
  exact parallelBody_hasDerivWithinAt_zero hK.add_reflectBody h0

end BlaschkeLebesgue
