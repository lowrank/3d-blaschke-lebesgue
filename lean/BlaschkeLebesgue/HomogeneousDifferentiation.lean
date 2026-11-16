module

public import BlaschkeLebesgue.TangentJacobian

/-!
# Degree-zero homogeneity of the support Jacobian

The homogeneous support map has degree one, so its derivative has degree zero.
Differentiability is equivalent along each positive ray, including the standard
zero derivative value on the exceptional rays.
-/

public noncomputable section

namespace BlaschkeLebesgue

theorem homogeneousSupport_hasFDerivAt_smul {K : ConvexBody Space} {x : Space}
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (homogeneousSupport K) A x)
    {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (homogeneousSupport K) A (r • x) := by
  have hd' : HasFDerivAt (homogeneousSupport K) A (r⁻¹ • (r • x)) := by
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using hd
  have h := (hd'.comp (r • x) ((hasFDerivAt_id (r • x)).const_smul r⁻¹)).const_smul r
  simpa only [Function.comp_def, Pi.smul_def, homogeneousSupport_smul K (inv_nonneg.2 hr.le),
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
    smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h

theorem homogeneousSupport_differentiableAt_smul_iff (K : ConvexBody Space) (x : Space)
    {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (homogeneousSupport K) (r • x) ↔
      DifferentiableAt ℝ (homogeneousSupport K) x := by
  constructor
  · intro hd
    have h := (homogeneousSupport_hasFDerivAt_smul hd.hasFDerivAt (inv_pos.2 hr)).differentiableAt
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using h
  · intro hd
    exact (homogeneousSupport_hasFDerivAt_smul hd.hasFDerivAt hr).differentiableAt

theorem fderiv_homogeneousSupport_smul (K : ConvexBody Space) (x : Space)
    {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (homogeneousSupport K) (r • x) = fderiv ℝ (homogeneousSupport K) x := by
  by_cases hd : DifferentiableAt ℝ (homogeneousSupport K) x
  · exact (homogeneousSupport_hasFDerivAt_smul hd.hasFDerivAt hr).fderiv
  · rw [fderiv_zero_of_not_differentiableAt hd,
      fderiv_zero_of_not_differentiableAt
        ((homogeneousSupport_differentiableAt_smul_iff K x hr).not.2 hd)]

theorem parallelJacobian_smul (K : ConvexBody Space) (t : ℝ) (x : Space)
    {r : ℝ} (hr : 0 < r) : parallelJacobian K t (r • x) = parallelJacobian K t x := by
  simp only [parallelJacobian, fderiv_homogeneousSupport_smul K x hr]

end BlaschkeLebesgue
