module

public import BlaschkeLebesgue.JacobianCubic
public import BlaschkeLebesgue.ParallelContinuity
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# A proved parallel-volume polynomial for summands of the ball

The coefficients are integrals of derivatives of the actual supporting-point
parametrization. Change of variables identifies the polynomial with actual
parallel volume for positive radii; continuity supplies radius zero.
-/

public noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace BlaschkeLebesgue

@[expose] def parallelConstant (K : ConvexBody Space) : ℝ :=
  ∫ x in closedBall 0 1, jacobianConstant K x

@[expose] def parallelLinear (K : ConvexBody Space) : ℝ :=
  ∫ x in closedBall 0 1, jacobianLinear K x

@[expose] def parallelQuadratic (K : ConvexBody Space) : ℝ :=
  ∫ x in closedBall 0 1, jacobianQuadratic K x

/-- The polynomial is defined for every real parameter, including negative ones. -/
@[expose] def parallelPolynomial (K : ConvexBody Space) (t : ℝ) : ℝ :=
  parallelConstant K + t * parallelLinear K + t ^ 2 * parallelQuadratic K +
    t ^ 3 * bodyVolume unitBallBody

theorem parallelJacobian_integrable_all {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) (t : ℝ) :
    IntegrableOn (parallelJacobian K t) (closedBall 0 1) := by
  obtain ⟨h0', h1, h2⟩ := jacobian_coefficients_integrable hKL h0
  have hc : IntegrableOn (fun _ : Space => t ^ 3) (closedBall 0 1) :=
    integrableOn_const (isCompact_closedBall (0 : Space) 1).measure_ne_top
  have hi : IntegrableOn (fun x => jacobianConstant K x + t * jacobianLinear K x +
      t ^ 2 * jacobianQuadratic K x + t ^ 3) (closedBall 0 1) :=
    ((h0'.add (h1.const_mul t)).add (h2.const_mul (t ^ 2))).add hc
  exact hi.congr (Eventually.of_forall fun x => (parallelJacobian_cubic K t x).symm)

theorem parallelPolynomial_eq_integral {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) (t : ℝ) :
    parallelPolynomial K t = ∫ x in closedBall 0 1, parallelJacobian K t x := by
  obtain ⟨h0', h1, h2⟩ := jacobian_coefficients_integrable hKL h0
  have hc : IntegrableOn (fun _ : Space => t ^ 3) (closedBall 0 1) :=
    integrableOn_const (isCompact_closedBall (0 : Space) 1).measure_ne_top
  have h01 : IntegrableOn (fun x => jacobianConstant K x + t * jacobianLinear K x)
      (closedBall 0 1) := h0'.add (h1.const_mul t)
  have h012 : IntegrableOn (fun x => jacobianConstant K x + t * jacobianLinear K x +
      t ^ 2 * jacobianQuadratic K x) (closedBall 0 1) := h01.add (h2.const_mul (t ^ 2))
  simp_rw [parallelJacobian_cubic]
  rw [integral_add h012 hc,
    integral_add h01 (h2.const_mul (t ^ 2)),
    integral_add h0' (h1.const_mul t), integral_const_mul, integral_const_mul,
    integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
  change parallelPolynomial K t = parallelConstant K + t * parallelLinear K +
    t ^ 2 * parallelQuadratic K + bodyVolume unitBallBody * t ^ 3
  unfold parallelPolynomial
  ring

theorem parallelPolynomial_eq_volume_pos {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {t : ℝ} (ht : 0 < t) : parallelPolynomial K t = bodyVolume (parallelBody K t) := by
  rw [parallelPolynomial_eq_integral hKL h0 t]
  exact (parallelJacobian_integral hKL h0 ht).2

theorem continuous_parallelPolynomial (K : ConvexBody Space) :
    Continuous (parallelPolynomial K) := by
  unfold parallelPolynomial
  fun_prop

theorem parallelConstant_eq_volume {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    (h0 : (0 : Space) ∈ interior (K : Set Space)) : parallelConstant K = bodyVolume K := by
  have hpoly : Tendsto (parallelPolynomial K) (𝓝[>] (0 : ℝ)) (𝓝 (parallelConstant K)) := by
    simpa only [parallelPolynomial, zero_mul, zero_pow (by norm_num : 3 ≠ 0),
      zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      ((continuous_parallelPolynomial K).tendsto 0).mono_left nhdsWithin_le_nhds
  have hvol := (parallelBody_volume_tendsto_zero h0).mono_left
    (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
  have heq : parallelPolynomial K =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => bodyVolume (parallelBody K t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact parallelPolynomial_eq_volume_pos hKL h0 ht
  exact tendsto_nhds_unique hpoly (hvol.congr' heq.symm)

/-- Steiner's cubic formula, proved here for actual summands of the unit ball. -/
theorem parallelBody_volume_polynomial {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {t : ℝ} (ht : 0 ≤ t) :
    bodyVolume (parallelBody K t) = bodyVolume K + t * parallelLinear K +
      t ^ 2 * parallelQuadratic K + (4 * Real.pi / 3) * t ^ 3 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [parallelBody_zero]
  · rw [← parallelPolynomial_eq_volume_pos hKL h0 ht, parallelPolynomial,
      parallelConstant_eq_volume hKL h0, bodyVolume_unitBallBody]
    ring

theorem parallelBody_hasDerivWithinAt_zero {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    HasDerivWithinAt (fun t => bodyVolume (parallelBody K t)) (parallelLinear K) (Ici 0) 0 := by
  have hd : HasDerivAt (fun t : ℝ => bodyVolume K + t * parallelLinear K +
      t ^ 2 * parallelQuadratic K + (4 * Real.pi / 3) * t ^ 3) (parallelLinear K) 0 := by
    convert (((hasDerivAt_id 0).mul_const (parallelLinear K)).const_add (bodyVolume K)
      |>.add (((hasDerivAt_pow 2 0).mul_const (parallelQuadratic K))))
      |>.add ((hasDerivAt_pow 3 0).const_mul (4 * Real.pi / 3)) using 1 <;>
        norm_num [Pi.add_apply]
    funext t
    rfl
  apply hd.hasDerivWithinAt.congr
  · intro t ht
    exact parallelBody_volume_polynomial hKL h0 ht
  · simp [parallelBody_zero]

end BlaschkeLebesgue
