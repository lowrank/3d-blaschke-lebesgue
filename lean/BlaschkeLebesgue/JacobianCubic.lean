module

public import BlaschkeLebesgue.ParallelJacobian

/-!
# Cubic dependence of the determinant

Three positive-radius values recover the coefficients of the monic cubic
`det (A + t I)`. This also proves integrability of all its coefficients from
the already established positive-radius change-of-variables formula.
-/

public noncomputable section

open MeasureTheory Metric

namespace BlaschkeLebesgue

@[expose] def cubicConstant (a b c : ℝ) : ℝ := 3 * a - 3 * b + c - 6
@[expose] def cubicLinear (a b c : ℝ) : ℝ := (-5 * a + 8 * b - 3 * c + 22) / 2
@[expose] def cubicQuadratic (a b c : ℝ) : ℝ := (a - 2 * b + c - 12) / 2

theorem matrix_det_shift_cubic (A : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (A + t • 1).det =
      cubicConstant (A + (1 : ℝ) • 1).det (A + (2 : ℝ) • 1).det (A + (3 : ℝ) • 1).det +
      t * cubicLinear (A + (1 : ℝ) • 1).det (A + (2 : ℝ) • 1).det (A + (3 : ℝ) • 1).det +
      t ^ 2 * cubicQuadratic (A + (1 : ℝ) • 1).det
        (A + (2 : ℝ) • 1).det (A + (3 : ℝ) • 1).det + t ^ 3 := by
  simp [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply,
    cubicConstant, cubicLinear, cubicQuadratic]
  ring

theorem linearMap_det_shift_cubic (A : Space →L[ℝ] Space) (t : ℝ) :
    let f := fun s : ℝ => (A + s • ContinuousLinearMap.id ℝ Space).det
    f t = cubicConstant (f 1) (f 2) (f 3) + t * cubicLinear (f 1) (f 2) (f 3) +
      t ^ 2 * cubicQuadratic (f 1) (f 2) (f 3) + t ^ 3 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let M := LinearMap.toMatrix b b A.toLinearMap
  have he (s : ℝ) : (A + s • ContinuousLinearMap.id ℝ Space).det = (M + s • 1).det := by
    change LinearMap.det (A.toLinearMap + s • LinearMap.id) = _
    rw [← LinearMap.det_toMatrix b, map_add, map_smul, LinearMap.toMatrix_id]
  dsimp only
  rw [he t, he 1, he 2, he 3]
  exact matrix_det_shift_cubic M t

@[expose] def jacobianConstant (K : ConvexBody Space) (x : Space) : ℝ :=
  cubicConstant (parallelJacobian K 1 x) (parallelJacobian K 2 x) (parallelJacobian K 3 x)

@[expose] def jacobianLinear (K : ConvexBody Space) (x : Space) : ℝ :=
  cubicLinear (parallelJacobian K 1 x) (parallelJacobian K 2 x) (parallelJacobian K 3 x)

@[expose] def jacobianQuadratic (K : ConvexBody Space) (x : Space) : ℝ :=
  cubicQuadratic (parallelJacobian K 1 x) (parallelJacobian K 2 x) (parallelJacobian K 3 x)

theorem parallelJacobian_cubic (K : ConvexBody Space) (t : ℝ) (x : Space) :
    parallelJacobian K t x = jacobianConstant K x + t * jacobianLinear K x +
      t ^ 2 * jacobianQuadratic K x + t ^ 3 :=
  linearMap_det_shift_cubic (fderiv ℝ (homogeneousSupport K) x) t

theorem jacobian_coefficients_integrable {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    IntegrableOn (jacobianConstant K) (closedBall 0 1) ∧
      IntegrableOn (jacobianLinear K) (closedBall 0 1) ∧
      IntegrableOn (jacobianQuadratic K) (closedBall 0 1) := by
  have h1 := (parallelJacobian_integral hKL h0 (t := 1) (by norm_num)).1
  have h2 := (parallelJacobian_integral hKL h0 (t := 2) (by norm_num)).1
  have h3 := (parallelJacobian_integral hKL h0 (t := 3) (by norm_num)).1
  have hc (r : ℝ) : IntegrableOn (fun _ : Space => r) (closedBall 0 1) :=
    integrableOn_const (isCompact_closedBall (0 : Space) 1).measure_ne_top
  refine ⟨?_, ?_, ?_⟩
  · exact (((h1.const_mul 3).sub (h2.const_mul 3)).add h3).sub (hc 6)
  · exact ((((h1.const_mul (-5)).add (h2.const_mul 8)).sub (h3.const_mul 3)).add
      (hc 22)).div_const 2
  · exact (((h1.sub (h2.const_mul 2)).add h3).sub (hc 12)).div_const 2

end BlaschkeLebesgue
