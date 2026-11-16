module

public import BlaschkeLebesgue.ShellDerivative
public import BlaschkeLebesgue.LocalJacobian

/-!
# The actual shell volume and its Jacobian

Change of variables on the compact annulus gives the difference of the actual
endpoint volumes. In polar coordinates the Jacobian is the support-height gap
times the tangent determinant, divided by the square of the radial coordinate.
-/

public noncomputable section

open MeasureTheory Set NormedSpace Filter
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem positive_det_nonneg {A : Space →L[ℝ] Space} (hA : A.IsPositive) : 0 ≤ A.det := by
  change 0 ≤ A.toLinearMap.det
  rw [hA.toLinearMap.isSymmetric.det_eq_prod_eigenvalues space_finrank]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact Finset.prod_nonneg fun i _ => hA.toLinearMap.nonneg_eigenvalues space_finrank i

theorem shellTangent_isPositive {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (ht : t ∈ Icc (0 : ℝ) 1) (u : UnitSphere) :
    (shellTangent D K ε δ t u).IsPositive :=
  (((sphereCurvature_isPositive hD u).smul_of_nonneg (sub_nonneg.2 ht.2)).add
    ((sphereCurvature_isPositive hK u).smul_of_nonneg ht.1)).add
    ((tangentProjection_isPositive u.norm_eq_one).smul_of_nonneg
      (add_nonneg hε (mul_nonneg ht.1 hδ)))

@[expose] def shellDensity (D K : ConvexBody Space) (ε δ t : ℝ) (u : UnitSphere) : ℝ :=
  (support K u - support D u + δ) *
    (shellTangent D K ε δ t u + normalProjection u).det

theorem shellDensity_nonneg {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space))
    {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (ht : t ∈ Icc (0 : ℝ) 1) (u : UnitSphere) :
    0 ≤ shellDensity D K ε δ t u :=
  mul_nonneg (add_nonneg (sub_nonneg.2 (support_mono_of_subset hDK u)) hδ)
    (positive_det_nonneg ((shellTangent_isPositive hD hK hε hδ ht u).add
      (normalProjection_isPositive u)))

theorem det_fderiv_shellMap_polar {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (ε δ : ℝ) (u : UnitSphere)
    (hd : DifferentiableAt ℝ (normalSupport D) (u : Space))
    (hk : DifferentiableAt ℝ (normalSupport K) (u : Space)) {r : ℝ} (hr : 0 < r) :
    (fderiv ℝ (shellMap D K ε δ) (r • (u : Space))).det =
      shellDensity D K ε δ (r - 1) u / r ^ 2 := by
  rw [(hasFDerivAt_shellMap_polar ε δ u hd hk hr).fderiv,
    det_tangent_add_normal u.norm_eq_one]
  · have hdet := det_tangent_smul_shift u (shellTangent D K ε δ (r - 1) u)
      (shellTangent_apply_normal D K ε δ (r - 1) u)
      (shellTangent_apply_tangent hD hK ε δ (r - 1) u) r⁻¹ 0
    have hz : (0 : ℝ) • tangentProjection (u : Space) = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, zero_smul, zero_apply]
    rw [hz] at hdet
    norm_num only [add_zero, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0)] at hdet
    rw [hdet, inner_shellIncrement, shellDensity]
    ring
  · intro v
    rw [smul_apply, inner_smul_right, shellTangent_apply_tangent hD hK, mul_zero]

theorem abs_det_fderiv_shellMap_polar_ae {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, ∀ r ∈ Icc (1 : ℝ) 2,
      |(fderiv ℝ (shellMap D K ε δ) (r • (u : Space))).det| =
        shellDensity D K ε δ (r - 1) u / r ^ 2 := by
  filter_upwards [normalSupport_sphere_ae_differentiable hD,
    normalSupport_sphere_ae_differentiable hK] with u hd hk
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
  rw [det_fderiv_shellMap_polar hD hK ε δ u hd hk hr0,
    abs_of_nonneg (div_nonneg (shellDensity_nonneg hD hK hDK hε hδ
      ⟨by linarith only [hr.1], by linarith only [hr.2]⟩ u) (sq_nonneg r))]

theorem bodyShell_volume {D K : ConvexBody Space}
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    (volume (bodyShell D K ε δ)).toReal =
      bodyVolume (parallelBody K (ε + δ)) - bodyVolume (parallelBody D ε) := by
  have hsub := parallelBody_subset_of_subset hDK hε (add_nonneg hε hδ)
    (le_add_of_nonneg_right hδ)
  have hi : interior (parallelBody D ε : Set Space) ⊆ (parallelBody K (ε + δ) : Set Space) :=
    interior_subset.trans hsub
  have hfinite := (parallelBody D ε).isCompact.measure_ne_top (μ := volume)
  rw [bodyShell, measure_sdiff hi isOpen_interior.measurableSet.nullMeasurableSet
    (measure_ne_top_of_subset interior_subset hfinite),
    measure_interior_of_null_frontier ((parallelBody D ε).convex.addHaar_frontier volume),
    ENNReal.toReal_sub_of_le (measure_mono hsub)
      ((parallelBody K (ε + δ)).isCompact.measure_ne_top (μ := volume))]
  rfl

/-- The integral is the volume of the actual shell, not a formal mixed-volume expression. -/
theorem shellJacobian_integral {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    IntegrableOn (fun x => |(fderiv ℝ (shellMap D K ε δ) x).det|) unitAnnulus ∧
      (∫ x in unitAnnulus, |(fderiv ℝ (shellMap D K ε δ) x).det|) =
        bodyVolume (parallelBody K (ε + δ)) - bodyVolume (parallelBody D ε) := by
  obtain ⟨C, hC⟩ := exists_lipschitzOn_shellMap hD hK ε δ
  have hd : ∀ᵐ x ∂volume.restrict unitAnnulus,
      HasFDerivAt (shellMap D K ε δ) (fderiv ℝ (shellMap D K ε δ) x) x := by
    filter_upwards [ae_restrict_of_ae (shellMap_ae_differentiable hD hK ε δ)] with x hx
    exact hx.hasFDerivAt
  obtain ⟨hi, he⟩ := integral_abs_det_of_lipschitzOn_injOn isCompact_unitAnnulus hC
    (shellMap_injOn hDK hε hδ) hd
  refine ⟨hi, ?_⟩
  rw [he, shellMap_image hD hK hDK hε.le hδ, bodyShell_volume hDK hε.le hδ.le]

end BlaschkeLebesgue
