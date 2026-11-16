module

public import BlaschkeLebesgue.MidpointQuadrature

/-!
# Two-dimensional midpoint quadrature from pure second derivatives

Applying the one-dimensional estimate in succession gives the certificate's
error term. Only the two pure second derivatives occur; no mixed derivative
bound is required. The positive-part variant justifies the retained cell's
nonnegative lower contribution.
-/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue

theorem rectangle_midpoint_quadrature_lower
    {H Hx Hxx Hy Hyy : ℝ × ℝ → ℝ} {mx my h k Mx My : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hH : Continuous H)
    (hHx : ∀ x ∈ Icc (mx - h) (mx + h), HasDerivAt (fun x ↦ H (x, my)) (Hx (x, my)) x)
    (hHxx : ∀ x ∈ Icc (mx - h) (mx + h), HasDerivAt (fun x ↦ Hx (x, my)) (Hxx (x, my)) x)
    (hHy : ∀ x ∈ Icc (mx - h) (mx + h), ∀ y ∈ Icc (my - k) (my + k),
      HasDerivAt (fun y ↦ H (x, y)) (Hy (x, y)) y)
    (hHyy : ∀ x ∈ Icc (mx - h) (mx + h), ∀ y ∈ Icc (my - k) (my + k),
      HasDerivAt (fun y ↦ Hy (x, y)) (Hyy (x, y)) y)
    (hMx : ∀ x ∈ Icc (mx - h) (mx + h), -Mx ≤ Hxx (x, my))
    (hMy : ∀ x ∈ Icc (mx - h) (mx + h), ∀ y ∈ Icc (my - k) (my + k), -My ≤ Hyy (x, y)) :
    4 * h * k * (H (mx, my) - Mx * h ^ 2 / 6 - My * k ^ 2 / 6) ≤
      ∫ x in (mx - h)..(mx + h), ∫ y in (my - k)..(my + k), H (x, y) := by
  have hxord : mx - h ≤ mx + h := by linarith
  have hyord : my - k ≤ my + k := by linarith
  have hinner (x : ℝ) (hx : x ∈ Icc (mx - h) (mx + h)) :
      2 * k * (H (x, my) - My * k ^ 2 / 6) ≤ ∫ y in (my - k)..(my + k), H (x, y) :=
    midpoint_quadrature_lower hk (hHy x hx) (hHyy x hx) (hMy x hx)
  have hi : IntegrableOn H (Ioc (mx - h) (mx + h) ×ˢ Ioc (my - k) (my + k)) (volume.prod volume) :=
    (hH.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hip : Integrable H ((volume.restrict (Ioc (mx - h) (mx + h))).prod
      (volume.restrict (Ioc (my - k) (my + k)))) := by
    rwa [Measure.prod_restrict]
  have houter : IntervalIntegrable (fun x ↦ ∫ y in (my - k)..(my + k), H (x, y)) volume (mx - h) (mx + h) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hxord).2
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hyord] using hip.integral_prod_left
  have hcenter : Continuous (fun x : ℝ ↦ H (x, my)) := hH.comp (continuous_id.prodMk continuous_const)
  have hiCenter := hcenter.intervalIntegrable (mx - h) (mx + h) (μ := volume)
  have hlow : IntervalIntegrable (fun x ↦ 2 * k * (H (x, my) - My * k ^ 2 / 6)) volume (mx - h) (mx + h) :=
    (show Continuous (fun x : ℝ ↦ 2 * k * (H (x, my) - My * k ^ 2 / 6)) by fun_prop).intervalIntegrable _ _
  have hcomp := intervalIntegral.integral_mono_on hxord hlow houter hinner
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hiCenter intervalIntegrable_const,
    intervalIntegral.integral_const] at hcomp
  simp only [smul_eq_mul] at hcomp
  have hmid := midpoint_quadrature_lower hh hHx hHxx hMx
  have hmid' := mul_le_mul_of_nonneg_left hmid (show 0 ≤ 2 * k by positivity)
  nlinarith only [hcomp, hmid']

theorem rectangle_midpoint_quadrature_posPart
    {H Hx Hxx Hy Hyy : ℝ × ℝ → ℝ} {mx my h k Mx My : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hH : Continuous H)
    (hHx : ∀ x ∈ Icc (mx - h) (mx + h), HasDerivAt (fun x ↦ H (x, my)) (Hx (x, my)) x)
    (hHxx : ∀ x ∈ Icc (mx - h) (mx + h), HasDerivAt (fun x ↦ Hx (x, my)) (Hxx (x, my)) x)
    (hHy : ∀ x ∈ Icc (mx - h) (mx + h), ∀ y ∈ Icc (my - k) (my + k),
      HasDerivAt (fun y ↦ H (x, y)) (Hy (x, y)) y)
    (hHyy : ∀ x ∈ Icc (mx - h) (mx + h), ∀ y ∈ Icc (my - k) (my + k),
      HasDerivAt (fun y ↦ Hy (x, y)) (Hyy (x, y)) y)
    (hMx : ∀ x ∈ Icc (mx - h) (mx + h), -Mx ≤ Hxx (x, my))
    (hMy : ∀ x ∈ Icc (mx - h) (mx + h), ∀ y ∈ Icc (my - k) (my + k), -My ≤ Hyy (x, y))
    (h0 : ∀ x ∈ Icc (mx - h) (mx + h), ∀ y ∈ Icc (my - k) (my + k), 0 ≤ H (x, y)) :
    4 * h * k * max (H (mx, my) - Mx * h ^ 2 / 6 - My * k ^ 2 / 6) 0 ≤
      ∫ x in (mx - h)..(mx + h), ∫ y in (my - k)..(my + k), H (x, y) := by
  by_cases hp : 0 ≤ H (mx, my) - Mx * h ^ 2 / 6 - My * k ^ 2 / 6
  · rw [max_eq_left hp]
    exact rectangle_midpoint_quadrature_lower hh hk hH hHx hHxx hHy hHyy hMx hMy
  · rw [max_eq_right (le_of_not_ge hp), mul_zero]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro x hx
    exact intervalIntegral.integral_nonneg (by linarith) (h0 x hx)

end BlaschkeLebesgue
