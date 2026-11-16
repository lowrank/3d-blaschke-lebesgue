module

public import BlaschkeLebesgue.ClippedLensParameters
public import BlaschkeLebesgue.CapMoments

/-! # Closed-form evaluation of the actual clipped face lenses -/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts

variable (c : BalancedContacts 4 Space)

@[expose] def contactCapAxis (i : Fin 4) : Space := -c.clippingCircleAxis i
@[expose] def edgeCapAxis (i j : Fin 4) : Space :=
  ‖c.point j - c.point i‖⁻¹ • (c.point j - c.point i)

theorem contactCapAxis_norm (hR : 0 < c.radius) (i : Fin 4) : ‖c.contactCapAxis i‖ = 1 := by
  rw [contactCapAxis, norm_neg, c.clippingCircleAxis_norm hR]

theorem edgeCapAxis_norm {i j : Fin 4} (hs : 0 < ‖c.point j - c.point i‖) :
    ‖c.edgeCapAxis i j‖ = 1 := by
  simp only [edgeCapAxis, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_cancel₀ hs.ne']

theorem unitFaceCap_normalized (hR : 0 < c.radius) (i : Fin 4) :
    c.unitFaceCap i = sphereCap (c.contactCapAxis i) (ClippedLens.unitHeight c.radius) := by
  have hn : ‖-c.point i‖ = c.radius := by rw [norm_neg, c.on_sphere]
  have hp : -c.point i ≠ 0 := norm_pos_iff.1 (hn.symm ▸ hR)
  rw [unitFaceCap, sphereCap_normalize hp, hn]
  simp only [contactCapAxis, clippingCircleAxis, smul_neg]
  congr 1
  unfold ClippedLens.unitHeight
  ring

theorem unitNeighborCap_normalized {i j : Fin 4} (hs : 0 < ‖c.point j - c.point i‖) :
    c.unitNeighborCap i j = sphereCap (c.edgeCapAxis i j)
      (ClippedLens.neighborHeight ‖c.point j - c.point i‖) := by
  rw [unitNeighborCap, sphereCap_normalize (norm_pos_iff.1 hs)]
  congr 1
  unfold ClippedLens.neighborHeight
  field_simp

theorem radiusExcludedCap_normalized (hR : 0 < c.radius) (i : Fin 4) :
    c.radiusExcludedCap i = openSphereCap (c.contactCapAxis i) (ClippedLens.radiusHeight c.radius) := by
  have hn : ‖-c.point i‖ = c.radius := by rw [norm_neg, c.on_sphere]
  have hp : -c.point i ≠ 0 := norm_pos_iff.1 (hn.symm ▸ hR)
  rw [radiusExcludedCap, openSphereCap_normalize hp, hn]
  simp only [contactCapAxis, clippingCircleAxis, smul_neg]
  congr 1
  unfold ClippedLens.radiusHeight
  field_simp

theorem inner_contacts_eq_edge (i j : Fin 4) :
    ⟪c.point i, c.point j⟫_ℝ = c.radius ^ 2 - ‖c.point j - c.point i‖ ^ 2 / 2 := by
  have h := norm_sub_sq_real (c.point j) (c.point i)
  rw [c.on_sphere, c.on_sphere, real_inner_comm] at h
  linarith

theorem inner_contactCapAxis_edgeCapAxis (hR : 0 < c.radius) {i j : Fin 4}
    (hs : 0 < ‖c.point j - c.point i‖) :
    ⟪c.contactCapAxis i, c.edgeCapAxis i j⟫_ℝ =
      ClippedLens.unitAxisInner c.radius ‖c.point j - c.point i‖ := by
  simp only [contactCapAxis, clippingCircleAxis, edgeCapAxis, inner_neg_left,
    real_inner_smul_left, real_inner_smul_right, inner_sub_right, c.inner_contacts_eq_edge,
    sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), ClippedLens.unitAxisInner]
  field_simp
  ring

theorem inner_contactCapAxes (hR : 0 < c.radius) (i j : Fin 4) :
    ⟪c.contactCapAxis i, c.contactCapAxis j⟫_ℝ =
      ClippedLens.radiusAxisInner c.radius ‖c.point j - c.point i‖ := by
  simp only [contactCapAxis, clippingCircleAxis, inner_neg_neg, real_inner_smul_left,
    real_inner_smul_right, c.inner_contacts_eq_edge, ClippedLens.radiusAxisInner]
  field_simp

theorem sphereMeasure_real_unitFaceCap_inter (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) :
    sphereMeasure.real (c.unitFaceCap i ∩ c.unitNeighborCap i j) =
      lensAreaExpression (ClippedLens.unitHeight c.radius)
        (ClippedLens.neighborHeight ‖c.point j - c.point i‖)
        (ClippedLens.unitAxisInner c.radius ‖c.point j - c.point i‖) := by
  obtain ⟨hR, hRlo, hRhi, hs, hs1, _⟩ := c.clipped_lens_parameter_bounds hA hij
  obtain ⟨ha, hb, hc, hbc, hD⟩ := ClippedLens.unit_parameters hR hRlo hRhi hs hs1
  rw [c.unitFaceCap_normalized hR, c.unitNeighborCap_normalized hs]
  have he := c.inner_contactCapAxis_edgeCapAxis hR hs
  have h := sphereMeasure_real_cap_inter_formula (c.contactCapAxis_norm hR i)
    (c.edgeCapAxis_norm hs) ha hb (he.symm ▸ hc) (he.symm ▸ hbc) (he.symm ▸ hD)
  rwa [he] at h

theorem integral_unitFaceCap_inter_inner (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) :
    (∫ n in c.unitFaceCap i ∩ c.unitNeighborCap i j, ⟪c.point i, (n : Space)⟫_ℝ ∂sphereMeasure) =
      -c.radius * lensMomentExpression (ClippedLens.unitHeight c.radius)
        (ClippedLens.neighborHeight ‖c.point j - c.point i‖)
        (ClippedLens.unitAxisInner c.radius ‖c.point j - c.point i‖) := by
  obtain ⟨hR, hRlo, hRhi, hs, hs1, _⟩ := c.clipped_lens_parameter_bounds hA hij
  obtain ⟨ha, hb, hc, hbc, hD⟩ := ClippedLens.unit_parameters hR hRlo hRhi hs hs1
  have he := c.inner_contactCapAxis_edgeCapAxis hR hs
  have h := integral_sphereCap_inter_inner_formula (c.contactCapAxis_norm hR i)
    (c.edgeCapAxis_norm hs) ha hb (he.symm ▸ hc) (he.symm ▸ hbc) (he.symm ▸ hD)
  rw [he] at h
  have hi (n : UnitSphere) : ⟪c.point i, (n : Space)⟫_ℝ =
      -c.radius * ⟪c.contactCapAxis i, (n : Space)⟫_ℝ := by
    simp only [contactCapAxis, clippingCircleAxis, inner_neg_left, real_inner_smul_left]
    field_simp
  simp_rw [hi]
  rw [integral_const_mul, c.unitFaceCap_normalized hR, c.unitNeighborCap_normalized hs, h]

theorem sphereMeasure_real_radiusExcludedCap_inter (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) :
    sphereMeasure.real (c.radiusExcludedCap i ∩ c.radiusExcludedCap j) =
      lensAreaExpression (ClippedLens.radiusHeight c.radius) (ClippedLens.radiusHeight c.radius)
        (ClippedLens.radiusAxisInner c.radius ‖c.point j - c.point i‖) := by
  obtain ⟨hR, hRlo, hRhi, hs, hs1, hslo⟩ := c.clipped_lens_parameter_bounds hA hij
  obtain ⟨ha, hc, hbc, hD⟩ := ClippedLens.radius_parameters hR hRlo hRhi hs hs1 hslo
  have he := c.inner_contactCapAxes hR i j
  have h := sphereMeasure_real_cap_inter_formula (c.contactCapAxis_norm hR i)
    (c.contactCapAxis_norm hR j) ha ha (he.symm ▸ hc) (he.symm ▸ hbc) (he.symm ▸ hD)
  rw [he] at h
  rw [c.radiusExcludedCap_normalized hR, c.radiusExcludedCap_normalized hR]
  have hi : c.contactCapAxis i ≠ 0 := norm_ne_zero_iff.1 (by rw [c.contactCapAxis_norm hR]; norm_num)
  have hj : c.contactCapAxis j ≠ 0 := norm_ne_zero_iff.1 (by rw [c.contactCapAxis_norm hR]; norm_num)
  have hae := (sphereCap_ae_eq_openCap hi (ClippedLens.radiusHeight c.radius)).inter
    (sphereCap_ae_eq_openCap hj (ClippedLens.radiusHeight c.radius))
  rw [← measureReal_congr hae]
  exact h

end BlaschkeLebesgue.BalancedContacts
