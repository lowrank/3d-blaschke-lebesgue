module

public import BlaschkeLebesgue.SphereHeightIntegral
public import BlaschkeLebesgue.SphereIsometry
public import BlaschkeLebesgue.ClippedFaceCaps

/-! # Exact first moments of spherical caps -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem integrable_sphere_inner (v : Space) :
    Integrable (fun n : UnitSphere ↦ ⟪v, (n : Space)⟫_ℝ) sphereMeasure :=
  (continuous_const.inner continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The cap's first moment, tested against any ambient vector. -/
theorem integral_sphereCap_inner {u : Space} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : c ∈ Icc (-1 : ℝ) 1) (v : Space) :
    (∫ n in sphereCap u c, ⟪v, (n : Space)⟫_ℝ ∂sphereMeasure) =
      ⟪v, u⟫_ℝ * Real.pi * (1 - c ^ 2) := by
  let e : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ u).reflection
  have heu : e u = u := Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self u)
  have he (n : UnitSphere) : ⟪v, (sphereIsometry e n : Space)⟫_ℝ =
      (2 * ⟪v, u⟫_ℝ) * ⟪u, (n : Space)⟫_ℝ - ⟪v, (n : Space)⟫_ℝ := by
    rw [sphereIsometry_val]
    change ⟪v, (ℝ ∙ u).reflection (n : Space)⟫_ℝ = _
    simp only [Submodule.reflection_singleton_apply, hu, RCLike.ofReal_one, one_pow, div_one, two_smul,
      inner_sub_right, inner_add_right, real_inner_smul_right]
    ring
  have hint := integral_cap_sphereIsometry e u c (fun n ↦ ⟪v, (n : Space)⟫_ℝ)
  rw [heu] at hint
  simp_rw [he] at hint
  rw [integral_sub ((integrable_sphere_inner u).const_mul (2 * ⟪v, u⟫_ℝ)).integrableOn
      (integrable_sphere_inner v).integrableOn,
    integral_const_mul, integral_sphereCap_inner_self hu hc] at hint
  linarith

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)

theorem integral_unitFaceCap_inner (hR : 1 / 2 < c.radius) (i : Fin 4) :
    (∫ n in c.unitFaceCap i, ⟪c.point i, (n : Space)⟫_ℝ ∂sphereMeasure) =
      -c.radius * Real.pi * (1 - 1 / (4 * c.radius ^ 2)) := by
  have hR0 : 0 < c.radius := by linarith
  have hn : ‖-c.point i‖ = c.radius := by rw [norm_neg, c.on_sphere]
  have hp : -c.point i ≠ 0 := norm_pos_iff.1 (hn.symm ▸ hR0)
  let u : Space := c.radius⁻¹ • (-c.point i)
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0, hn, inv_mul_cancel₀ hR0.ne']
  have hc : 1 / (2 * c.radius) ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (by positivity)
    · exact (div_le_one (by positivity : 0 < 2 * c.radius)).2 (by linarith)
  have hcap : c.unitFaceCap i = sphereCap u (1 / (2 * c.radius)) := by
    change sphereCap (-c.point i) (1 / 2) = _
    rw [sphereCap_normalize hp, hn]
    congr 1
    ring
  have hi : ⟪c.point i, u⟫_ℝ = -c.radius := by
    simp only [u, real_inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq, c.on_sphere]
    field_simp
  rw [hcap, integral_sphereCap_inner hu hc, hi]
  congr 2
  field_simp
  ring

theorem integral_unitRemovedCap_inner (i j : Fin 4) :
    (∫ n in c.unitRemovedCap i j, ⟪c.point i, (n : Space)⟫_ℝ ∂sphereMeasure) =
      (∫ n in c.unitFaceCap i, ⟪c.point i, (n : Space)⟫_ℝ ∂sphereMeasure) -
        ∫ n in c.unitFaceCap i ∩ c.unitNeighborCap i j,
          ⟪c.point i, (n : Space)⟫_ℝ ∂sphereMeasure := by
  have h := integral_inter_add_sdiff (μ := sphereMeasure) (s := c.unitFaceCap i)
    (c.measurableSet_unitNeighborCap i j) (integrable_sphere_inner (c.point i)).integrableOn
  change (∫ n in c.unitFaceCap i \ c.unitNeighborCap i j, ⟪c.point i, (n : Space)⟫_ℝ ∂sphereMeasure) = _
  linarith

end BalancedContacts
end BlaschkeLebesgue
