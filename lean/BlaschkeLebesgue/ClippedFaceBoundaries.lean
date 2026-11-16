module

public import BlaschkeLebesgue.ClippedFaceCaps

/-! # Null boundaries and disjointness of the actual spherical face regions -/

public noncomputable section

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts

variable (c : BalancedContacts 4 Space)

theorem sphereMeasure_unitFace_radius_boundary (hR : 0 < c.radius) (i : Fin 4) :
    sphereMeasure {u : UnitSphere | ‖c.point i + (u : Space)‖ = c.radius} = 0 := by
  have hp : -c.point i ≠ 0 := by
    apply norm_pos_iff.1
    rw [norm_neg, c.on_sphere]
    exact hR
  apply measure_mono_null (t := {u : UnitSphere | ⟪-c.point i, (u : Space)⟫_ℝ = 1 / 2}) _
    (sphereMeasure_inner_level hp _)
  intro u hu
  change ⟪-c.point i, (u : Space)⟫_ℝ = 1 / 2
  rw [inner_neg_left]
  have h := norm_add_sq_real (c.point i) (u : Space)
  rw [c.on_sphere i, u.norm_eq_one, hu] at h
  linarith

theorem sphereMeasure_unitFace_neighbor_boundary (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) :
    sphereMeasure {u : UnitSphere | ‖c.point i + (u : Space) - c.point j‖ = 1} = 0 := by
  have hp : c.point j - c.point i ≠ 0 := sub_ne_zero.2
    (fun h ↦ hij ((c.point_injective_of_small_deficit hA h).symm))
  apply measure_mono_null (t := {u : UnitSphere |
    ⟪c.point j - c.point i, (u : Space)⟫_ℝ = ‖c.point j - c.point i‖ ^ 2 / 2}) _
    (sphereMeasure_inner_level hp _)
  intro u hu
  have he : c.point i + (u : Space) - c.point j = (u : Space) - (c.point j - c.point i) := by abel
  have h := norm_sub_sq_real (u : Space) (c.point j - c.point i)
  rw [← he, hu, u.norm_eq_one, real_inner_comm] at h
  change ⟪c.point j - c.point i, (u : Space)⟫_ℝ = _
  linarith

theorem sphereMeasure_radiusFace_boundary (hR : 0 < c.radius) (i : Fin 4) :
    sphereMeasure {u : UnitSphere | ‖c.radius • (u : Space) - c.point i‖ = 1} = 0 := by
  have hp : -c.point i ≠ 0 := by
    apply norm_pos_iff.1
    rw [norm_neg, c.on_sphere]
    exact hR
  apply measure_mono_null (t := {u : UnitSphere |
    ⟪-c.point i, (u : Space)⟫_ℝ = (1 - 2 * c.radius ^ 2) / (2 * c.radius)}) _
    (sphereMeasure_inner_level hp _)
  intro u hu
  change ‖c.radius • (u : Space) - c.point i‖ = 1 at hu
  have h := norm_sub_sq_real (c.radius • (u : Space)) (c.point i)
  simp only [hu, norm_smul, Real.norm_eq_abs, abs_of_pos hR, u.norm_eq_one, mul_one,
    c.on_sphere i, real_inner_smul_left, real_inner_comm (c.point i) (u : Space)] at h
  change ⟪-c.point i, (u : Space)⟫_ℝ = _
  rw [inner_neg_left, eq_div_iff (by positivity : (2 : ℝ) * c.radius ≠ 0)]
  linarith

theorem unitFaceNormals_ae_strict (hA : c.totalDeficit ≤ 2 / 25) (hR : 0 < c.radius)
    (i : Fin 4) : ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.unitFaceNormals i →
      ‖c.point i + (u : Space)‖ < c.radius ∧
        ∀ j, j ≠ i → ‖c.point i + (u : Space) - c.point j‖ < 1 := by
  have hRa : ∀ᵐ u : UnitSphere ∂sphereMeasure, ‖c.point i + (u : Space)‖ ≠ c.radius := by
    rw [ae_iff]
    simpa only [not_not] using c.sphereMeasure_unitFace_radius_boundary hR i
  have hja : ∀ᵐ u : UnitSphere ∂sphereMeasure,
      ∀ j, j ≠ i → ‖c.point i + (u : Space) - c.point j‖ ≠ 1 := by
    apply Filter.eventually_all.2
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h ↦ False.elim (h hji))
    · have h : ∀ᵐ u : UnitSphere ∂sphereMeasure, ‖c.point i + (u : Space) - c.point j‖ ≠ 1 := by
        rw [ae_iff]
        simpa only [not_not] using c.sphereMeasure_unitFace_neighbor_boundary hA (Ne.symm hji)
      exact h.mono (fun _ hu _ ↦ hu)
  filter_upwards [hRa, hja] with u hRu hju hu
  have hc := (c.mem_clippedOuter_range_iff _).1 hu
  exact ⟨lt_of_le_of_ne hc.1 hRu, fun j hji ↦ lt_of_le_of_ne (hc.2 j) (hju j hji)⟩

theorem radiusFaceNormals_ae_strict (hR : 0 < c.radius) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, u ∈ c.radiusFaceNormals →
      ∀ j, ‖c.radius • (u : Space) - c.point j‖ < 1 := by
  have hja : ∀ᵐ u : UnitSphere ∂sphereMeasure,
      ∀ j, ‖c.radius • (u : Space) - c.point j‖ ≠ 1 := by
    apply Filter.eventually_all.2
    intro j
    rw [ae_iff]
    simpa only [not_not] using c.sphereMeasure_radiusFace_boundary hR j
  filter_upwards [hja] with u hju hu j
  exact lt_of_le_of_ne (((c.mem_clippedOuter_range_iff _).1 hu).2 j) (hju j)

theorem unitFaceNormals_pairwise_disjoint (hA : c.totalDeficit ≤ 2 / 25)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} :
    Pairwise (fun i j ↦ Disjoint (c.unitFaceNormals i) (c.unitFaceNormals j)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro u hi hj
  have he := (c.normalSupport_unitFaceNormals (hne := hne) i hi).symm.trans
    (c.normalSupport_unitFaceNormals (hne := hne) j hj)
  exact hij (c.point_injective_of_small_deficit hA (add_right_cancel he))

theorem radiusFaceNormals_disjoint_unitFaceNormals (hR : 1 / 2 < c.radius)
    {hne : (clippedOuter c.radius (range c.point)).Nonempty} (i : Fin 4) :
    Disjoint c.radiusFaceNormals (c.unitFaceNormals i) := by
  apply Set.disjoint_left.2
  intro u hRu hi
  have he := (c.normalSupport_radiusFaceNormals (hne := hne) hRu).symm.trans
    (c.normalSupport_unitFaceNormals (hne := hne) i hi)
  have hp : c.point i = (c.radius - 1) • (u : Space) := by
    rw [sub_smul, one_smul]
    exact (eq_sub_iff_add_eq.2 he.symm)
  have hn := c.on_sphere i
  rw [hp, norm_smul, Real.norm_eq_abs, u.norm_eq_one, mul_one] at hn
  have hR1 : c.radius < 1 := by nlinarith [c.radius_sq_le (by decide)]
  rw [abs_of_neg (sub_neg.2 hR1)] at hn
  linarith

end BlaschkeLebesgue.BalancedContacts
