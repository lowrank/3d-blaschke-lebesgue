module

public import BlaschkeLebesgue.CapLensSlices

/-! # Coordinate-free latitude integration for two-cap lenses -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

/-- Two explicit reflections put any pair of unit axes in the latitude coordinate plane. -/
theorem exists_isometry_cap_axes {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ e : Space ≃ₗᵢ[ℝ] Space,
      e u = coordinatePole ∧ e v = latitudeCapAxis ⟪u, v⟫_ℝ := by
  let e₁ : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ (u - coordinatePole))ᗮ.reflection
  have he₁ : e₁ u = coordinatePole := Submodule.reflection_sub (hu.trans norm_coordinatePole.symm)
  have hc : ⟪u, v⟫_ℝ ∈ Icc (-1 : ℝ) 1 := by
    simpa only [hu, hv, mul_one, mem_Icc] using abs_le.1 (abs_real_inner_le_norm u v)
  let w := latitudeCapAxis ⟪u, v⟫_ℝ
  have hw : ‖w‖ = 1 := norm_latitudeCapAxis hc
  let e₂ : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ (e₁ v - w))ᗮ.reflection
  have he₂ : e₂ (e₁ v) = w :=
    Submodule.reflection_sub (by rw [e₁.norm_map, hv, hw])
  have hfix : e₂ coordinatePole = coordinatePole := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right]
    have h₁ : ⟪coordinatePole, e₁ v⟫_ℝ = ⟪u, v⟫_ℝ := by
      rw [← he₁, e₁.inner_map_map]
    have h₂ : ⟪coordinatePole, w⟫_ℝ = ⟪u, v⟫_ℝ := by
      rw [inner_coordinatePole]
      rfl
    rw [h₁, h₂, sub_self]
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · change e₂ (e₁ u) = coordinatePole
    rw [he₁, hfix]
  · exact he₂

theorem integral_cap_inter_sphereIsometry (e : Space ≃ₗᵢ[ℝ] Space) (u v : Space) (a b : ℝ)
    (f : UnitSphere → ℝ) :
    (∫ n in sphereCap u a ∩ sphereCap v b, f (sphereIsometry e n) ∂sphereMeasure) =
      ∫ n in sphereCap (e u) a ∩ sphereCap (e v) b, f n ∂sphereMeasure := by
  have h := (sphereIsometry_measurePreserving e).setIntegral_preimage_emb
    (sphereIsometry e).measurableEmbedding f (sphereCap (e u) a ∩ sphereCap (e v) b)
  rwa [preimage_inter, sphereIsometry_preimage_cap, sphereIsometry_preimage_cap] at h

/-- The weighted latitude formula for any two nonparallel unit cap axes. -/
theorem integral_sphereCap_inter_height {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {a : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (hc : ⟪u, v⟫_ℝ ∈ Ioo (-1 : ℝ) 1)
    (b : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ n in sphereCap u a ∩ sphereCap v b, g ⟪u, (n : Space)⟫_ℝ ∂sphereMeasure) =
      ∫ z in Icc a 1, 2 * Real.arccos (latitudeCapThreshold b ⟪u, v⟫_ℝ z) * g z := by
  obtain ⟨e, heu, hev⟩ := exists_isometry_cap_axes hu hv
  have h := integral_cap_inter_sphereIsometry e u v a b
    (fun n ↦ g ⟪coordinatePole, (n : Space)⟫_ℝ)
  have he (n : UnitSphere) : ⟪coordinatePole, (sphereIsometry e n : Space)⟫_ℝ =
      ⟪u, (n : Space)⟫_ℝ := by
    rw [sphereIsometry_val, ← heu, e.inner_map_map]
  simp_rw [he] at h
  rw [heu, hev, integral_capLens_height ha hc b hg] at h
  exact h

theorem sphereMeasure_real_cap_inter {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {a : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (hc : ⟪u, v⟫_ℝ ∈ Ioo (-1 : ℝ) 1) (b : ℝ) :
    sphereMeasure.real (sphereCap u a ∩ sphereCap v b) =
      ∫ z in Icc a 1, 2 * Real.arccos (latitudeCapThreshold b ⟪u, v⟫_ℝ z) := by
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using
    integral_sphereCap_inter_height hu hv ha hc b (g := fun _ ↦ 1) continuous_const

theorem integral_sphereCap_inter_inner_axis {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {a : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (hc : ⟪u, v⟫_ℝ ∈ Ioo (-1 : ℝ) 1) (b : ℝ) :
    (∫ n in sphereCap u a ∩ sphereCap v b, ⟪u, (n : Space)⟫_ℝ ∂sphereMeasure) =
      ∫ z in Icc a 1, 2 * Real.arccos (latitudeCapThreshold b ⟪u, v⟫_ℝ z) * z :=
  integral_sphereCap_inter_height hu hv ha hc b continuous_id

end BlaschkeLebesgue
