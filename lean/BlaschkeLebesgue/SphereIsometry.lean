module

public import BlaschkeLebesgue.CapBoundaries

/-! # Orthogonal invariance of actual spherical measure and integration -/

public noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def sphereIsometry (e : Space ≃ₗᵢ[ℝ] Space) : UnitSphere ≃ₜ UnitSphere where
  toFun u := ⟨e (u : Space), by simp only [mem_sphere, dist_zero_right, e.norm_map, u.norm_eq_one]⟩
  invFun u := ⟨e.symm (u : Space), by
    simp only [mem_sphere, dist_zero_right, e.symm.norm_map, u.norm_eq_one]⟩
  left_inv u := by apply Subtype.ext; exact e.symm_apply_apply (u : Space)
  right_inv u := by apply Subtype.ext; exact e.apply_symm_apply (u : Space)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem sphereIsometry_val (e : Space ≃ₗᵢ[ℝ] Space) (u : UnitSphere) :
    (sphereIsometry e u : Space) = e (u : Space) := rfl

theorem cone_sphereIsometry_preimage (e : Space ≃ₗᵢ[ℝ] Space) (s : Set UnitSphere) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereIsometry e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨r, hr, (sphereIsometry e u : Space), ⟨sphereIsometry e u, hu, rfl⟩,
      (e.map_smul r (u : Space)).symm⟩
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, he⟩
    refine ⟨r, hr, ((sphereIsometry e).symm u : Space),
      ⟨(sphereIsometry e).symm u, ?_, rfl⟩, ?_⟩
    · change sphereIsometry e ((sphereIsometry e).symm u) ∈ s
      simpa only [Homeomorph.apply_symm_apply] using hu
    · have h := congrArg e.symm he
      change r • e.symm (u : Space) = x
      simpa only [e.symm.map_smul, e.symm_apply_apply] using h

theorem sphereIsometry_measurePreserving (e : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (sphereIsometry e) sphereMeasure sphereMeasure := by
  refine ⟨(sphereIsometry e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereIsometry e).measurable hs, sphereMeasure,
    Measure.toSphere_apply' _ (hs.preimage (sphereIsometry e).measurable),
    Measure.toSphere_apply' _ hs, cone_sphereIsometry_preimage]
  have he := e.toHomeomorph.measurableEmbedding.map_apply (μ := (volume : Measure Space))
    (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  change (volume.map e) _ = volume (e ⁻¹' _) at he
  rw [e.measurePreserving.map_eq] at he
  rw [← he]

theorem sphereIsometry_preimage_cap (e : Space ≃ₗᵢ[ℝ] Space) (u : Space) (c : ℝ) :
    sphereIsometry e ⁻¹' sphereCap (e u) c = sphereCap u c := by
  ext v
  simp only [mem_preimage, sphereCap, mem_ofPred_eq, sphereIsometry_val, e.inner_map_map]

theorem sphereIsometry_measurePreserving_restrict_cap (e : Space ≃ₗᵢ[ℝ] Space)
    (u : Space) (c : ℝ) :
    MeasurePreserving (sphereIsometry e) (sphereMeasure.restrict (sphereCap u c))
      (sphereMeasure.restrict (sphereCap (e u) c)) := by
  have h := (sphereIsometry_measurePreserving e).restrict_preimage (measurableSet_sphereCap (e u) c)
  rwa [sphereIsometry_preimage_cap] at h

theorem integral_sphereIsometry (e : Space ≃ₗᵢ[ℝ] Space) (f : UnitSphere → ℝ) :
    (∫ u : UnitSphere, f (sphereIsometry e u) ∂sphereMeasure) =
      ∫ u : UnitSphere, f u ∂sphereMeasure :=
  (sphereIsometry_measurePreserving e).integral_comp (sphereIsometry e).measurableEmbedding f

theorem integral_cap_sphereIsometry (e : Space ≃ₗᵢ[ℝ] Space) (u : Space) (c : ℝ)
    (f : UnitSphere → ℝ) :
    (∫ v in sphereCap u c, f (sphereIsometry e v) ∂sphereMeasure) =
      ∫ v in sphereCap (e u) c, f v ∂sphereMeasure := by
  have h := (sphereIsometry_measurePreserving e).setIntegral_preimage_emb
    (sphereIsometry e).measurableEmbedding f (sphereCap (e u) c)
  rw [sphereIsometry_preimage_cap] at h
  exact h

end BlaschkeLebesgue
