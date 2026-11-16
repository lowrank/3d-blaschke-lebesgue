module

public import BlaschkeLebesgue.RadialVolume

/-!
# Antipodal invariance of spherical integration

The antipodal homeomorphism preserves the spherical measure defined from
Lebesgue volume. This follows directly from the cone formula and invariance
of ambient volume under negation.
-/

public noncomputable section

open MeasureTheory Set Metric Filter
open scoped Pointwise

namespace BlaschkeLebesgue

@[expose] def sphereAntipode : UnitSphere ≃ₜ UnitSphere where
  toFun u := ⟨-(u : Space), by simp only [mem_sphere, dist_zero_right, norm_neg, u.norm_eq_one]⟩
  invFun u := ⟨-(u : Space), by simp only [mem_sphere, dist_zero_right, norm_neg, u.norm_eq_one]⟩
  left_inv u := by apply Subtype.ext; exact neg_neg (u : Space)
  right_inv u := by apply Subtype.ext; exact neg_neg (u : Space)
  continuous_toFun := (continuous_subtype_val.neg).subtype_mk
    (fun u => by simp only [Pi.neg_apply, mem_sphere, dist_zero_right, norm_neg, UnitSphere.norm_eq_one u])
  continuous_invFun := (continuous_subtype_val.neg).subtype_mk
    (fun u => by simp only [Pi.neg_apply, mem_sphere, dist_zero_right, norm_neg, UnitSphere.norm_eq_one u])

theorem sphereAntipode_val (u : UnitSphere) : (sphereAntipode u : Space) = -(u : Space) := rfl

theorem sphereAntipode_involutive (u : UnitSphere) : sphereAntipode (sphereAntipode u) = u := by
  apply Subtype.ext
  exact neg_neg (u : Space)

theorem cone_antipode_preimage (s : Set UnitSphere) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereAntipode ⁻¹' s)) =
      Neg.neg ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨r, hr, (sphereAntipode u : Space), ⟨sphereAntipode u, hu, rfl⟩,
      by simp only [sphereAntipode_val, smul_neg]⟩
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, he⟩
    refine ⟨r, hr, (sphereAntipode u : Space),
      ⟨sphereAntipode u, ?_, rfl⟩, ?_⟩
    · change sphereAntipode (sphereAntipode u) ∈ s
      rw [sphereAntipode_involutive]
      exact hu
    · simpa only [sphereAntipode_val, smul_neg, neg_neg] using congrArg Neg.neg he

theorem sphereAntipode_measurePreserving : MeasurePreserving sphereAntipode sphereMeasure sphereMeasure := by
  refine ⟨sphereAntipode.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply sphereAntipode.measurable hs, sphereMeasure,
    Measure.toSphere_apply' _ (hs.preimage sphereAntipode.measurable),
    Measure.toSphere_apply' _ hs, cone_antipode_preimage]
  have hn := (volume : Measure Space).measurePreserving_neg
  have he := (LinearIsometryEquiv.neg ℝ (E := Space)).toHomeomorph.measurableEmbedding.map_apply
    (μ := (volume : Measure Space)) (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  change (volume.map Neg.neg) _ = volume (Neg.neg ⁻¹' _) at he
  rw [hn.map_eq] at he
  rw [← he]

theorem integral_sphereAntipode (f : UnitSphere → ℝ) :
    (∫ u : UnitSphere, f (sphereAntipode u) ∂sphereMeasure) = ∫ u : UnitSphere, f u ∂sphereMeasure :=
  sphereAntipode_measurePreserving.integral_comp sphereAntipode.measurableEmbedding f

theorem integrable_sphereAntipode {f : UnitSphere → ℝ} (hf : Integrable f sphereMeasure) :
    Integrable (fun u => f (sphereAntipode u)) sphereMeasure :=
  (sphereAntipode_measurePreserving.integrable_comp hf.aestronglyMeasurable).2 hf

theorem integral_antipodal_pair (f : UnitSphere → ℝ) (hf : Integrable f sphereMeasure) :
    (∫ u : UnitSphere, f u + f (sphereAntipode u) ∂sphereMeasure) =
      2 * (∫ u : UnitSphere, f u ∂sphereMeasure) := by
  rw [integral_add hf (integrable_sphereAntipode hf), integral_sphereAntipode]
  ring

end BlaschkeLebesgue
