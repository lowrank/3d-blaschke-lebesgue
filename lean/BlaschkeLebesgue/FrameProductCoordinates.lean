module

public import BlaschkeLebesgue.ProjectiveAnnulus
public import BlaschkeLebesgue.SliceVolume

/-! # Separating radial and planar integration in the actual orthonormal frame -/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def threeCoordinateEquiv : Space ≃ᵐ ℝ × (ℝ × ℝ) :=
  sliceEquiv.trans ((MeasurableEquiv.refl ℝ).prodCongr
    ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ))))

theorem threeCoordinateEquiv_measurePreserving : MeasurePreserving threeCoordinateEquiv :=
  ((MeasurePreserving.id volume).prod
    ((volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2)))).comp
    sliceEquiv_measurePreserving

theorem threeCoordinateEquiv_apply (p : Space) : threeCoordinateEquiv p = (p 0, (p 1, p 2)) := by
  change ((sliceEquiv p).1, ((sliceEquiv p).2 0, (sliceEquiv p).2 1)) = _
  rw [sliceEquiv_fst, sliceEquiv_snd, sliceEquiv_snd]
  rw [show (0 : Fin 2).succ = (1 : Fin 3) by decide,
    show (1 : Fin 2).succ = (2 : Fin 3) by decide]

namespace ObliqueFrame

variable (f : ObliqueFrame)

theorem exists_volume_coordinates : ∃ e : Space ≃ᵐ ℝ × (ℝ × ℝ), MeasurePreserving e ∧
    ∀ p, e p = (⟪f.normal, p⟫_ℝ, (⟪f.axis₁, p⟫_ℝ, ⟪f.transverse₁, p⟫_ℝ)) := by
  obtain ⟨b, hb0, hb1, hb2⟩ := f.exists_first_basis
  let e := b.repr.toHomeomorph.toMeasurableEquiv.trans threeCoordinateEquiv
  refine ⟨e, ?_, ?_⟩
  · exact threeCoordinateEquiv_measurePreserving.comp b.repr.measurePreserving
  · intro p
    change threeCoordinateEquiv (b.repr p) = _
    rw [threeCoordinateEquiv_apply, b.repr_apply_apply, b.repr_apply_apply, b.repr_apply_apply,
      hb0, hb1, hb2]

theorem integral_frame_product (I : Set ℝ) (s : Set (ℝ × ℝ)) (F : ℝ → ℝ) (G : ℝ × ℝ → ℝ) :
    (∫ p in {p : Space | ⟪f.normal, p⟫_ℝ ∈ I ∧ (⟪f.axis₁, p⟫_ℝ, ⟪f.transverse₁, p⟫_ℝ) ∈ s},
      F ⟪f.normal, p⟫_ℝ * G (⟪f.axis₁, p⟫_ℝ, ⟪f.transverse₁, p⟫_ℝ)) =
      (∫ r in I, F r) * ∫ q in s, G q := by
  obtain ⟨e, he, hcoord⟩ := f.exists_volume_coordinates
  have h := he.setIntegral_preimage_emb e.measurableEmbedding (fun q : ℝ × (ℝ × ℝ) ↦ F q.1 * G q.2) (I ×ˢ s)
  have hpre : e ⁻¹' (I ×ˢ s) =
      {p : Space | ⟪f.normal, p⟫_ℝ ∈ I ∧ (⟪f.axis₁, p⟫_ℝ, ⟪f.transverse₁, p⟫_ℝ) ∈ s} := by
    ext p
    simp only [mem_preimage, hcoord, mem_prod, mem_ofPred_eq]
  rw [hpre] at h
  simp_rw [hcoord] at h
  exact h.trans (setIntegral_prod_mul F G I s)

end ObliqueFrame
end BlaschkeLebesgue
