module

public import BlaschkeLebesgue.ProjectiveIntegrability

/-! # Integrating the four sign choices over a symmetric rectangle -/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue

@[expose] def rectangleSignEquiv (sx sy : Bool) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (if sx then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ).prodCongr
    (if sy then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ)

theorem rectangleSignEquiv_apply (sx sy : Bool) (p : ℝ × ℝ) :
    rectangleSignEquiv sx sy p = (if sx then -p.1 else p.1, if sy then -p.2 else p.2) := by
  cases sx <;> cases sy <;> rfl

theorem rectangleSignEquiv_measurePreserving (sx sy : Bool) :
    MeasurePreserving (rectangleSignEquiv sx sy) volume volume := by
  have hn := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hi := MeasurePreserving.id (volume : Measure ℝ)
  cases sx <;> cases sy
  · exact hi.prod hi
  · exact hi.prod hn
  · exact hn.prod hi
  · exact hn.prod hn

theorem rectangleSignEquiv_preimage (sx sy : Bool) (T : ℝ) :
    rectangleSignEquiv sx sy ⁻¹' {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T} =
      {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T} := by
  ext p
  simp only [mem_preimage, mem_ofPred_eq, rectangleSignEquiv_apply]
  cases sx <;> cases sy <;> simp

theorem integral_rectangle_sign (H : ℝ × ℝ → ℝ) (T : ℝ) (sx sy : Bool) :
    (∫ p in {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}, H (rectangleSignEquiv sx sy p)) =
      ∫ p in {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}, H p := by
  have h := (rectangleSignEquiv_measurePreserving sx sy).setIntegral_preimage_emb
    (rectangleSignEquiv sx sy).measurableEmbedding H {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}
  rwa [rectangleSignEquiv_preimage] at h

theorem integrableOn_rectangle_sign {H : ℝ × ℝ → ℝ} {T : ℝ}
    (hH : IntegrableOn H {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}) (sx sy : Bool) :
    IntegrableOn (fun p ↦ H (rectangleSignEquiv sx sy p)) {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T} := by
  have h := ((rectangleSignEquiv_measurePreserving sx sy).integrableOn_comp_preimage
    (rectangleSignEquiv sx sy).measurableEmbedding).2 hH
  rwa [rectangleSignEquiv_preimage] at h

theorem integral_rectangle_four_sign {H : ℝ × ℝ → ℝ} {T : ℝ}
    (hH : IntegrableOn H {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}) :
    (∫ p in {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T},
      H p + H (-p.1, -p.2) + H (p.1, -p.2) + H (-p.1, p.2)) =
      4 * ∫ p in {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}, H p := by
  have hnn : IntegrableOn (fun p : ℝ × ℝ ↦ H (-p.1, -p.2)) {p | |p.1| < T ∧ |p.2| < T} :=
    integrableOn_rectangle_sign hH true true
  have hpn : IntegrableOn (fun p : ℝ × ℝ ↦ H (p.1, -p.2)) {p | |p.1| < T ∧ |p.2| < T} :=
    integrableOn_rectangle_sign hH false true
  have hnp : IntegrableOn (fun p : ℝ × ℝ ↦ H (-p.1, p.2)) {p | |p.1| < T ∧ |p.2| < T} :=
    integrableOn_rectangle_sign hH true false
  have inn := integral_rectangle_sign H T true true
  have ipn := integral_rectangle_sign H T false true
  have inp := integral_rectangle_sign H T true false
  simp only [rectangleSignEquiv_apply, Bool.false_eq_true, ↓reduceIte] at inn ipn inp
  have he3 := integral_add ((hH.add hnn).add hpn) hnp
  have he2 := integral_add (hH.add hnn) hpn
  have he1 := integral_add hH hnn
  simp only [Pi.add_apply] at he3 he2 he1
  rw [he3, he2, he1, inn, ipn, inp]
  ring

theorem integral_rectangle_le_of_four_sign {H G : ℝ × ℝ → ℝ} {T : ℝ}
    (hH : IntegrableOn H {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T})
    (hG : IntegrableOn G {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T})
    (hpoint : ∀ p : ℝ × ℝ, |p.1| < T → |p.2| < T →
      4 * H p ≤ G p + G (-p.1, -p.2) + G (p.1, -p.2) + G (-p.1, p.2)) :
    (∫ p in {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}, H p) ≤
      ∫ p in {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T}, G p := by
  have hnn : IntegrableOn (fun p : ℝ × ℝ ↦ G (-p.1, -p.2)) {p | |p.1| < T ∧ |p.2| < T} :=
    integrableOn_rectangle_sign hG true true
  have hpn : IntegrableOn (fun p : ℝ × ℝ ↦ G (p.1, -p.2)) {p | |p.1| < T ∧ |p.2| < T} :=
    integrableOn_rectangle_sign hG false true
  have hnp : IntegrableOn (fun p : ℝ × ℝ ↦ G (-p.1, p.2)) {p | |p.1| < T ∧ |p.2| < T} :=
    integrableOn_rectangle_sign hG true false
  have hs : MeasurableSet {p : ℝ × ℝ | |p.1| < T ∧ |p.2| < T} :=
    ((isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)).measurableSet
  have h := setIntegral_mono_on (hH.const_mul 4) (((hG.add hnn).add hpn).add hnp)
    hs (fun p hp ↦ hpoint p hp.1 hp.2)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_rectangle_four_sign hG] at h
  linarith only [h]

end BlaschkeLebesgue
