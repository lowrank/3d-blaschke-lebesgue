module

public import BlaschkeLebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The geometric statement to be proved

`ConstantWidthVolumeBound` is a proposition defining the requested target. It is not
a theorem asserting that target. Its volume is the ordinary Lebesgue measure on
three-dimensional Euclidean space.
-/

public noncomputable section

namespace BlaschkeLebesgue

open MeasureTheory
open scoped Pointwise

/-- The real-valued Lebesgue volume of the underlying compact set. -/
@[expose] def bodyVolume (K : ConvexBody Space) : ℝ :=
  (MeasureTheory.volume (K : Set Space)).toReal

/-- The manuscript's main statement, including its nonempty-interior hypothesis.
This is the formal target; no proof of this proposition is supplied by this definition. -/
@[expose] def ConstantWidthVolumeBound : Prop :=
  ∀ (K : ConvexBody Space), (interior (K : Set Space)).Nonempty →
    ∀ (w : ℝ), 0 < w → HasConstantWidth K w → (259 / 625 : ℝ) * w ^ 3 < bodyVolume K

/-- The normalized target, still an unproved proposition. -/
@[expose] def UnitWidthVolumeBound : Prop :=
  ∀ (K : ConvexBody Space), (interior (K : Set Space)).Nonempty →
    HasConstantWidth K 1 → (259 / 625 : ℝ) < bodyVolume K

/-- Dilation multiplies ordinary three-dimensional Lebesgue volume by the cube. -/
theorem bodyVolume_smul (K : ConvexBody Space) {a : ℝ} (ha : 0 ≤ a) :
    bodyVolume (a • K) = a ^ 3 * bodyVolume K := by
  change (volume (a • (K : Set Space))).toReal = _
  rw [Measure.addHaar_smul_of_nonneg volume ha, ENNReal.toReal_mul]
  simp [Space, bodyVolume, ENNReal.toReal_ofReal (pow_nonneg ha _)]

/-- The normalization and rescaling reduction. This does not assert either target. -/
theorem unitWidthVolumeBound_iff : UnitWidthVolumeBound ↔ ConstantWidthVolumeBound := by
  constructor
  · intro h K hK w hw hwidth
    let L : ConvexBody Space := w⁻¹ • K
    have hL : (interior (L : Set Space)).Nonempty := by
      change (interior (w⁻¹ • (K : Set Space))).Nonempty
      rw [interior_smul₀ (inv_ne_zero hw.ne')]
      exact hK.smul_set
    have hwL : HasConstantWidth L 1 := by
      simpa [L, hw.ne'] using hwidth.smul (inv_nonneg.mpr hw.le)
    have hbound := h L hL hwL
    change (259 / 625 : ℝ) < bodyVolume (w⁻¹ • K) at hbound
    rw [bodyVolume_smul K (inv_nonneg.mpr hw.le)] at hbound
    calc
      (259 / 625 : ℝ) * w ^ 3 = w ^ 3 * (259 / 625 : ℝ) := by ring
      _ < w ^ 3 * (w⁻¹ ^ 3 * bodyVolume K) :=
        mul_lt_mul_of_pos_left hbound (pow_pos hw _)
      _ = bodyVolume K := by field_simp
  · intro h K hK hwidth
    simpa using h K hK 1 (by norm_num) hwidth

end BlaschkeLebesgue
