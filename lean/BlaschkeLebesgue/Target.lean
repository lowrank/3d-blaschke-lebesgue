module

public import BlaschkeLebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The geometric statement to be proved

`ConstantWidthVolumeBound` is a proposition defining the requested target. It is not
a theorem asserting that target. Its volume is the ordinary Lebesgue measure on
three-dimensional Euclidean space.
-/

public noncomputable section

namespace BlaschkeLebesgue

/-- The real-valued Lebesgue volume of the underlying compact set. -/
@[expose] def bodyVolume (K : ConvexBody Space) : ℝ :=
  (MeasureTheory.volume (K : Set Space)).toReal

/-- The manuscript's main statement, including its nonempty-interior hypothesis.
This is the formal target; no proof of this proposition is supplied by this definition. -/
@[expose] def ConstantWidthVolumeBound : Prop :=
  ∀ (K : ConvexBody Space), (interior (K : Set Space)).Nonempty →
    ∀ (w : ℝ), 0 < w → HasConstantWidth K w → (259 / 625 : ℝ) * w ^ 3 < bodyVolume K

end BlaschkeLebesgue
