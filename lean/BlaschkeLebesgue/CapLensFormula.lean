module

public import BlaschkeLebesgue.CapLensCoordinates
public import BlaschkeLebesgue.LensIntegrals

/-!
# Exact area and axial first moment of a spherical lens

These identities evaluate the actual geometric spherical integrals. The
positive Gram determinant says that the two boundary circles cross in two
points; the distinct-height condition excludes the upper crossing at the pole.
-/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem sphereMeasure_real_cap_inter_formula {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {a b : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : ⟪u, v⟫_ℝ ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ ⟪u, v⟫_ℝ)
    (hD : 0 < lensGram a b ⟪u, v⟫_ℝ) :
    sphereMeasure.real (sphereCap u a ∩ sphereCap v b) = lensAreaExpression a b ⟪u, v⟫_ℝ := by
  rw [sphereMeasure_real_cap_inter hu hv ⟨ha.1.le, ha.2.le⟩ hc,
    integral_lensSlice ha hb hc hbc hD]

theorem integral_sphereCap_inter_inner_formula {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {a b : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1)
    (hc : ⟪u, v⟫_ℝ ∈ Ioo (-1 : ℝ) 1) (hbc : b ≠ ⟪u, v⟫_ℝ)
    (hD : 0 < lensGram a b ⟪u, v⟫_ℝ) :
    (∫ n in sphereCap u a ∩ sphereCap v b, ⟪u, (n : Space)⟫_ℝ ∂sphereMeasure) =
      lensMomentExpression a b ⟪u, v⟫_ℝ := by
  rw [integral_sphereCap_inter_inner_axis hu hv ⟨ha.1.le, ha.2.le⟩ hc,
    integral_lensMomentSlice ha hb hc hbc hD]

end BlaschkeLebesgue
