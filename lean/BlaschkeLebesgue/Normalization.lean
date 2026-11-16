module

public import BlaschkeLebesgue.ContactExistence
public import BlaschkeLebesgue.InnerOuter
public import BlaschkeLebesgue.Translation

/-!
# Width and circumsphere normalization

Every positive-width body has a translated, dilated unit-width representative whose
minimum enclosing center is zero. The transformation preserves the actual geometric
meaning of the volume, and the inner-ball inclusion puts the origin in the interior.
-/

public noncomputable section

namespace BlaschkeLebesgue

theorem MinimumEnclosingBall.centeredBody_zero_mem_interior {K : ConvexBody Space}
    (b : MinimumEnclosingBall K) (hK : HasConstantWidth K 1) :
    (0 : Space) ∈ interior (b.centeredBody : Set Space) := by
  have hR : b.radius < 1 := by nlinarith [b.radius_sq_le hK]
  exact (b.centeredBody_width hK).center_mem_interior hR
    (fun _ hx ↦ b.centeredBody_norm_le hx)

/-- The normalized body and its minimum enclosing ball are constructed from the
original body; the relation between their Lebesgue volumes is proved. -/
theorem exists_centered_unit_body {K : ConvexBody Space} {w : ℝ}
    (hw : 0 < w) (hK : HasConstantWidth K w) :
    ∃ (L : ConvexBody Space) (b : MinimumEnclosingBall L),
      HasConstantWidth L 1 ∧ b.center = 0 ∧ (1 / 2 : ℝ) ≤ b.radius ∧
      b.radius ^ 2 ≤ 3 / 8 ∧ (0 : Space) ∈ interior (L : Set Space) ∧
      bodyVolume L = w⁻¹ ^ 3 * bodyVolume K := by
  let M : ConvexBody Space := w⁻¹ • K
  have hM : HasConstantWidth M 1 := by
    simpa [M, hw.ne'] using hK.smul (inv_nonneg.mpr hw.le)
  obtain ⟨b⟩ := exists_minimumEnclosingBall M
  refine ⟨b.centeredBody, b.centeredBall, b.centeredBody_width hM, rfl,
    b.radius_ge_half hM, b.radius_sq_le hM, b.centeredBody_zero_mem_interior hM, ?_⟩
  rw [MinimumEnclosingBall.centeredBody, bodyVolume_translateBody]
  exact bodyVolume_smul K (inv_nonneg.mpr hw.le)

end BlaschkeLebesgue
