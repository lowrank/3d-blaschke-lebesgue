module

public import BlaschkeLebesgue.Basic

/-! The concentric inner ball and the forced clipped inner/outer approximations. -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem support_le_of_norm_le {K : ConvexBody E} {R : ℝ}
    (hbound : ∀ x ∈ K, ‖x‖ ≤ R) {n : E} (hn : ‖n‖ = 1) : support K n ≤ R := by
  apply (support_le_iff K n R).2
  intro x hx
  have hi := real_inner_le_norm n x
  rw [hn, one_mul] at hi
  exact hi.trans (hbound x hx)

/-- The concentric inner ball in equation (3.3). -/
theorem HasConstantWidth.innerBall_subset {K : ConvexBody E}
    (hK : HasConstantWidth K 1) {R : ℝ} (hbound : ∀ x ∈ K, ‖x‖ ≤ R) :
    Metric.closedBall (0 : E) (1 - R) ⊆ (K : Set E) := by
  intro x hx
  have hnorm : ‖x‖ ≤ 1 - R := by simpa using hx
  apply (mem_iff_unit_inner_le_support K x).2
  intro n hn
  have hw := hK n hn
  have hneg := support_le_of_norm_le hbound (show ‖-n‖ = 1 by simpa using hn)
  have hi := real_inner_le_norm n x
  rw [hn, one_mul] at hi
  linarith

theorem HasConstantWidth.center_mem_interior {K : ConvexBody E}
    (hK : HasConstantWidth K 1) {R : ℝ} (hR : R < 1)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ R) : (0 : E) ∈ interior (K : Set E) := by
  rw [mem_interior_iff_mem_nhds]
  apply Metric.mem_nhds_iff.mpr
  exact ⟨1 - R, sub_pos.mpr hR, Metric.ball_subset_closedBall.trans (hK.innerBall_subset hbound)⟩

/-- The clipped intersection of the circum-ball and the unit balls at the contacts. -/
@[expose] def clippedOuter (R : ℝ) (Y : Set E) : Set E :=
  Metric.closedBall 0 R ∩ ballTransform Y

/-- The forced sandwich `B(C) ⊆ K ⊆ C` for the actual clipped outer set, equation (4.2). -/
theorem HasConstantWidth.clipped_sandwich {K : ConvexBody E}
    (hK : HasConstantWidth K 1) {R : ℝ} {Y : Set E}
    (hY : Y ⊆ (K : Set E)) (hbound : ∀ x ∈ K, ‖x‖ ≤ R) :
    ballTransform (clippedOuter R Y) ⊆ (K : Set E) ∧
      (K : Set E) ⊆ clippedOuter R Y := by
  have hout : (K : Set E) ⊆ clippedOuter R Y := by
    intro x hx
    refine ⟨by simpa using hbound x hx, ?_⟩
    intro y hy
    exact hK.norm_sub_le (by norm_num) hx (hY hy)
  exact ⟨hK.forced_inner hout, hout⟩

end BlaschkeLebesgue
