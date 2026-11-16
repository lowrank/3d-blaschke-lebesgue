module

public import BlaschkeLebesgue.ClippedFaceCaps
public import Mathlib.Analysis.Convex.Extrema

/-!
# Support maxima after deleting inactive ball constraints

Strict constraints hold in a neighborhood of the support point. Deleting them
therefore preserves a local maximum of the supporting linear functional.
Convexity promotes that local maximum to a global maximum on the remaining
ball intersection.
-/

public noncomputable section

open Set Metric Filter Topology
open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem isMaxOn_inner_of_eventually_mem {K S : Set E} {x u : E}
    (hS : Convex ℝ S) (hx : x ∈ S)
    (hmax : IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) K x)
    (hnear : ∀ᶠ y in 𝓝 x, y ∈ S → y ∈ K) :
    IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) S x := by
  apply IsMaxOn.of_isLocalMaxOn_of_concaveOn hx
    (h_conc := (innerSL ℝ u).toLinearMap.concaveOn hS)
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with y hy hyS
  exact hmax (hy hyS)

theorem isMaxOn_active_ball_intersection {ι : Type*} [Finite ι]
    (p : ι → E) (r : ι → ℝ) (s : Set ι) {x u : E}
    (hx : ∀ i, ‖x - p i‖ ≤ r i)
    (hmax : IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (⋂ i, closedBall (p i) (r i)) x)
    (hstrict : ∀ i, i ∉ s → ‖x - p i‖ < r i) :
    IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (⋂ i ∈ s, closedBall (p i) (r i)) x := by
  apply isMaxOn_inner_of_eventually_mem
    (convex_iInter fun i ↦ convex_iInter fun _ ↦ convex_closedBall (p i) (r i))
    (by simpa only [mem_iInter, mem_closedBall, dist_eq_norm] using fun i _ ↦ hx i) hmax
  have he : ∀ i, ∀ᶠ y in 𝓝 x, i ∉ s → ‖y - p i‖ < r i := by
    intro i
    by_cases hi : i ∈ s
    · exact Eventually.of_forall fun _ h ↦ (h hi).elim
    · filter_upwards [((continuous_id.sub continuous_const).norm.continuousAt
        : ContinuousAt (fun y : E ↦ ‖y - p i‖) x).eventually_lt_const (hstrict i hi)]
        with y hy
      exact fun _ ↦ hy
  filter_upwards [eventually_all.2 he] with y hy hyS
  simp only [mem_iInter, mem_closedBall, dist_eq_norm] at hyS ⊢
  intro i
  by_cases hi : i ∈ s
  · exact hyS i hi
  · exact (hy i hi).le

theorem eq_ball_face_of_isMaxOn {p x u : E} {r : ℝ} (hu : ‖u‖ = 1)
    (hx : ‖x - p‖ ≤ r)
    (hmax : IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ) (closedBall p r) x) :
    x = p + r • u := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hx
  have hface : p + r • u ∈ closedBall p r := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hu, mul_one, le_refl]
  have hlo := hmax hface
  change ⟪u, p + r • u⟫_ℝ ≤ ⟪u, x⟫_ℝ at hlo
  have hhi := real_inner_le_norm u (x - p)
  rw [hu, one_mul] at hhi
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hu, one_pow, mul_one] at hlo
  have hi : ⟪u, x - p⟫_ℝ = r := by rw [inner_sub_right] at hhi ⊢; linarith
  have hn : ‖x - p‖ = r := le_antisymm hx (by linarith)
  have he := inner_eq_norm_mul_iff_real.1
    (show ⟪u, x - p⟫_ℝ = ‖u‖ * ‖x - p‖ by rw [hi, hn, hu, one_mul])
  rw [hn, hu, one_smul] at he
  rw [← sub_add_cancel x p, ← he]
  abel

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)

@[expose] def clippedBallCenter : Option (Fin 4) → Space
  | none => 0
  | some i => c.point i

@[expose] def clippedBallRadius : Option (Fin 4) → ℝ
  | none => c.radius
  | some _ => 1

theorem clippedOuter_eq_five_balls :
    clippedOuter c.radius (range c.point) =
      ⋂ i, closedBall (c.clippedBallCenter i) (c.clippedBallRadius i) := by
  ext x
  rw [c.mem_clippedOuter_range_iff]
  simp only [mem_iInter, Option.forall, clippedBallCenter, clippedBallRadius,
    mem_closedBall, dist_eq_norm, sub_zero]

theorem normalSupport_clipped_maxOn_active
    {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    (u : Space) (s : Set (Option (Fin 4)))
    (hstrict : ∀ i, i ∉ s →
      ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) u -
        c.clippedBallCenter i‖ < c.clippedBallRadius i) :
    IsMaxOn (fun y ↦ ⟪u, y⟫_ℝ)
      (⋂ i ∈ s, closedBall (c.clippedBallCenter i) (c.clippedBallRadius i))
      (normalSupport (clippedOuterBody c.radius (range c.point) hne) u) := by
  have hx := normalSupport_mem (clippedOuterBody c.radius (range c.point) hne) u
  change normalSupport (clippedOuterBody c.radius (range c.point) hne) u ∈
    clippedOuter c.radius (range c.point) at hx
  rw [c.clippedOuter_eq_five_balls] at hx
  apply isMaxOn_active_ball_intersection c.clippedBallCenter c.clippedBallRadius s
    (by simpa only [mem_iInter, mem_closedBall, dist_eq_norm] using hx) _ hstrict
  intro y hy
  rw [← c.clippedOuter_eq_five_balls] at hy
  change ⟪u, y⟫_ℝ ≤ ⟪u, normalSupport (clippedOuterBody c.radius (range c.point) hne) u⟫_ℝ
  rw [inner_normalSupport]
  exact inner_le_support _ u hy

end BalancedContacts
end BlaschkeLebesgue
