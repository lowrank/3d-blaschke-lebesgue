module

public import BlaschkeLebesgue.CompactHull

/-!
# Minimum enclosing balls

The enclosing radius is the maximum of the actual distances to the body. Compactness
and finite dimensionality give a minimizing center; no existence or balancing
condition is included in the definition of a convex body.
-/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radius of the smallest ball with a specified center containing the body. -/
@[expose] def enclosingRadius (K : ConvexBody E) (c : E) : ℝ :=
  sSup ((fun x ↦ ‖x - c‖) '' (K : Set E))

theorem exists_farthest_point (K : ConvexBody E) (c : E) :
    ∃ x ∈ K, enclosingRadius K c = ‖x - c‖ ∧ ∀ y ∈ K, ‖y - c‖ ≤ ‖x - c‖ :=
  K.isCompact.exists_sSup_image_eq_and_ge K.nonempty (by fun_prop)

theorem norm_sub_le_enclosingRadius (K : ConvexBody E) (c : E) {x : E} (hx : x ∈ K) :
    ‖x - c‖ ≤ enclosingRadius K c := by
  obtain ⟨y, _, hy, hmax⟩ := exists_farthest_point K c
  rw [hy]
  exact hmax x hx

theorem enclosingRadius_nonneg (K : ConvexBody E) (c : E) :
    0 ≤ enclosingRadius K c := by
  obtain ⟨x, hx⟩ := K.nonempty
  exact (norm_nonneg _).trans (norm_sub_le_enclosingRadius K c hx)

theorem enclosingRadius_le_iff (K : ConvexBody E) (c : E) (r : ℝ) :
    enclosingRadius K c ≤ r ↔ ∀ x ∈ K, ‖x - c‖ ≤ r := by
  constructor
  · intro h x hx
    exact (norm_sub_le_enclosingRadius K c hx).trans h
  · intro h
    obtain ⟨x, hx, hmax, _⟩ := exists_farthest_point K c
    rw [hmax]
    exact h x hx

theorem enclosingRadius_lt_iff (K : ConvexBody E) (c : E) (r : ℝ) :
    enclosingRadius K c < r ↔ ∀ x ∈ K, ‖x - c‖ < r :=
  K.isCompact.sSup_lt_iff_of_continuous K.nonempty (by fun_prop) r

theorem continuous_enclosingRadius (K : ConvexBody E) : Continuous (enclosingRadius K) :=
  K.isCompact.continuous_sSup (by fun_prop)

/-- A minimum enclosing ball, with minimality relative to every possible center. -/
structure MinimumEnclosingBall (K : ConvexBody E) where
  center : E
  radius : ℝ
  radius_eq : radius = enclosingRadius K center
  minimal : ∀ c : E, radius ≤ enclosingRadius K c

theorem exists_minimumEnclosingBall [FiniteDimensional ℝ E] (K : ConvexBody E) :
    Nonempty (MinimumEnclosingBall K) := by
  obtain ⟨x₀, hx₀⟩ := K.nonempty
  let r₀ := enclosingRadius K x₀
  have hr₀ : 0 ≤ r₀ := enclosingRadius_nonneg K x₀
  obtain ⟨c, _, hc⟩ := (isCompact_closedBall x₀ r₀).exists_isMinOn
    ⟨x₀, by simpa using hr₀⟩ (continuous_enclosingRadius K).continuousOn
  refine ⟨⟨c, enclosingRadius K c, rfl, fun d ↦ ?_⟩⟩
  by_cases hd : d ∈ Metric.closedBall x₀ r₀
  · exact hc hd
  · have hcd : enclosingRadius K c ≤ r₀ := hc (by simpa using hr₀)
    have hd' : r₀ < ‖x₀ - d‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] using hd
    exact hcd.trans (hd'.le.trans (norm_sub_le_enclosingRadius K d hx₀))

namespace MinimumEnclosingBall

variable {K : ConvexBody E} (b : MinimumEnclosingBall K)

theorem radius_nonneg : 0 ≤ b.radius := b.radius_eq ▸ enclosingRadius_nonneg K b.center

theorem norm_sub_center_le {x : E} (hx : x ∈ K) : ‖x - b.center‖ ≤ b.radius := by
  rw [b.radius_eq]
  exact norm_sub_le_enclosingRadius K b.center hx

/-- The contact set is defined by equality in the enclosing-ball constraint. -/
@[expose] def contacts : Set E := {x | x ∈ K ∧ ‖x - b.center‖ = b.radius}

theorem contacts_nonempty : b.contacts.Nonempty := by
  obtain ⟨x, hx, hmax, _⟩ := exists_farthest_point K b.center
  exact ⟨x, hx, (b.radius_eq.trans hmax).symm⟩

theorem contacts_isCompact : IsCompact b.contacts :=
  K.isCompact.inter_right (isClosed_eq (by fun_prop) continuous_const)

/-- A direction cannot have a uniformly positive inner product with all contact
vectors: a small movement in that direction would decrease the enclosing radius. -/
theorem no_positive_contact_direction (v : E) {a : ℝ} (ha : 0 < a)
    (hsep : ∀ x ∈ b.contacts, a ≤ ⟪v, x - b.center⟫_ℝ) : False := by
  obtain ⟨x₀, hx₀⟩ := b.contacts_nonempty
  have hv : 0 < ‖v‖ := by
    by_contra! h
    have : v = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg v))
    have hh := hsep x₀ hx₀
    simp [this] at hh
    linarith
  have hR : 0 < b.radius := by
    have hxpos : 0 < ‖x₀ - b.center‖ := by
      apply norm_pos_iff.mpr
      intro hx
      have hh := hsep x₀ hx₀
      rw [hx, inner_zero_right] at hh
      linarith
    exact hx₀.2 ▸ hxpos
  let S : Set E := {x | x ∈ K ∧ ⟪v, x - b.center⟫_ℝ ≤ a / 2}
  have hS : IsCompact S := K.isCompact.inter_right
    (isClosed_le (show Continuous (fun x ↦ ⟪v, x - b.center⟫_ℝ) by fun_prop)
      continuous_const)
  obtain ⟨r, hr, hbound⟩ : ∃ r < b.radius, ∀ x ∈ S, ‖x - b.center‖ ≤ r := by
    by_cases hne : S.Nonempty
    · obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne
        (show ContinuousOn (fun x ↦ ‖x - b.center‖) S by fun_prop)
      refine ⟨‖x - b.center‖, ?_, fun y hy ↦ hmax hy⟩
      have hle := b.norm_sub_center_le hx.1
      apply lt_of_le_of_ne hle
      intro heq
      have hh := hsep x ⟨hx.1, heq⟩
      have hh' := hx.2
      linarith
    · exact ⟨0, hR, fun x hx ↦ (hne ⟨x, hx⟩).elim⟩
  have hsmall : 0 < min (a / ‖v‖ ^ 2) ((b.radius - r) / ‖v‖) :=
    lt_min (div_pos ha (sq_pos_of_pos hv)) (div_pos (sub_pos.mpr hr) hv)
  obtain ⟨t, ht, htmin⟩ := exists_between hsmall
  have ht₁ : t * ‖v‖ ^ 2 < a :=
    (lt_div_iff₀ (sq_pos_of_pos hv)).1 (lt_min_iff.1 htmin).1
  have ht₂ : t * ‖v‖ < b.radius - r :=
    (lt_div_iff₀ hv).1 (lt_min_iff.1 htmin).2
  have hdecrease : enclosingRadius K (b.center + t • v) < b.radius := by
    apply (enclosingRadius_lt_iff _ _ _).2
    intro x hx
    have hsub : x - (b.center + t • v) = (x - b.center) - t • v := by abel
    rw [hsub]
    by_cases hbad : ⟪v, x - b.center⟫_ℝ ≤ a / 2
    · calc
        ‖(x - b.center) - t • v‖ ≤ ‖x - b.center‖ + ‖t • v‖ := norm_sub_le _ _
        _ = ‖x - b.center‖ + t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        _ < b.radius := by linarith [hbound x ⟨hx, hbad⟩]
    · have hsq := (sq_le_sq₀ (norm_nonneg _) b.radius_nonneg).2 (b.norm_sub_center_le hx)
      have hexpand := norm_sub_sq_real (x - b.center) (t • v)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, real_inner_smul_right,
        real_inner_comm v (x - b.center)] at hexpand
      have hstrict : ‖(x - b.center) - t • v‖ ^ 2 < b.radius ^ 2 := by
        nlinarith [mul_pos ht (show 0 < 2 * ⟪v, x - b.center⟫_ℝ - t * ‖v‖ ^ 2 by
          linarith)]
      exact (sq_lt_sq₀ (norm_nonneg _) b.radius_nonneg).1 hstrict
  exact (not_lt_of_ge (b.minimal _)) hdecrease

/-- The center lies in the convex hull of the actual contacts. -/
theorem center_mem_convexHull_contacts [FiniteDimensional ℝ E] :
    b.center ∈ convexHull ℝ b.contacts := by
  by_contra hnot
  have hcompact := isCompact_convexHull b.contacts_isCompact
  have hne : (convexHull ℝ b.contacts).Nonempty :=
    b.contacts_nonempty.mono (subset_convexHull ℝ _)
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcompact.isComplete
    (convex_convexHull ℝ b.contacts) b.center
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero
    (convex_convexHull ℝ b.contacts) hy).1 hmin
  have hv : y - b.center ≠ 0 := by
    intro h
    exact hnot (sub_eq_zero.mp h ▸ hy)
  apply b.no_positive_contact_direction (y - b.center) (sq_pos_of_ne_zero (norm_ne_zero_iff.2 hv))
  intro x hx
  have hp := hproj x (subset_convexHull ℝ b.contacts hx)
  have hid : ⟪b.center - y, x - y⟫_ℝ =
      ‖y - b.center‖ ^ 2 - ⟪y - b.center, x - b.center⟫_ℝ := by
    have h₁ : b.center - y = -(y - b.center) := by abel
    have h₂ : x - y = (x - b.center) - (y - b.center) := by abel
    rw [h₁, h₂, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  linarith

end MinimumEnclosingBall

end BlaschkeLebesgue
