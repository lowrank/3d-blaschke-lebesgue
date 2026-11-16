module

public import BlaschkeLebesgue.MinkowskiInterpolation

/-!
# Uniqueness in the shell parametrization

A positive increase of the parallel radius separates different interpolation
times. A positive base parallel radius separates different unit normals at the
same time. Both arguments use supporting inequalities and monotonicity.
-/

public noncomputable section

open Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem support_shellBody_strict_mono {D K : ConvexBody Space}
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ s t : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s < t) {u : Space} (hu : ‖u‖ = 1) :
    support (shellBody D K ε δ s) u < support (shellBody D K ε δ t) u := by
  rw [support_shellBody D K hε hδ.le hs hu, support_shellBody D K hε hδ.le ht hu]
  have hp : 0 < support K u - support D u + δ := by
    linarith only [support_mono_of_subset hDK u, hδ]
  linarith only [mul_lt_mul_of_pos_right hst hp]

theorem shellPoint_time_injective {D K : ConvexBody Space}
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ s t : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (he : shellPoint D K ε δ s u = shellPoint D K ε δ t v) : s = t := by
  apply le_antisymm
  · by_contra h
    have hst : t < s := lt_of_not_ge h
    have h := inner_le_support (shellBody D K ε δ t) u (shellPoint_mem D K ε δ t hv)
    rw [← he, inner_shellPoint D K hε hδ.le hs hu] at h
    exact (not_le_of_gt (support_shellBody_strict_mono hDK hε hδ ht hs hst hu)) h
  · by_contra h
    have hst : s < t := lt_of_not_ge h
    have h := inner_le_support (shellBody D K ε δ s) v (shellPoint_mem D K ε δ s hu)
    rw [he, inner_shellPoint D K hε hδ.le ht hv] at h
    exact (not_le_of_gt (support_shellBody_strict_mono hDK hε hδ hs ht hst hv)) h

theorem shellPoint_normal_injective (D K : ConvexBody Space) {ε δ t : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ) (ht : t ∈ Icc (0 : ℝ) 1)
    {u v : Space} (he : shellPoint D K ε δ t u = shellPoint D K ε δ t v) : u = v := by
  have hd := normalSupport_monotone D u v
  have hk := normalSupport_monotone K u v
  have hradius : 0 < ε + t * δ := add_pos_of_pos_of_nonneg hε (mul_nonneg ht.1 hδ)
  have hsub : shellPoint D K ε δ t u - shellPoint D K ε δ t v =
      (1 - t) • (normalSupport D u - normalSupport D v) +
        t • (normalSupport K u - normalSupport K v) + (ε + t * δ) • (u - v) := by
    unfold shellPoint
    module
  have hi : ⟪shellPoint D K ε δ t u - shellPoint D K ε δ t v, u - v⟫_ℝ = 0 := by
    rw [he, sub_self, inner_zero_left]
  rw [hsub, inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hi
  have hn : ‖u - v‖ ^ 2 = 0 := by
    have hm : (ε + t * δ) * ‖u - v‖ ^ 2 ≤ 0 := by
      linarith only [hi, mul_nonneg (sub_nonneg.2 ht.2) hd, mul_nonneg ht.1 hk]
    have hz : ‖u - v‖ ^ 2 ≤ 0 := by
      by_contra h
      exact (not_le_of_gt (mul_pos hradius (lt_of_not_ge h))) hm
    exact le_antisymm hz (sq_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 hn))

theorem shellPoint_injective {D K : ConvexBody Space}
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    InjOn (fun p : ℝ × UnitSphere => shellPoint D K ε δ p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ univ) := by
  rintro ⟨s, u⟩ hs ⟨t, v⟩ ht he
  have hst := shellPoint_time_injective hDK hε.le hδ hs.1 ht.1 u.norm_eq_one v.norm_eq_one he
  change s = t at hst
  subst t
  have huv := shellPoint_normal_injective D K hε hδ.le hs.1 he
  exact Prod.ext rfl (Subtype.ext huv)

end BlaschkeLebesgue
