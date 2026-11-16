module

public import BlaschkeLebesgue.ShellCoverage

/-!
# Parametrizing the actual shell by an ordinary Euclidean annulus

The Euclidean radius minus one is interpolation time, and the normalized
direction is the supporting normal. This gives a bijective parametrization
of the shell between the two rounded endpoint bodies.
-/

public noncomputable section

open Set Metric NormedSpace
open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def unitAnnulus : Set Space := closedBall 0 2 \ ball 0 1

theorem mem_unitAnnulus_iff (x : Space) : x ∈ unitAnnulus ↔ 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  simp only [unitAnnulus, mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt]
  exact and_comm

theorem isCompact_unitAnnulus : IsCompact unitAnnulus :=
  (isCompact_closedBall (0 : Space) 2).diff isOpen_ball

theorem unitAnnulus_ne_zero {x : Space} (hx : x ∈ unitAnnulus) : x ≠ 0 := by
  have h := (mem_unitAnnulus_iff x).1 hx
  intro he
  norm_num [he] at h

theorem unitAnnulus_time {x : Space} (hx : x ∈ unitAnnulus) : ‖x‖ - 1 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := (mem_unitAnnulus_iff x).1 hx
  constructor <;> linarith only [h1, h2]

@[expose] def shellMap (D K : ConvexBody Space) (ε δ : ℝ) (x : Space) : Space :=
  shellPoint D K ε δ (‖x‖ - 1) (normalize x)

theorem smul_unit_mem_annulus {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : UnitSphere) :
    (1 + t) • (u : Space) ∈ unitAnnulus := by
  rw [mem_unitAnnulus_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith only [ht.1]),
    u.norm_eq_one, mul_one]
  constructor <;> linarith only [ht.1, ht.2]

theorem shellMap_polar (D K : ConvexBody Space) (ε δ : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : UnitSphere) :
    shellMap D K ε δ ((1 + t) • (u : Space)) = shellPoint D K ε δ t u := by
  have hp : 0 < 1 + t := by linarith only [ht.1]
  rw [shellMap, norm_smul, Real.norm_eq_abs, abs_of_pos hp, u.norm_eq_one, mul_one,
    normalize_smul_of_pos hp, normalize_eq_self_of_norm_eq_one u.norm_eq_one]
  congr 1
  ring

theorem shellMap_image {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) :
    shellMap D K ε δ '' unitAnnulus = bodyShell D K ε δ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact shellPoint_mem_bodyShell hDK hε hδ.le (unitAnnulus_time hy)
      (norm_normalize (unitAnnulus_ne_zero hy))
  · intro hx
    obtain ⟨t, ht, u, he⟩ := exists_shellPoint_eq hD hK hDK hε hδ hx
    exact ⟨(1 + t) • (u : Space), smul_unit_mem_annulus ht u,
      (shellMap_polar D K ε δ ht u).trans he.symm⟩

theorem shellMap_injOn {D K : ConvexBody Space}
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    InjOn (shellMap D K ε δ) unitAnnulus := by
  intro x hx y hy he
  have hx0 := unitAnnulus_ne_zero hx
  have hy0 := unitAnnulus_ne_zero hy
  have htime := shellPoint_time_injective hDK hε.le hδ (unitAnnulus_time hx) (unitAnnulus_time hy)
    (norm_normalize hx0) (norm_normalize hy0) he
  have hn : ‖x‖ = ‖y‖ := by linarith only [htime]
  change shellPoint D K ε δ (‖x‖ - 1) (normalize x) =
    shellPoint D K ε δ (‖y‖ - 1) (normalize y) at he
  rw [← hn] at he
  have hdir := shellPoint_normal_injective D K hε hδ.le (unitAnnulus_time hx) he
  calc
    x = ‖x‖ • normalize x := (norm_smul_normalize x).symm
    _ = ‖y‖ • normalize y := by rw [hn, hdir]
    _ = y := norm_smul_normalize y

theorem parallelBody_subset_of_subset {D K : ConvexBody Space}
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    (parallelBody D a : Set Space) ⊆ (parallelBody K b : Set Space) := by
  intro x hx
  apply (mem_iff_unit_inner_le_support _ x).2
  intro u hu
  have h := inner_le_support (parallelBody D a) u hx
  rw [support_parallelBody D ha hu] at h
  rw [support_parallelBody K hb hu]
  linarith only [h, hab, support_mono_of_subset hDK u]

end BlaschkeLebesgue
