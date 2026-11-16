module

public import BlaschkeLebesgue.SupportVolumeFormula

/-!
# Interior and strict supporting inequalities

An interior point lies strictly below every supporting plane. Conversely, a
uniform positive support margin contains a ball about the point. These facts
will characterize the two boundary components of a shell.
-/

public noncomputable section

open Metric Set Filter
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem inner_lt_support_of_mem_interior (K : ConvexBody Space) {x u : Space}
    (hx : x ∈ interior (K : Set Space)) (hu : ‖u‖ = 1) : ⟪u, x⟫_ℝ < support K u := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hy : x + (r / 2) • u ∈ K := hb (by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (half_pos hr), hu, mul_one]
    linarith only [hr])
  have hi := inner_le_support K u hy
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one] at hi
  linarith only [hi, hr]

theorem mem_interior_of_support_margin (K : ConvexBody Space) {x : Space} {r : ℝ}
    (hr : 0 < r) (h : ∀ u : Space, ‖u‖ = 1 → ⟪u, x⟫_ℝ + r ≤ support K u) :
    x ∈ interior (K : Set Space) := by
  rw [mem_interior_iff_mem_nhds]
  apply mem_of_superset (ball_mem_nhds x hr)
  intro y hy
  apply (mem_iff_unit_inner_le_support K y).2
  intro u hu
  have hn : ‖y - x‖ < r := hy
  have hc := real_inner_le_norm u (y - x)
  rw [hu, one_mul, inner_sub_right] at hc
  linarith only [h u hu, hn, hc]

theorem support_mono_of_subset {D K : ConvexBody Space}
    (hDK : (D : Set Space) ⊆ (K : Set Space)) (u : Space) : support D u ≤ support K u := by
  apply (support_le_iff D u _).2
  intro x hx
  exact inner_le_support K u (hDK hx)

end BlaschkeLebesgue
