module

public import BlaschkeLebesgue.Minkowski

/-!
# Complementarity of intersections of balls of radius at most one

A small ball contains an explicit outward perturbation of every chord. The same
perturbation lies in an intersection of such balls. Testing it against a support
plane and passing to the endpoint proves the unit supporting-ball inequality.
This avoids a normal-cone or boundary-regularity assumption.
-/

public noncomputable section

open Set Metric Filter Topology
open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_convexCombination_sq (x y c : E) (s : ℝ) :
    ‖(1 - s) • x + s • y - c‖ ^ 2 =
      (1 - s) * ‖x - c‖ ^ 2 + s * ‖y - c‖ ^ 2 - s * (1 - s) * ‖y - x‖ ^ 2 := by
  have hid : (1 - s) • x + s • y - c = (1 - s) • (x - c) + s • (y - c) := by module
  have hsub : y - x = (y - c) - (x - c) := by abel
  rw [hid, hsub, norm_add_sq_real, norm_sub_sq_real (y - c) (x - c)]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, inner_smul_right, real_inner_comm (y - c) (x - c)]
  ring

/-- A quadratic outward perturbation of a chord stays inside every ball of radius at most one. -/
theorem smallBall_chord_perturbation {x y c n : E} {r s : ℝ}
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) (hr : r ≤ 1)
    (hs : s ∈ Icc 0 1) (hn : ‖n‖ = 1) :
    (1 - s) • x + s • y + (s * (1 - s) * ‖y - x‖ ^ 2 / 2) • n ∈ closedBall c r := by
  have hx' : ‖x - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖y - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hx'
  let z := (1 - s) • x + s • y
  let D := s * (1 - s) * ‖y - x‖ ^ 2
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hs.1 (sub_nonneg.2 hs.2)) (sq_nonneg _)
  have hsq : ‖z - c‖ ^ 2 + D ≤ r ^ 2 := by
    have hx2 := (sq_le_sq₀ (norm_nonneg _) hr0).2 hx'
    have hy2 := (sq_le_sq₀ (norm_nonneg _) hr0).2 hy'
    have h1 := mul_le_mul_of_nonneg_left hx2 (sub_nonneg.2 hs.2)
    have h2 := mul_le_mul_of_nonneg_left hy2 hs.1
    have he := norm_convexCombination_sq x y c s
    change ‖z - c‖ ^ 2 = (1 - s) * ‖x - c‖ ^ 2 + s * ‖y - c‖ ^ 2 - D at he
    nlinarith only [h1, h2, he]
  have hDr : D ≤ r := by
    have hDsq : D ≤ r ^ 2 := by nlinarith only [hsq, sq_nonneg ‖z - c‖]
    nlinarith only [hDsq, hr, hr0]
  have hnorm : ‖z - c‖ ≤ r - D / 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by linarith only [hDr, hr0])).1
    have hprod := mul_nonneg hD (sub_nonneg.2 hr)
    nlinarith only [hsq, hprod, sq_nonneg D]
  have hid : z + (D / 2) • n - c = (z - c) + (D / 2) • n := by abel
  change z + (D / 2) • n ∈ closedBall c r
  rw [mem_closedBall, dist_eq_norm]
  rw [hid]
  have htri := norm_add_le (z - c) ((D / 2) • n)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ D / 2), hn,
    mul_one] at htri
  linarith only [htri, hnorm]

/-- Every supporting unit ball contains the entire intersection. -/
theorem smallBallIntersection_support_inequality {ι : Type*} {C : ConvexBody E}
    (c : ι → E) (r : ι → ℝ) (hr : ∀ i, r i ≤ 1)
    (hC : (C : Set E) = ⋂ i, closedBall (c i) (r i)) {x y n : E}
    (hx : x ∈ C) (hy : y ∈ C) (hn : ‖n‖ = 1) (hs : ⟪n, x⟫_ℝ = support C n) :
    ‖y - x‖ ^ 2 ≤ 2 * ⟪n, x - y⟫_ℝ := by
  have hxall : ∀ i, x ∈ closedBall (c i) (r i) := by
    apply mem_iInter.1
    rw [← hC]
    exact hx
  have hyall : ∀ i, y ∈ closedBall (c i) (r i) := by
    apply mem_iInter.1
    rw [← hC]
    exact hy
  have hstep (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
      (1 - s) * ‖y - x‖ ^ 2 ≤ 2 * ⟪n, x - y⟫_ℝ := by
    have hz : (1 - s) • x + s • y + (s * (1 - s) * ‖y - x‖ ^ 2 / 2) • n ∈ C := by
      change _ ∈ (C : Set E)
      rw [hC]
      exact mem_iInter.2 fun i => smallBall_chord_perturbation
        (hxall i) (hyall i) (hr i) ⟨hs0.le, hs1⟩ hn
    have h := inner_le_support C n hz
    rw [← hs, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one] at h
    rw [inner_sub_right]
    apply le_of_mul_le_mul_left (a := s) _ hs0
    nlinarith only [h]
  have hcont : Continuous (fun s : ℝ => (1 - s) * ‖y - x‖ ^ 2) := by fun_prop
  have hlim : Tendsto (fun s : ℝ => (1 - s) * ‖y - x‖ ^ 2)
      (𝓝[>] 0) (𝓝 (‖y - x‖ ^ 2)) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 :=
    (continuous_id.continuousWithinAt.tendsto (s := Ioi (0 : ℝ))).eventually_lt_const zero_lt_one
  filter_upwards [self_mem_nhdsWithin, hsmall] with s hs0 hs1
  exact hstep s hs0 hs1.le

theorem smallBallIntersection_opposite_mem {ι : Type*} {C : ConvexBody E}
    (c : ι → E) (r : ι → ℝ) (hr : ∀ i, r i ≤ 1)
    (hC : (C : Set E) = ⋂ i, closedBall (c i) (r i)) {x n : E}
    (hx : x ∈ C) (hn : ‖n‖ = 1) (hs : ⟪n, x⟫_ℝ = support C n) :
    x - n ∈ ballTransform (C : Set E) := by
  intro y hy
  have h := smallBallIntersection_support_inequality c r hr hC hx hy hn hs
  have he : x - n - y = (x - y) - n := by abel
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).1
  rw [he, norm_sub_sq_real, hn]
  rw [norm_sub_rev] at h
  nlinarith only [h, real_inner_comm n (x - y)]

end BlaschkeLebesgue
