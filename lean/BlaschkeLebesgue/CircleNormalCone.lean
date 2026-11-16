module

public import BlaschkeLebesgue.ContactCircle

/-! # The normal cone of the intersection circle of two unit balls -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts.Opposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

@[expose] def circleProjection (n : E) : E := n - ⟪firstAxis c, n⟫_ℝ • firstAxis c
@[expose] def circleDirection (n : E) : E := NormedSpace.normalize (circleProjection c n)
@[expose] def circleCandidate (n : E) : E := circlePoint c (circleDirection c n)

theorem circleProjection_inner_axis (ha : edgeBudget c < 1) (n : E) :
    ⟪firstAxis c, circleProjection c n⟫_ℝ = 0 := by
  simp only [circleProjection, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, firstAxis_norm c ha]
  ring

theorem circleProjection_norm_sq (ha : edgeBudget c < 1) {n : E} (hn : ‖n‖ = 1) :
    ‖circleProjection c n‖ ^ 2 = 1 - ⟪firstAxis c, n⟫_ℝ ^ 2 := by
  simp only [circleProjection, norm_sub_sq_real, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, firstAxis_norm c ha, hn, real_inner_smul_right,
    real_inner_comm n (firstAxis c)]
  ring

theorem circleProjection_norm_pos (ha : edgeBudget c < 1) {n : E} (hn : ‖n‖ = 1)
    (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2) :
    0 < ‖circleProjection c n‖ := by
  have hs := firstEdge_norm_sq_le_one c
  have hp := circleProjection_norm_sq c ha hn
  have hc := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hcone
  rw [sq_abs] at hc
  nlinarith [norm_nonneg (circleProjection c n)]

theorem circleDirection_frame (ha : edgeBudget c < 1) {n : E} (hn : ‖n‖ = 1)
    (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2) :
    ‖circleDirection c n‖ = 1 ∧ ⟪firstEdge c, circleDirection c n⟫_ℝ = 0 ∧
      ⟪n, circleDirection c n⟫_ℝ = ‖circleProjection c n‖ := by
  have hp := circleProjection_norm_pos c ha hn hcone
  have hp0 := norm_pos_iff.mp hp
  have hinner : ⟪n, circleProjection c n⟫_ℝ = ‖circleProjection c n‖ ^ 2 := by
    rw [circleProjection_norm_sq c ha hn]
    simp only [circleProjection, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn, real_inner_comm n (firstAxis c)]
    ring
  refine ⟨NormedSpace.norm_normalize hp0, ?_, ?_⟩
  · rw [← NormedSpace.norm_smul_normalize (firstEdge c), real_inner_smul_left]
    change ‖firstEdge c‖ * ⟪firstAxis c, circleDirection c n⟫_ℝ = 0
    simp only [circleDirection, NormedSpace.normalize, real_inner_smul_right,
      circleProjection_inner_axis c ha, mul_zero]
  · simp only [circleDirection, NormedSpace.normalize, real_inner_smul_right, hinner]
    field_simp

/-- A strictly positive complementary-radius bound implies the strict normal
cone condition whenever the projection is nonzero. The nonzero hypothesis is
essential because division in Lean is total at zero. -/
theorem circle_normal_cone_of_positive_complement (ha : edgeBudget c < 1)
    {n : E} (hn : ‖n‖ = 1) (hp : 0 < ‖circleProjection c n‖)
    (hcurv : 0 < 1 - circleRadius c / ‖circleProjection c n‖) :
    |⟪firstAxis c, n⟫_ℝ| < ‖firstEdge c‖ / 2 := by
  have hr := circleRadius_pos c
  have hlt : circleRadius c < ‖circleProjection c n‖ :=
    (div_lt_one hp).1 (by linarith)
  have hsq := (sq_lt_sq₀ hr.le hp.le).2 hlt
  rw [circleRadius_sq, circleProjection_norm_sq c ha hn] at hsq
  apply (sq_lt_sq₀ (abs_nonneg _) (by positivity)).1
  rw [sq_abs]
  nlinarith

/-- On the circle's normal cone the proposed normal is a nonnegative
combination of the two actual unit-sphere normals. -/
theorem circle_normal_cone (ha : edgeBudget c < 1) {n : E} (hn : ‖n‖ = 1)
    (hcone : |⟪firstAxis c, n⟫_ℝ| ≤ ‖firstEdge c‖ / 2) :
    ∃ l₀ l₁ : ℝ, 0 ≤ l₀ ∧ 0 ≤ l₁ ∧
      n = l₀ • (circleCandidate c n - c.point 0) +
        l₁ • (circleCandidate c n - c.point 1) := by
  let a := ⟪firstAxis c, n⟫_ℝ
  let s := ‖firstEdge c‖
  let r := circleRadius c
  let q := ‖circleProjection c n‖
  have hs : 0 < s := norm_pos_iff.mpr (firstEdge_ne_zero c ha)
  have hr : 0 < r := circleRadius_pos c
  have hq : 0 < q := circleProjection_norm_pos c ha hn hcone
  have hr2 : r ^ 2 = 1 - s ^ 2 / 4 := circleRadius_sq c
  have hq2 : q ^ 2 = 1 - a ^ 2 := circleProjection_norm_sq c ha hn
  have ha2 : a ^ 2 ≤ s ^ 2 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hcone
    simpa only [sq_abs, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hcone' : r * |a| ≤ s * q / 2 := by
    have hleft : 0 ≤ r * |a| := mul_nonneg hr.le (abs_nonneg _)
    have hright : 0 ≤ s * q / 2 := by positivity
    have hsquares : (r * |a|) ^ 2 ≤ (s * q / 2) ^ 2 := by
      rw [mul_pow, sq_abs, div_pow, mul_pow, hr2, hq2]
      nlinarith
    exact (sq_le_sq₀ hleft hright).1 hsquares
  let l₀ := q / (2 * r) + a / s
  let l₁ := q / (2 * r) - a / s
  have hcoeff : |a / s| ≤ q / (2 * r) := by
    rw [abs_div, abs_of_pos hs]
    apply (div_le_div_iff₀ hs (by positivity)).2
    nlinarith
  have hl₀ : 0 ≤ l₀ := by dsimp only [l₀]; linarith [(abs_le.mp hcoeff).1]
  have hl₁ : 0 ≤ l₁ := sub_nonneg.mpr (abs_le.mp hcoeff).2
  have hsum : (l₀ + l₁) * r = q := by dsimp only [l₀, l₁]; field_simp; ring
  have hdiff : (l₀ - l₁) * s / 2 = a := by dsimp only [l₀, l₁]; field_simp; ring
  refine ⟨l₀, l₁, hl₀, hl₁, ?_⟩
  rw [circleCandidate, circlePoint_sub_first, circlePoint_sub_second]
  have hedge : firstEdge c = s • firstAxis c :=
    (NormedSpace.norm_smul_normalize (firstEdge c)).symm
  rw [hedge]
  have hid : l₀ • ((1 / 2 : ℝ) • (s • firstAxis c) + r • circleDirection c n) +
      l₁ • ((-1 / 2 : ℝ) • (s • firstAxis c) + r • circleDirection c n) =
        ((l₀ - l₁) * s / 2) • firstAxis c + ((l₀ + l₁) * r) • circleDirection c n := by
    module
  change n = _
  rw [hid, hdiff, hsum]
  have hqv : q • circleDirection c n = circleProjection c n :=
    NormedSpace.norm_smul_normalize (circleProjection c n)
  rw [hqv]
  dsimp only [circleProjection, a]
  module

end BlaschkeLebesgue.BalancedContacts.Opposite
