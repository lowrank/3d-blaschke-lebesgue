module

public import BlaschkeLebesgue.ClippedActiveSupport

/-! # The actual support map on an enclosing-sphere edge -/

public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem oriented_height_mono {a b p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (ha : a ^ 2 + p ^ 2 = 1) (hb : b ^ 2 + q ^ 2 = 1) (hab : a ≤ b) :
    a * q ≤ b * p := by
  by_cases ha0 : 0 ≤ a
  · have hb0 : 0 ≤ b := ha0.trans hab
    apply (sq_le_sq₀ (mul_nonneg ha0 hq.le) (mul_nonneg hb0 hp.le)).1
    have he : (a * q) ^ 2 - (b * p) ^ 2 = a ^ 2 - b ^ 2 := by
      rw [mul_pow, mul_pow, show p ^ 2 = 1 - a ^ 2 by linarith,
        show q ^ 2 = 1 - b ^ 2 by linarith]
      ring
    nlinarith [sq_le_sq₀ ha0 hb0 |>.2 hab]
  · by_cases hb0 : 0 ≤ b
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha0) hq.le).trans
        (mul_nonneg hb0 hp.le)
    · have ha' : 0 ≤ -a := by linarith
      have hb' : 0 ≤ -b := by linarith
      have hs : (-b * p) ^ 2 ≤ (-a * q) ^ 2 := by
        have he : (-b * p) ^ 2 - (-a * q) ^ 2 = b ^ 2 - a ^ 2 := by
          rw [mul_pow, mul_pow, show p ^ 2 = 1 - a ^ 2 by linarith,
            show q ^ 2 = 1 - b ^ 2 by linarith]
          ring
        nlinarith [sq_le_sq₀ hb' ha' |>.2 (show -b ≤ -a by linarith)]
      have := (sq_le_sq₀ (mul_nonneg hb' hp.le) (mul_nonneg ha' hq.le)).1 hs
      nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sphere_normal_supports_ball {p x y : E} {r : ℝ} (hx : ‖x - p‖ = r)
    (hy : ‖y - p‖ ≤ r) : ⟪x - p, y - x⟫_ℝ ≤ 0 := by
  have hr : 0 ≤ r := hx ▸ norm_nonneg (x - p)
  have h := real_inner_le_norm (x - p) (y - p)
  rw [hx] at h
  have hm := mul_le_mul_of_nonneg_left hy hr
  have he : y - x = (y - p) - (x - p) := by abel
  rw [he, inner_sub_right, real_inner_self_eq_norm_sq, hx]
  nlinarith

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)

theorem clippingCircleDirection_frame (hR : 0 < c.radius) (i : Fin 4) {u : Space}
    (hp : axisProjection (c.clippingCircleAxis i) u ≠ 0) :
    ‖NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u)‖ = 1 ∧
      ⟪c.point i, NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) u)⟫_ℝ = 0 := by
  refine ⟨NormedSpace.norm_normalize hp, ?_⟩
  rw [← c.radius_smul_clippingCircleAxis hR.ne' i, real_inner_smul_left]
  simp only [NormedSpace.normalize, real_inner_smul_right,
    axisProjection_inner_axis (c.clippingCircleAxis_norm hR i), mul_zero]

theorem clippingCircle_normal_cone (hR : 1 / 2 < c.radius) (i : Fin 4) (u : UnitSphere)
    (hlo : -(1 / (2 * c.radius)) ≤ ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)
    (hhi : ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ≤ 1 - 1 / (2 * c.radius ^ 2)) :
    ∃ l₀ l₁ : ℝ, 0 ≤ l₀ ∧ 0 ≤ l₁ ∧
      (u : Space) = l₀ • c.clippingCircleCandidate i u +
        l₁ • (c.clippingCircleCandidate i u - c.point i) := by
  let R := c.radius
  let t := ClippingCircle.height R
  let r := ClippingCircle.radius R
  let z := ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ
  let q := ‖axisProjection (c.clippingCircleAxis i) (u : Space)‖
  have hR0 : 0 < R := by dsimp only [R]; linarith
  have hr : 0 < r := ClippingCircle.radius_pos hR
  have hq : 0 < q := norm_pos_iff.2 (c.clippingCircleProjection_ne_zero hR u i hlo hhi)
  have ht : t ^ 2 + r ^ 2 = R ^ 2 := ClippingCircle.height_sq_add_radius_sq hR
  have htr : (t - R) ^ 2 + r ^ 2 = 1 := ClippingCircle.offset_sq_add_radius_sq hR
  have hz : z ^ 2 + q ^ 2 = 1 := by
    have := axisProjection_norm_sq (c.clippingCircleAxis_norm hR0 i) u.norm_eq_one
    dsimp only [z, q]
    linarith
  have hlo' : t - R ≤ z := by
    dsimp only [t, R, ClippingCircle.height]
    linarith only [hlo]
  have hhi' : z ≤ t / R := by
    have he : t / R = 1 - 1 / (2 * R ^ 2) := by
      dsimp only [t, ClippingCircle.height]
      field_simp
    rw [he]
    exact hhi
  have h₀ := oriented_height_mono hr hq htr hz hlo'
  have h₁ := oriented_height_mono hq (div_pos hr hR0) hz
    (show (t / R) ^ 2 + (r / R) ^ 2 = 1 by
      rw [div_pow, div_pow, ← add_div, ht, div_self (pow_ne_zero _ hR0.ne')]) hhi'
  have h₁' : z * r ≤ t * q := by
    have he : z * (r / R) ≤ (t * q) / R := by simpa only [div_mul_eq_mul_div] using h₁
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hR0] at he
    exact he
  let l₀ := (z - (t - R) * q / r) / R
  let l₁ := (t * q / r - z) / R
  have hl₀ : 0 ≤ l₀ := by
    apply div_nonneg _ hR0.le
    exact sub_nonneg.2 ((div_le_iff₀ hr).2 h₀)
  have hl₁ : 0 ≤ l₁ := by
    apply div_nonneg _ hR0.le
    exact sub_nonneg.2 ((le_div_iff₀ hr).2 h₁')
  have hsum : (l₀ + l₁) * r = q := by dsimp only [l₀, l₁]; field_simp; ring
  have haxis : l₀ * t + l₁ * (t - R) = z := by dsimp only [l₀, l₁]; field_simp; ring
  refine ⟨l₀, l₁, hl₀, hl₁, ?_⟩
  change (u : Space) = l₀ • (t • c.clippingCircleAxis i + r •
    NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) (u : Space))) +
    l₁ • (c.clippingCirclePoint i
      (NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) (u : Space))) - c.point i)
  rw [c.clippingCirclePoint_sub_contact hR0.ne']
  have he : l₀ • (t • c.clippingCircleAxis i + r •
      NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) (u : Space))) +
      l₁ • ((t - R) • c.clippingCircleAxis i + r •
        NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) (u : Space))) =
      (l₀ * t + l₁ * (t - R)) • c.clippingCircleAxis i +
        ((l₀ + l₁) * r) • NormedSpace.normalize (axisProjection (c.clippingCircleAxis i) (u : Space)) := by
    module
  rw [he, haxis, hsum, NormedSpace.norm_smul_normalize]
  dsimp only [axisProjection, z]
  module

theorem clippingCircleCandidate_inner_le (hR : 1 / 2 < c.radius) (i : Fin 4) (u : UnitSphere)
    (hlo : -(1 / (2 * c.radius)) ≤ ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)
    (hhi : ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ≤ 1 - 1 / (2 * c.radius ^ 2))
    {y : Space} (hyR : ‖y‖ ≤ c.radius) (hyi : ‖y - c.point i‖ ≤ 1) :
    ⟪(u : Space), y⟫_ℝ ≤ ⟪(u : Space), c.clippingCircleCandidate i u⟫_ℝ := by
  obtain ⟨l₀, l₁, hl₀, hl₁, hn⟩ := c.clippingCircle_normal_cone hR i u hlo hhi
  have hf := c.clippingCircleDirection_frame (by linarith : 0 < c.radius) i
    (c.clippingCircleProjection_ne_zero hR u i hlo hhi)
  have hs := c.clippingCirclePoint_mem_spheres hR hf.1 hf.2
  have h₀ := sphere_normal_supports_ball
    (show ‖c.clippingCircleCandidate i u - 0‖ = c.radius by
      simpa only [mem_sphere, dist_eq_norm, clippingCircleCandidate] using hs.1)
    (by simpa only [sub_zero] using hyR)
  have h₁ := unitSphere_normal_supports_ball
    (show ‖c.clippingCircleCandidate i u - c.point i‖ = 1 by
      simpa only [mem_sphere, dist_eq_norm, clippingCircleCandidate] using hs.2) hyi
  have hi : ⟪(u : Space), y - c.clippingCircleCandidate i u⟫_ℝ ≤ 0 := by
    conv_lhs => lhs; rw [hn]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simpa only [sub_zero] using add_nonpos (mul_nonpos_of_nonneg_of_nonpos hl₀ h₀)
      (mul_nonpos_of_nonneg_of_nonpos hl₁ h₁)
  rw [inner_sub_right] at hi
  linarith

theorem normalSupport_clipped_clippingCircleCandidate
    {hne : (clippedOuter c.radius (range c.point)).Nonempty}
    (hR : 1 / 2 < c.radius) (i : Fin 4) (u : UnitSphere)
    (hlo : -(1 / (2 * c.radius)) ≤ ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ)
    (hhi : ⟪c.clippingCircleAxis i, (u : Space)⟫_ℝ ≤ 1 - 1 / (2 * c.radius ^ 2))
    (hmem : c.clippingCircleCandidate i u ∈ clippedOuter c.radius (range c.point)) :
    normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) =
      c.clippingCircleCandidate i u := by
  have hs : ⟪(u : Space), c.clippingCircleCandidate i u⟫_ℝ =
      support (clippedOuterBody c.radius (range c.point) hne) (u : Space) := by
    apply le_antisymm (inner_le_support _ _ hmem)
    apply (support_le_iff _ _ _).2
    intro y hy
    have hy' := (c.mem_clippedOuter_range_iff y).1 hy
    exact c.clippingCircleCandidate_inner_le hR i u hlo hhi hy'.1 (hy'.2 i)
  have hR1 : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  have he := supportPoint_unique_of_ball_sum
    (clippedBodies_complement c.radius (range c.point) hne hR1) u.norm_eq_one hmem hs
  simpa only [normalSupport, NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one] using he.symm

end BalancedContacts
end BlaschkeLebesgue
