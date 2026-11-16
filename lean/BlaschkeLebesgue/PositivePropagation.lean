module

public import BlaschkeLebesgue.RadialFunction
public import BlaschkeLebesgue.RadialGeometry

/-!
# Positive-cap propagation from supporting normals

The argument uses orthogonal components of three unit vectors and a supporting
plane at the new radial boundary point. No differentiability of the boundary is
needed for the propagation step.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_orthogonal_component_sq (x : E) {v : E} (hv : ‖v‖ = 1) :
    ‖x - ⟪x, v⟫_ℝ • v‖ ^ 2 = ‖x‖ ^ 2 - ⟪x, v⟫_ℝ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hv, mul_one,
    Real.norm_eq_abs, sq_abs]
  ring

/-- A cone constraint on a supporting normal gives a lower bound for its scalar
product with every direction in a nearby spherical cap. -/
theorem supporting_inner_lower {u v n : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hn : ‖n‖ = 1) {c q a d b : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hcircle : c ^ 2 + q ^ 2 = 1) (hangle : c ≤ ⟪u, v⟫_ℝ)
    (ha : 0 < a) (hd : 0 ≤ d) (hb : 0 < b) (hcone : a ^ 2 + d ^ 2 = b ^ 2)
    (hnormal : a ≤ b * ⟪n, v⟫_ℝ) :
    ⟪n, v⟫_ℝ * (a * c - d * q) ≤ a * ⟪n, u⟫_ℝ := by
  let t := ⟪n, v⟫_ℝ
  let p := ⟪u, v⟫_ℝ
  let N := n - t • v
  let U := u - p • v
  have ht : 0 < t := pos_of_mul_pos_right (ha.trans_le hnormal) hb.le
  have hp : 0 ≤ p := hc.trans hangle
  have hN : ‖N‖ ^ 2 = 1 - t ^ 2 := by
    simpa [N, t, hn] using norm_orthogonal_component_sq n hv
  have hU : ‖U‖ ^ 2 = 1 - p ^ 2 := by
    simpa [U, p, hu] using norm_orthogonal_component_sq u hv
  have hUle : ‖U‖ ≤ q := by
    apply (sq_le_sq₀ (norm_nonneg _) hq).1
    nlinarith only [hU, hcircle, sq_le_sq₀ hc hp |>.2 hangle]
  have hNle : a * ‖N‖ ≤ d * t := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    have hsq := (sq_le_sq₀ ha.le (mul_nonneg hb.le ht.le)).2 hnormal
    have hscaled := congrArg (fun r : ℝ ↦ r * t ^ 2) hcone
    simp only [mul_pow, hN]
    nlinarith only [hsq, hscaled]
  have hprod : ⟪N, U⟫_ℝ = ⟪n, u⟫_ℝ - t * p := by
    dsimp [N, U, t, p]
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hv, real_inner_comm u v]
    ring
  have hCS := (abs_le.1 (abs_real_inner_le_norm N U)).1
  rw [hprod] at hCS
  have hcross := mul_le_mul_of_nonneg_left hUle (norm_nonneg N)
  have hp' := mul_le_mul_of_nonneg_left hangle ht.le
  have hlow : t * c - ‖N‖ * q ≤ ⟪n, u⟫_ℝ := by linarith only [hCS, hcross, hp']
  have hlow' := mul_le_mul_of_nonneg_left hlow ha.le
  have hNle' := mul_le_mul_of_nonneg_right hNle hq
  nlinarith only [hlow', hNle']

/-- A rational propagation test transports a lower radial bound to a nearby
direction. This statement applies directly to a compact convex body, including
nonsmooth bodies. -/
theorem HasConstantWidth.positive_cap_step [CompleteSpace E] {K : ConvexBody E}
    (hK : HasConstantWidth K 1) (h0 : (0 : E) ∈ interior (K : Set E))
    {R m x y c q : ℝ} (hR : 0 ≤ R) (hbound : ∀ z ∈ K, ‖z‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) (hx : 0 < x) (hy : 0 < y)
    (hxm : x ^ 2 ≤ m) (hc : 0 ≤ c) (hq : 0 ≤ q) (hcircle : c ^ 2 + q ^ 2 = 1)
    (hrad : 0 ≤ 4 * x ^ 2 - (x ^ 2 + m) ^ 2) (hlinear : 0 < y * c - x)
    (htest : y ^ 2 * (4 * x ^ 2 - (x ^ 2 + m) ^ 2) * q ^ 2 ≤
      (x ^ 2 + m) ^ 2 * (y * c - x) ^ 2)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hangle : c ≤ ⟪u, v⟫_ℝ)
    (hprevious : y ≤ radialFunction K u) : x ≤ radialFunction K v := by
  by_contra! hsmall
  let s := radialFunction K v
  let r := radialFunction K u
  have hv' : v ≠ 0 := by intro h; simp [h] at hv
  have hu' : u ≠ 0 := by intro h; simp [h] at hu
  have hs : 0 < s := radialFunction_pos h0 hv'
  have hr : 0 < r := radialFunction_pos h0 hu'
  obtain ⟨n, hn, hnmax⟩ := radialFunction_supporting_normal h0 hv'
  let t := ⟪n, v⟫_ℝ
  let T := x ^ 2 + m
  let D := Real.sqrt (4 * x ^ 2 - (x ^ 2 + m) ^ 2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = 4 * x ^ 2 - T ^ 2 := Real.sq_sqrt hrad
  have hnormal : s ^ 2 + m ≤ 2 * s * t := by
    have hh := hK.radial_normal hR hbound (radialFunction_smul_mem h0 hv') hn hnmax
    change ‖s • v‖ ^ 2 + 1 - R ^ 2 ≤ 2 * ⟪s • v, n⟫_ℝ at hh
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hv, mul_one,
      real_inner_smul_left, real_inner_comm n v] at hh
    dsimp [t]
    nlinarith only [hh, hmR]
  have hparamnormal : T ≤ (2 * x) * t := by
    have hmx : 0 ≤ m - s * x := by
      nlinarith only [hxm, mul_le_mul_of_nonneg_right hsmall.le hx.le]
    have hh := mul_nonneg (show 0 ≤ x - s by linarith) hmx
    have hh' := mul_le_mul_of_nonneg_left hnormal hx.le
    have hmul : s * T ≤ s * ((2 * x) * t) := by dsimp [T]; nlinarith only [hh, hh']
    exact le_of_mul_le_mul_left hmul hs
  have ht : 0 < t := pos_of_mul_pos_right (hT.trans_le hparamnormal) (by positivity)
  have hinner := supporting_inner_lower hu hv hn hc hq hcircle hangle hT hD
    (show 0 < 2 * x by positivity)
    (show T ^ 2 + D ^ 2 = (2 * x) ^ 2 by nlinarith only [hDsq])
      hparamnormal
  obtain ⟨hden, hN⟩ := Radial.propagation_test_sound hm hx hy hq hrad hlinear htest
  change 0 < T * c - D * q at hden
  change x * T / (T * c - D * q) ≤ y at hN
  have hsupport : r * ⟪n, u⟫_ℝ ≤ s * t := by
    have hh := inner_le_support K n (radialFunction_smul_mem h0 hu')
    rw [← hnmax, real_inner_smul_right, real_inner_smul_right] at hh
    exact hh
  have hcone := mul_le_mul_of_nonneg_left hinner hr.le
  have hsupport' := mul_le_mul_of_nonneg_left hsupport hT.le
  have hmul : (r * (T * c - D * q)) * t ≤ (s * T) * t := by
    nlinarith only [hcone, hsupport']
  have hupper := le_of_mul_le_mul_right hmul ht
  have hchecked := (div_le_iff₀ hden).1 hN
  have hprevious' := mul_le_mul_of_nonneg_right hprevious hden.le
  have hstrict := mul_lt_mul_of_pos_right hsmall hT
  change s * T < x * T at hstrict
  change y * (T * c - D * q) ≤ r * (T * c - D * q) at hprevious'
  linarith only [hupper, hchecked, hprevious', hstrict]

end BlaschkeLebesgue
