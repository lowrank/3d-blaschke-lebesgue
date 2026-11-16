module

public import BlaschkeLebesgue.Basic
public import BlaschkeLebesgue.Radial

/-!
# Geometric cap estimates

The negative-cap bound applies to actual points of a unit-width body. Spherical
caps are expressed by inner products, so the exact rational grid can be used
without introducing rounded angles.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A closed spherical cap, specified by the cosine of its half-angle. -/
@[expose] def sphericalCap (u : E) (c : ℝ) : Set E :=
  {x | ‖x‖ = 1 ∧ c ≤ ⟪u, x⟫_ℝ}

/-- A point common to two caps forces their centers to be close enough. -/
theorem inner_lower_of_common_cap {u v x : E} {c : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hc : 0 ≤ c)
    (hx₁ : x ∈ sphericalCap u c) (hx₂ : x ∈ sphericalCap v c) :
    2 * c ^ 2 - 1 ≤ ⟪u, v⟫_ℝ := by
  have hinner := real_inner_le_norm (u + v) x
  rw [inner_add_left, hx₁.1, mul_one] at hinner
  have hsum : 2 * c ≤ ‖u + v‖ := by linarith [hx₁.2, hx₂.2]
  have hsq := (sq_le_sq₀ (show 0 ≤ 2 * c by positivity) (norm_nonneg _)).2 hsum
  have hexpand := norm_add_sq_real u v
  rw [hu, hv] at hexpand
  nlinarith

theorem sphericalCap_disjoint {u v : E} {c : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hc : 0 ≤ c)
    (hsep : ⟪u, v⟫_ℝ < 2 * c ^ 2 - 1) :
    Disjoint (sphericalCap u c) (sphericalCap v c) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact (not_le_of_gt hsep) (inner_lower_of_common_cap hu hv hc hx₁ hx₂)

/-- The negative-cap quadratic inequality follows from diameter one, including
replacement of the actual contact radius by a smaller interval endpoint. -/
theorem HasConstantWidth.negative_cap_quadratic {K : ConvexBody E}
    (hK : HasConstantWidth K 1) {u v : E} {ρ R r c : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hrR : r ≤ R) (hc : 0 ≤ c) (hangle : ⟪u, v⟫_ℝ ≤ -c)
    (hx : ρ • u ∈ K) (hy : R • v ∈ K) :
    ρ ^ 2 + 2 * r * c * ρ + r ^ 2 ≤ 1 := by
  have hR : 0 ≤ R := hr.trans hrR
  have hdist := hK.norm_sub_le (by norm_num) hx hy
  have hsq := (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hdist
  rw [norm_sub_sq_real, norm_smul, norm_smul, hu, hv, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hρ, abs_of_nonneg hR,
    real_inner_smul_left, real_inner_smul_right] at hsq
  have hprod := mul_le_mul_of_nonneg_left hangle (mul_nonneg hρ hR)
  have hreplace := mul_nonneg (sub_nonneg.mpr hrR) (mul_nonneg hc hρ)
  have hradius := (sq_le_sq₀ hr hR).2 hrR
  nlinarith

/-- Every point of the body in a negative contact cap obeys the radical bound,
without any smoothness assumption. -/
theorem HasConstantWidth.negative_cap_bound {K : ConvexBody E}
    (hK : HasConstantWidth K 1) {u v : E} {ρ R r c s : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hrR : r ≤ R) (hc : 0 ≤ c) (hcircle : c ^ 2 + s ^ 2 = 1)
    (hangle : ⟪u, v⟫_ℝ ≤ -c) (hx : ρ • u ∈ K) (hy : R • v ∈ K) :
    ρ ≤ -r * c + Real.sqrt (1 - r ^ 2 * s ^ 2) := by
  have hquad := hK.negative_cap_quadratic hu hv hρ hr hrR hc hangle hx hy
  have hscaled := congrArg (fun t : ℝ ↦ r ^ 2 * t) hcircle
  have hsquare : (ρ + r * c) ^ 2 ≤ 1 - r ^ 2 * s ^ 2 := by nlinarith
  have hroot := Real.sqrt_le_sqrt hsquare
  rw [Real.sqrt_sq (show 0 ≤ ρ + r * c by positivity)] at hroot
  linarith

end BlaschkeLebesgue
