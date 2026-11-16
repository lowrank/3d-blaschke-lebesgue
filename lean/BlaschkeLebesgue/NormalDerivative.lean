module

public import BlaschkeLebesgue.SupportDifferentiation
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Curvature bounds from support-map derivatives

At a unit normal the derivative of normalization is the tangent projection.
Complementary support maps therefore have complementary tangent derivatives.
Monotonicity, homogeneity, and symmetry prove that each derivative is a positive
semidefinite contraction with the normal direction in its kernel.
-/

public noncomputable section

open MeasureTheory Set NormedSpace Filter Topology
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem normalSupport_unitBall {x : Space} (hx : x ≠ 0) :
    normalSupport unitBallBody x = normalize x := by
  apply eq_unit_of_norm_le_inner_eq (norm_normalize hx)
    (mem_unitBallBody.1 (normalSupport_mem unitBallBody x))
  change ⟪normalize x, supportPoint unitBallBody (normalize x)⟫_ℝ = 1
  rw [inner_supportPoint, support_unitBallBody (norm_normalize hx)]

theorem support_unitBallBody_eq_norm (x : Space) : support unitBallBody x = ‖x‖ := by
  rw [← inner_normalSupport]
  by_cases hx : x = 0
  · simp [hx]
  rw [normalSupport_unitBall hx, NormedSpace.normalize, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp

theorem hasFDerivAt_space_norm {x : Space} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Space => ‖y‖) (innerSL ℝ (normalize x)) x := by
  have hsum : unitBallBody + (0 : ℝ) • unitBallBody = unitBallBody :=
    parallelBody_zero unitBallBody
  have h := hasFDerivAt_support hsum hx
  have heq : support unitBallBody = fun y : Space => ‖y‖ := funext support_unitBallBody_eq_norm
  rw [heq, normalSupport_unitBall hx] at h
  exact h

@[expose] def tangentProjection (u : Space) : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space - (innerSL ℝ u).smulRight u

theorem tangentProjection_apply (u v : Space) :
    tangentProjection u v = v - ⟪u, v⟫_ℝ • u := rfl

theorem hasFDerivAt_normalize_unit {u : Space} (hu : ‖u‖ = 1) :
    HasFDerivAt (normalize : Space → Space) (tangentProjection u) u := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hn : HasFDerivAt (fun y : Space => ‖y‖) (innerSL ℝ u) u := by
    simpa only [normalize_eq_self_of_norm_eq_one hu] using hasFDerivAt_space_norm hu0
  have hi : HasFDerivAt (fun y : Space => ‖y‖⁻¹) (-(innerSL ℝ u)) u := by
    have h := (hasFDerivAt_inv (norm_ne_zero_iff.2 hu0)).comp u hn
    have heq : (ContinuousLinearMap.toSpanSingleton ℝ (-(‖u‖ ^ 2)⁻¹)).comp
        (innerSL ℝ u) = -(innerSL ℝ u) := by
      ext v
      simp [hu]
    rw [heq] at h
    exact h
  convert hi.smul (hasFDerivAt_id u) using 1
  · rfl
  · ext v
    simp [tangentProjection, hu, sub_eq_add_neg]

theorem normalSupport_add {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    {x : Space} (hx : x ≠ 0) : normalSupport K x + normalSupport L x = normalize x :=
  supportPoint_add_eq_unit hKL (norm_normalize hx)

theorem normalSupport_complement_derivative {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {u : Space} (hu : ‖u‖ = 1)
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (normalSupport K) A u) :
    HasFDerivAt (normalSupport L) (tangentProjection u - A) u := by
  apply ((hasFDerivAt_normalize_unit hu).sub hd).congr_of_eventuallyEq
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  filter_upwards [isOpen_ne.mem_nhds hu0] with x hx
  exact eq_sub_of_add_eq' (normalSupport_add hKL hx)

theorem normalSupport_monotone (K : ConvexBody Space) (x y : Space) :
    0 ≤ ⟪normalSupport K x - normalSupport K y, x - y⟫_ℝ := by
  have h1 := inner_le_support K x (normalSupport_mem K y)
  have h2 := inner_le_support K y (normalSupport_mem K x)
  rw [← inner_normalSupport K x] at h1
  rw [← inner_normalSupport K y] at h2
  rw [real_inner_comm, inner_sub_left, inner_sub_right, inner_sub_right]
  linarith only [h1, h2]

theorem normalSupport_derivative_nonneg {K : ConvexBody Space} {x : Space}
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (normalSupport K) A x) (v : Space) :
    0 ≤ ⟪A v, v⟫_ℝ := by
  apply ge_of_tendsto ((hd.lim_real v).inner tendsto_const_nhds)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have h := normalSupport_monotone K (x + r⁻¹ • v) x
  rw [add_sub_cancel_left, inner_smul_right] at h
  have h' : 0 ≤ ⟪normalSupport K (x + r⁻¹ • v) - normalSupport K x, v⟫_ℝ :=
    nonneg_of_mul_nonneg_right h (inv_pos.2 hr)
  simpa only [real_inner_smul_left] using mul_nonneg hr.le h'

theorem normalSupport_derivative_radial {K : ConvexBody Space} {x : Space}
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (normalSupport K) A x) : A x = 0 := by
  have he : (fun r : ℝ => r • (normalSupport K (x + r⁻¹ • x) - normalSupport K x))
      =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hsum : x + r⁻¹ • x = (1 + r⁻¹) • x := by module
    rw [hsum, normalSupport_smul K (by positivity), sub_self, smul_zero]
  exact tendsto_nhds_unique (hd.lim_real x) (tendsto_const_nhds.congr' he.symm)

theorem normalSupport_derivative_tangent {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {x : Space} (hx : x ≠ 0)
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (normalSupport K) A x) (v : Space) :
    ⟪x, A v⟫_ℝ = 0 := by
  have h := normalSupport_derivative_symmetric hKL hx hd v x
  rw [normalSupport_derivative_radial hd, inner_zero_left] at h
  simpa only [real_inner_comm] using h

theorem normalSupport_derivative_le_one {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {u : Space} (hu : ‖u‖ = 1)
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (normalSupport K) A u) (v : Space) :
    ⟪A v, v⟫_ℝ ≤ ‖v‖ ^ 2 := by
  have h := normalSupport_derivative_nonneg (normalSupport_complement_derivative hKL hu hd) v
  simp only [sub_apply, tangentProjection_apply, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  nlinarith only [h, sq_nonneg ⟪u, v⟫_ℝ]

end BlaschkeLebesgue
