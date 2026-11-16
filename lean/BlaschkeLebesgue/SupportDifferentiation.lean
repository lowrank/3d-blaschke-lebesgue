module

public import BlaschkeLebesgue.SupportParametrization
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives of actual support functions

The support point selected in a normalized direction is the gradient of the
support function away from the origin. The supporting inequalities and continuity
prove this directly. Its derivative exists almost everywhere and is symmetric
wherever it exists, by symmetry of the second derivative.
-/

public noncomputable section

open MeasureTheory Set NormedSpace Filter Topology Asymptotics Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def normalSupport (K : ConvexBody Space) (x : Space) : Space :=
  supportPoint K (normalize x)

theorem normalSupport_mem (K : ConvexBody Space) (x : Space) : normalSupport K x ∈ K :=
  supportPoint_mem K _

theorem normalSupport_smul (K : ConvexBody Space) {r : ℝ} (hr : 0 < r) (x : Space) :
    normalSupport K (r • x) = normalSupport K x := by
  simp only [normalSupport, normalize_smul_of_pos hr]

theorem inner_normalSupport (K : ConvexBody Space) (x : Space) :
    ⟪x, normalSupport K x⟫_ℝ = support K x := by
  calc
    ⟪x, normalSupport K x⟫_ℝ =
        ⟪‖x‖ • normalize x, normalSupport K x⟫_ℝ := by rw [norm_smul_normalize]
    _ = ‖x‖ * support K (normalize x) := by
      rw [real_inner_smul_left, normalSupport, inner_supportPoint]
    _ = support K x := by
      rw [← support_smul_direction K (normalize x) (norm_nonneg x), norm_smul_normalize]

theorem normalSupport_eq_inv_smul (K : ConvexBody Space) {x : Space} (hx : x ≠ 0) :
    normalSupport K x = ‖x‖⁻¹ • homogeneousSupport K x := by
  simp only [homogeneousSupport, smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx),
    one_smul, normalSupport]

theorem normalSupport_eventually_eq (K : ConvexBody Space) {x : Space} (hx : x ≠ 0) :
    normalSupport K =ᶠ[𝓝 x] (fun y => ‖y‖⁻¹ • homogeneousSupport K y) := by
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  exact normalSupport_eq_inv_smul K hy

theorem continuousAt_normalSupport {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {x : Space} (hx : x ≠ 0) :
    ContinuousAt (normalSupport K) x := by
  obtain ⟨C, hC⟩ := exists_lipschitz_homogeneousSupport_of_ball_sum hKL
  exact (continuousAt_congr (normalSupport_eventually_eq K hx)).2
    ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.2 hx)).smul hC.continuous.continuousAt)

theorem support_first_order_error (K : ConvexBody Space) (x y : Space) :
    0 ≤ support K y - support K x - ⟪normalSupport K x, y - x⟫_ℝ ∧
      support K y - support K x - ⟪normalSupport K x, y - x⟫_ℝ ≤
        ‖y - x‖ * ‖normalSupport K y - normalSupport K x‖ := by
  have h1 := inner_le_support K y (normalSupport_mem K x)
  have h2 := inner_le_support K x (normalSupport_mem K y)
  have hx := inner_normalSupport K x
  have hy := inner_normalSupport K y
  have hc := real_inner_le_norm (y - x) (normalSupport K y - normalSupport K x)
  simp only [inner_sub_left, inner_sub_right] at hc ⊢
  constructor <;> nlinarith only [h1, h2, hx, hy, hc,
    real_inner_comm (normalSupport K x) y, real_inner_comm (normalSupport K x) x]

/-- The actual supporting point represents the derivative of the support function. -/
theorem hasFDerivAt_support {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    {x : Space} (hx : x ≠ 0) :
    HasFDerivAt (support K) (innerSL ℝ (normalSupport K x)) x := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ y in 𝓝 x, ‖normalSupport K y - normalSupport K x‖ < ε :=
    (continuousAt_normalSupport hKL hx).tendsto.eventually (ball_mem_nhds _ hε)
  filter_upwards [he] with y hy
  obtain ⟨hlo, hhi⟩ := support_first_order_error K x y
  simp only [innerSL_apply_apply, Real.norm_eq_abs, abs_of_nonneg hlo]
  exact hhi.trans (by nlinarith only [hy.le, norm_nonneg (y - x)])

theorem normalSupport_ae_differentiable {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    ∀ᵐ x ∂(volume : Measure Space), DifferentiableAt ℝ (normalSupport K) x := by
  have hne : ∀ᵐ x ∂(volume : Measure Space), x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [homogeneousSupport_ae_differentiable_of_ball_sum hKL, hne] with x hx hx0
  have hn : DifferentiableAt ℝ (fun y : Space => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx0
  have hd := (hn.inv (norm_ne_zero_iff.2 hx0)).smul hx
  exact (normalSupport_eventually_eq K hx0).differentiableAt_iff.2 hd

/-- Symmetry requires only existence of the derivative at this point, not a smooth boundary. -/
theorem normalSupport_derivative_symmetric {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {x : Space} (hx : x ≠ 0)
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (normalSupport K) A x) (v w : Space) :
    ⟪A v, w⟫_ℝ = ⟪A w, v⟫_ℝ := by
  have he : ∀ᶠ y in 𝓝 x, HasFDerivAt (support K) (innerSL ℝ (normalSupport K y)) y := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact hasFDerivAt_support hKL hy
  have hsecond : HasFDerivAt (fun y => innerSL ℝ (normalSupport K y))
      ((innerSL ℝ).comp A) x := (innerSL ℝ).hasFDerivAt.comp x hd
  exact second_derivative_symmetric_of_eventually he hsecond v w

end BlaschkeLebesgue
