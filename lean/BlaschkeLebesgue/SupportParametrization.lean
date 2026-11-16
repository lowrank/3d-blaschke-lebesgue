module

public import BlaschkeLebesgue.SupportMap
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Homogeneous parametrizations from actual support points

Extend the support map from the sphere by positive homogeneity. For a summand
of the unit ball this map is globally Lipschitz, hence differentiable almost
everywhere. These are the analytic inputs for a change-of-variables proof of
the parallel-volume polynomial; that polynomial is not assumed here.
-/

public noncomputable section

open MeasureTheory Set NormedSpace
open scoped InnerProductSpace NNReal

namespace BlaschkeLebesgue

/-- Homogeneous extension of the actual supporting-point map. -/
@[expose] def homogeneousSupport (K : ConvexBody Space) (x : Space) : Space :=
  ‖x‖ • supportPoint K (normalize x)

@[simp] theorem homogeneousSupport_zero (K : ConvexBody Space) : homogeneousSupport K 0 = 0 := by
  simp [homogeneousSupport]

theorem homogeneousSupport_unit (K : ConvexBody Space) {u : Space} (hu : ‖u‖ = 1) :
    homogeneousSupport K u = supportPoint K u := by
  simp [homogeneousSupport, hu, normalize_eq_self_of_norm_eq_one hu]

theorem homogeneousSupport_smul (K : ConvexBody Space) {r : ℝ} (hr : 0 ≤ r) (x : Space) :
    homogeneousSupport K (r • x) = r • homogeneousSupport K x := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  · simp [homogeneousSupport, normalize_smul_of_pos hr, norm_smul, abs_of_pos hr, mul_smul]

theorem norm_homogeneousSupport_le {K : ConvexBody Space} {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (x : Space) : ‖homogeneousSupport K x‖ ≤ ‖x‖ * R := by
  rw [homogeneousSupport, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hR _ (supportPoint_mem K _)) (norm_nonneg _)

theorem norm_mul_normalize_sub_le {x y : Space} (hy : y ≠ 0) :
    ‖x‖ * ‖normalize x - normalize y‖ ≤ 2 * ‖x - y‖ := by
  have hid : ‖x‖ • (normalize x - normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • normalize y := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  calc
    ‖x‖ * ‖normalize x - normalize y‖ = ‖‖x‖ • (normalize x - normalize y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖x - y‖ + |‖y‖ - ‖x‖| := by
      rw [hid]
      simpa only [norm_smul, Real.norm_eq_abs, norm_normalize hy, mul_one] using
        norm_add_le (x - y) ((‖y‖ - ‖x‖) • normalize y)
    _ ≤ 2 * ‖x - y‖ := by
      have h := abs_norm_sub_norm_le x y
      rw [abs_sub_comm] at h
      linarith only [h]

/-- Global Lipschitz regularity follows from the proved spherical 1-Lipschitz bound. -/
theorem homogeneousSupport_lipschitz_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (R : ℝ≥0) (hR : ∀ x ∈ K, ‖x‖ ≤ R) :
    LipschitzWith (R + 2) (homogeneousSupport K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_ofNat]
  by_cases hx : x = 0
  · subst x
    simp only [homogeneousSupport_zero, zero_sub, norm_neg]
    have h := norm_homogeneousSupport_le hR y
    nlinarith only [h, norm_nonneg y]
  by_cases hy : y = 0
  · subst y
    simp only [homogeneousSupport_zero, sub_zero]
    have h := norm_homogeneousSupport_le hR x
    nlinarith only [h, norm_nonneg x]
  have hs := supportPoint_norm_sub_le_of_ball_sum hKL (norm_normalize hx) (norm_normalize hy)
  have hid : homogeneousSupport K x - homogeneousSupport K y =
      ‖x‖ • (supportPoint K (normalize x) - supportPoint K (normalize y)) +
        (‖x‖ - ‖y‖) • supportPoint K (normalize y) := by
    dsimp [homogeneousSupport]
    module
  calc
    ‖homogeneousSupport K x - homogeneousSupport K y‖ ≤
        ‖x‖ * ‖supportPoint K (normalize x) - supportPoint K (normalize y)‖ +
          |‖x‖ - ‖y‖| * ‖supportPoint K (normalize y)‖ := by
      rw [hid]
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using
        norm_add_le (‖x‖ • (supportPoint K (normalize x) - supportPoint K (normalize y)))
          ((‖x‖ - ‖y‖) • supportPoint K (normalize y))
    _ ≤ ‖x‖ * ‖normalize x - normalize y‖ + |‖x‖ - ‖y‖| * R :=
      add_le_add (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hR _ (supportPoint_mem K _)) (abs_nonneg _))
    _ ≤ 2 * ‖x - y‖ + ‖x - y‖ * R :=
      add_le_add (norm_mul_normalize_sub_le hy)
        (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x y) R.coe_nonneg)
    _ = (R + 2) * ‖x - y‖ := by ring

theorem exists_lipschitz_homogeneousSupport_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) : ∃ C, LipschitzWith C (homogeneousSupport K) := by
  obtain ⟨R, hR, hbound⟩ := K.isBounded.exists_pos_norm_le
  exact ⟨⟨R, hR.le⟩ + 2, homogeneousSupport_lipschitz_of_ball_sum hKL ⟨R, hR.le⟩ hbound⟩

theorem homogeneousSupport_ae_differentiable_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    ∀ᵐ x ∂(volume : Measure Space), DifferentiableAt ℝ (homogeneousSupport K) x := by
  obtain ⟨C, hC⟩ := exists_lipschitz_homogeneousSupport_of_ball_sum hKL
  exact hC.ae_differentiableAt

theorem homogeneousSupport_add_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (x : Space) :
    homogeneousSupport K x + homogeneousSupport L x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [homogeneousSupport, homogeneousSupport, ← smul_add,
      supportPoint_add_eq_unit hKL (norm_normalize hx), norm_smul_normalize]

theorem supportPoint_reflectBody_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {u : Space} (hu : ‖u‖ = 1) :
    supportPoint (reflectBody K) u = -supportPoint K (-u) := by
  have hKL' : reflectBody K + reflectBody L = unitBallBody := by
    rw [← reflectBody_add, hKL, reflectBody_unitBallBody]
  symm
  apply supportPoint_unique_of_ball_sum hKL' hu
  · exact (mem_reflectBody K _).2 (by simpa using supportPoint_mem K (-u))
  · rw [support_reflectBody, inner_neg_right]
    simpa only [inner_neg_left] using inner_supportPoint K (-u)

theorem homogeneousSupport_reflectBody_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (x : Space) :
    homogeneousSupport (reflectBody K) x = -homogeneousSupport K (-x) := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [homogeneousSupport, supportPoint_reflectBody_of_ball_sum hKL (norm_normalize hx),
      norm_neg, normalize_neg, smul_neg]

theorem HasConstantWidth.homogeneousSupport_ae_differentiable {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) :
    ∀ᵐ x ∂(volume : Measure Space), DifferentiableAt ℝ (homogeneousSupport K) x :=
  homogeneousSupport_ae_differentiable_of_ball_sum hK.add_reflectBody

end BlaschkeLebesgue
