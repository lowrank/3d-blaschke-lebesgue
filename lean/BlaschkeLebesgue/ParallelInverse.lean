module

public import BlaschkeLebesgue.ParallelParametrization
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Injectivity and quantitative inverse bounds for the parallel parametrization

An inner ball controls changes of radial scale, while support monotonicity
controls changes of normal direction. Together they give a global lower
Lipschitz bound whenever the parallel radius is positive.
-/

public noncomputable section

open MeasureTheory Set Metric NormedSpace
open scoped InnerProductSpace NNReal

namespace BlaschkeLebesgue

theorem support_ge_of_innerBall {K : ConvexBody Space} {a : ℝ} (ha : 0 ≤ a)
    (hball : closedBall (0 : Space) a ⊆ (K : Set Space)) {u : Space} (hu : ‖u‖ = 1) :
    a ≤ support K u := by
  have hx : a • u ∈ K := hball (by simp [norm_smul, hu, abs_of_nonneg ha])
  simpa only [inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one] using
    inner_le_support K u hx

theorem inner_parallelSupport_le (K : ConvexBody Space) {t : ℝ} (ht : 0 ≤ t)
    {u : Space} (hu : ‖u‖ = 1) (x : Space) :
    ⟪u, parallelSupport K t x⟫_ℝ ≤ ‖x‖ * (support K u + t) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [parallelSupport_eq_norm_smul, inner_smul_right]
  have h := inner_le_support (parallelBody K t) u
    (parallel_support_point_mem K t (norm_normalize hx))
  rw [support_parallelBody K ht hu] at h
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

theorem inner_normalize_parallelSupport (K : ConvexBody Space) (t : ℝ)
    {x : Space} (hx : x ≠ 0) :
    ⟪normalize x, parallelSupport K t x⟫_ℝ = ‖x‖ * (support K (normalize x) + t) := by
  rw [parallelSupport_eq_norm_smul, inner_smul_right, inner_add_right,
    inner_smul_right, inner_supportPoint, real_inner_self_eq_norm_sq, norm_normalize hx,
    one_pow, mul_one]

/-- Moving radial scale must move the image by at least the inner support distance. -/
theorem parallelSupport_norm_difference_le {K : ConvexBody Space} {a t : ℝ}
    (ha : 0 ≤ a) (hball : closedBall (0 : Space) a ⊆ (K : Set Space)) (ht : 0 ≤ t)
    (x y : Space) :
    (a + t) * |‖x‖ - ‖y‖| ≤ ‖parallelSupport K t x - parallelSupport K t y‖ := by
  wlog hxy : ‖y‖ ≤ ‖x‖ generalizing x y
  · have h := this y x (le_of_not_ge hxy)
    simpa only [abs_sub_comm, norm_sub_rev] using h
  rw [abs_of_nonneg (sub_nonneg.2 hxy)]
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.1 (le_antisymm (by simpa [hx] using hxy) (norm_nonneg y))
    simp [hx, hy]
  have hu : ‖normalize x‖ = 1 := norm_normalize hx
  have hs := support_ge_of_innerBall ha hball hu
  have h1 := inner_normalize_parallelSupport K t hx
  have h2 := inner_parallelSupport_le K ht hu y
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hs t) (sub_nonneg.2 hxy)
  have hc := real_inner_le_norm (normalize x) (parallelSupport K t x - parallelSupport K t y)
  rw [hu, one_mul, inner_sub_right] at hc
  nlinarith only [h1, h2, hmul, hc]

/-- A positive parallel radius separates distinct normal directions quantitatively. -/
theorem parallel_support_point_norm_sub_ge (K : ConvexBody Space) {t : ℝ} (_ht : 0 ≤ t)
    (u v : Space) : t * ‖u - v‖ ≤
      ‖(supportPoint K u + t • u) - (supportPoint K v + t • v)‖ := by
  have hm := supportPoint_monotone K u v
  have hi := real_inner_le_norm
    ((supportPoint K u + t • u) - (supportPoint K v + t • v)) (u - v)
  have heq : (supportPoint K u + t • u) - (supportPoint K v + t • v) =
      (supportPoint K u - supportPoint K v) + t • (u - v) := by module
  rw [heq, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hi
  by_cases huv : ‖u - v‖ = 0
  · simpa only [huv, mul_zero] using
      norm_nonneg ((supportPoint K u + t • u) - (supportPoint K v + t • v))
  apply le_of_mul_le_mul_right (a := ‖u - v‖)
    (by rw [heq]; nlinarith only [hm, hi])
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm huv)

/-- A global lower Lipschitz estimate, expressed without divisions. -/
theorem parallelSupport_lower_bound {K : ConvexBody Space} {a R t : ℝ}
    (ha : 0 ≤ a) (hball : closedBall (0 : Space) a ⊆ (K : Set Space))
    (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R) (ht : 0 ≤ t) (x y : Space) :
    t * (a + t) * ‖x - y‖ ≤
      (a + R + 3 * t) * ‖parallelSupport K t x - parallelSupport K t y‖ := by
  let D := ‖parallelSupport K t x - parallelSupport K t y‖
  have hD : 0 ≤ D := norm_nonneg _
  have hrad := parallelSupport_norm_difference_le ha hball ht x y
  change (a + t) * |‖x‖ - ‖y‖| ≤ D at hrad
  by_cases hx : x = 0
  · subst x
    simp only [norm_zero, zero_sub, norm_neg, abs_neg, abs_of_nonneg (norm_nonneg y)] at hrad ⊢
    have h := mul_le_mul_of_nonneg_left hrad ht
    nlinarith only [h, mul_nonneg (show 0 ≤ a + R + 2 * t by positivity) hD]
  by_cases hy : y = 0
  · subst y
    simp only [norm_zero, sub_zero, abs_of_nonneg (norm_nonneg x)] at hrad ⊢
    have h := mul_le_mul_of_nonneg_left hrad ht
    nlinarith only [h, mul_nonneg (show 0 ≤ a + R + 2 * t by positivity) hD]
  let u := normalize x
  let v := normalize y
  let P := supportPoint K u + t • u
  let Q := supportPoint K v + t • v
  have hP : ‖P‖ ≤ R + t := by
    calc
      ‖P‖ ≤ ‖supportPoint K u‖ + ‖t • u‖ := norm_add_le _ _
      _ ≤ R + t := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, u, norm_normalize hx,
          mul_one]
        linarith only [hbound _ (supportPoint_mem K u)]
  have hscale : ‖y‖ • (P - Q) = (parallelSupport K t x - parallelSupport K t y) -
      (‖x‖ - ‖y‖) • P := by
    rw [parallelSupport_eq_norm_smul, parallelSupport_eq_norm_smul]
    dsimp only [P, Q, u, v]
    module
  have hdir : ‖y‖ * (t * ‖u - v‖) ≤ D + |‖x‖ - ‖y‖| * (R + t) := by
    calc
      _ ≤ ‖y‖ * ‖P - Q‖ :=
        mul_le_mul_of_nonneg_left (parallel_support_point_norm_sub_ge K ht u v) (norm_nonneg _)
      _ = ‖‖y‖ • (P - Q)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
      _ ≤ D + |‖x‖ - ‖y‖| * ‖P‖ := by
        rw [hscale]
        simpa only [norm_smul, Real.norm_eq_abs] using
          norm_sub_le (parallelSupport K t x - parallelSupport K t y) ((‖x‖ - ‖y‖) • P)
      _ ≤ _ := by gcongr
  have hxy : ‖x - y‖ ≤ |‖x‖ - ‖y‖| + ‖y‖ * ‖u - v‖ := by
    have hid : x - y = (‖x‖ - ‖y‖) • u + ‖y‖ • (u - v) := by
      dsimp [u, v]
      rw [sub_smul, smul_sub, norm_smul_normalize, norm_smul_normalize]
      abel
    rw [hid]
    simpa only [norm_smul, Real.norm_eq_abs, norm_normalize hx, mul_one,
      abs_of_nonneg (norm_nonneg y), u] using
      norm_add_le ((‖x‖ - ‖y‖) • u) (‖y‖ • (u - v))
  have hxy' := mul_le_mul_of_nonneg_left hxy (show 0 ≤ t * (a + t) by positivity)
  have hdir' := mul_le_mul_of_nonneg_left hdir (show 0 ≤ a + t by positivity)
  have hrad' := mul_le_mul_of_nonneg_left hrad (show 0 ≤ R + 2 * t by positivity)
  nlinarith only [hxy', hdir', hrad']

theorem parallelSupport_antilipschitz {K : ConvexBody Space} {a R t : ℝ}
    (ha : 0 < a) (hball : closedBall (0 : Space) a ⊆ (K : Set Space))
    (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R) (ht : 0 < t) :
    AntilipschitzWith ⟨(a + R + 3 * t) / (t * (a + t)), by positivity⟩
      (parallelSupport K t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change ‖x - y‖ ≤ ((a + R + 3 * t) / (t * (a + t))) *
    ‖parallelSupport K t x - parallelSupport K t y‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos ht (add_pos ha ht))).2
  have h := parallelSupport_lower_bound ha.le hball hR hbound ht.le x y
  nlinarith only [h]

/-- The inverse estimate holds for every body with the origin in its interior. -/
theorem exists_antilipschitz_parallelSupport {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) {t : ℝ} (ht : 0 < t) :
    ∃ C, AntilipschitzWith C (parallelSupport K t) := by
  obtain ⟨a, ha, haball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h0)
  have hball : closedBall (0 : Space) (a / 2) ⊆ (K : Set Space) :=
    (closedBall_subset_ball (by linarith)).trans haball
  obtain ⟨R, hR, hbound⟩ := K.isBounded.exists_pos_norm_le
  exact ⟨_, parallelSupport_antilipschitz (by positivity) hball hR.le hbound ht⟩

theorem parallelSupport_injective {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) {t : ℝ} (ht : 0 < t) :
    Function.Injective (parallelSupport K t) := by
  obtain ⟨C, hC⟩ := exists_antilipschitz_parallelSupport h0 ht
  exact hC.injective

end BlaschkeLebesgue
