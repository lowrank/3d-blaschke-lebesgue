module

public import BlaschkeLebesgue.SupportParametrization

/-!
# Parametrizing actual parallel bodies

The homogeneous support map plus `t` times the identity maps the closed unit ball
onto the actual parallel body. Its derivative depends affinely on `t` almost
everywhere, on one common full-measure set.
-/

public noncomputable section

open MeasureTheory Set Metric NormedSpace
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem supportPoint_monotone (K : ConvexBody Space) (u v : Space) :
    0 ≤ ⟪supportPoint K u - supportPoint K v, u - v⟫_ℝ := by
  have h1 := inner_le_support K u (supportPoint_mem K v)
  have h2 := inner_le_support K v (supportPoint_mem K u)
  rw [← inner_supportPoint K u] at h1
  rw [← inner_supportPoint K v] at h2
  rw [real_inner_comm, inner_sub_left, inner_sub_right, inner_sub_right]
  linarith only [h1, h2]

theorem parallel_support_point_mem (K : ConvexBody Space) (t : ℝ) {u : Space} (hu : ‖u‖ = 1) :
    supportPoint K u + t • u ∈ parallelBody K t :=
  Set.add_mem_add (supportPoint_mem K u) (Set.smul_mem_smul_set (mem_unitBallBody.2 hu.le))

theorem inner_parallel_support_point (K : ConvexBody Space) {t : ℝ} (ht : 0 ≤ t)
    {u : Space} (hu : ‖u‖ = 1) :
    ⟪u, supportPoint K u + t • u⟫_ℝ = support (parallelBody K t) u := by
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow,
    mul_one, inner_supportPoint, support_parallelBody K ht hu]

theorem parallel_support_point_unique {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    {t : ℝ} (ht : 0 ≤ t) {u x : Space} (hu : ‖u‖ = 1)
    (hx : x ∈ parallelBody K t) (hs : ⟪u, x⟫_ℝ = support (parallelBody K t) u) :
    x = supportPoint K u + t • u := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [parallelBody_zero] at hx hs
    simpa using supportPoint_unique_of_ball_sum hKL hu hx hs
  rcases hx with ⟨y, hy, _, ⟨z, hz, rfl⟩, rfl⟩
  have hy' := inner_le_support K u hy
  have hz' : ⟪u, z⟫_ℝ ≤ 1 := by
    have hh := real_inner_le_norm u z
    rw [hu, one_mul] at hh
    exact hh.trans (mem_unitBallBody.1 hz)
  rw [inner_add_right, inner_smul_right, support_parallelBody K ht.le hu] at hs
  have hzy : ⟪u, z⟫_ℝ = 1 := by nlinarith only [hy', hz', hs, ht]
  have hzunit : z = u := eq_unit_of_norm_le_inner_eq hu (mem_unitBallBody.1 hz) hzy
  have hys : ⟪u, y⟫_ℝ = support K u := by rw [hzy] at hs; linarith only [hs]
  rw [supportPoint_unique_of_ball_sum hKL hu hy hys, hzunit]

/-- The normal-direction parametrization, extended homogeneously to the entire space. -/
@[expose] def parallelSupport (K : ConvexBody Space) (t : ℝ) (x : Space) : Space :=
  homogeneousSupport K x + t • x

@[simp] theorem parallelSupport_zero (K : ConvexBody Space) (t : ℝ) :
    parallelSupport K t 0 = 0 := by
  simp [parallelSupport]

theorem parallelSupport_unit (K : ConvexBody Space) (t : ℝ) {u : Space} (hu : ‖u‖ = 1) :
    parallelSupport K t u = supportPoint K u + t • u := by
  rw [parallelSupport, homogeneousSupport_unit K hu]

theorem parallelSupport_smul (K : ConvexBody Space) (t : ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Space) :
    parallelSupport K t (r • x) = r • parallelSupport K t x := by
  rw [parallelSupport, homogeneousSupport_smul K hr, parallelSupport, smul_add, smul_comm t r]

theorem parallelSupport_eq_norm_smul (K : ConvexBody Space) (t : ℝ) (x : Space) :
    parallelSupport K t x = ‖x‖ • (supportPoint K (normalize x) + t • normalize x) := by
  rw [smul_add, smul_comm ‖x‖ t, norm_smul_normalize]
  rfl

/-- The parametrization covers precisely the parallel body, including its interior. -/
theorem parallelSupport_image_closedBall {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    (h0 : (0 : Space) ∈ interior (K : Set Space)) {t : ℝ} (ht : 0 ≤ t) :
    parallelSupport K t '' closedBall 0 1 = (parallelBody K t : Set Space) := by
  have h0t := zero_mem_interior_parallelBody h0 t
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · simpa only [hx0, parallelSupport_zero] using interior_subset h0t
    rw [parallelSupport_eq_norm_smul]
    apply (parallelBody K t).convex.smul_mem_of_zero_mem (interior_subset h0t)
      (parallel_support_point_mem K t (norm_normalize hx0))
    exact ⟨norm_nonneg _, by simpa using hx⟩
  · intro hy
    by_cases hy0 : y = 0
    · exact ⟨0, by simp, by simpa using hy0.symm⟩
    let v := normalize y
    have hv : ‖v‖ = 1 := norm_normalize hy0
    have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
    let ρ := radialFunction (parallelBody K t) v
    have hρ : 0 < ρ := radialFunction_pos h0t hv0
    have hrad : ‖y‖ ≤ ρ :=
      (smul_mem_iff_le_radialFunction h0t hv0 (norm_nonneg y)).1
        (by simpa only [v, norm_smul_normalize, SetLike.mem_coe] using hy)
    obtain ⟨n, hn, hs⟩ := radialFunction_supporting_normal h0t hv0
    have hboundary : ρ • v = supportPoint K n + t • n :=
      parallel_support_point_unique hKL ht hn (radialFunction_smul_mem h0t hv0) hs
    let r := ‖y‖ / ρ
    have hr : 0 ≤ r := div_nonneg (norm_nonneg y) hρ.le
    have hr1 : r ≤ 1 := (div_le_one hρ).2 hrad
    refine ⟨r • n, ?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hr, hn, mul_one] using hr1
    · rw [parallelSupport_smul K t hr, parallelSupport_unit K t hn, ← hboundary, smul_smul]
      have hrρ : r * ρ = ‖y‖ := by dsimp [r]; field_simp
      rw [hrρ]
      exact norm_smul_normalize y

/-- One common full-measure set supplies the affine derivative for every parameter. -/
theorem parallelSupport_ae_hasFDerivAt {K L : ConvexBody Space} (hKL : K + L = unitBallBody) :
    ∀ᵐ x ∂(volume : Measure Space), ∀ t : ℝ,
      HasFDerivAt (parallelSupport K t)
        (fderiv ℝ (homogeneousSupport K) x + t • ContinuousLinearMap.id ℝ Space) x := by
  filter_upwards [homogeneousSupport_ae_differentiable_of_ball_sum hKL] with x hx
  intro t
  exact hx.hasFDerivAt.add ((hasFDerivAt_id x).const_smul t)

end BlaschkeLebesgue
