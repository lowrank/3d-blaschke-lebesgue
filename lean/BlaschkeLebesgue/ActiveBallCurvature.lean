module

public import BlaschkeLebesgue.ClippedFaceCaps
public import BlaschkeLebesgue.TangentDeterminant
public import BlaschkeLebesgue.SupportInterior
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Curvature at active ball constraints

At an active ball, the support-map derivative has range perpendicular to
the ball normal. A nonzero tangent determinant forces that normal to be
parallel to the support direction. An interior ball-center inequality fixes
its sign, so nonzero area density can occur only on an actual spherical face.
-/

public noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem sphereCurvature_inner_active_ball (K : ConvexBody Space) (u : UnitSphere)
    {p : Space} {r : ℝ} (hball : ∀ x ∈ K, ‖x - p‖ ≤ r)
    (hactive : ‖normalSupport K (u : Space) - p‖ = r) (v : Space) :
    ⟪normalSupport K (u : Space) - p, sphereCurvature K u v⟫_ℝ = 0 := by
  by_cases hd : DifferentiableAt ℝ (normalSupport K) (u : Space)
  · have hmax : IsLocalMax (fun z : Space ↦ ‖normalSupport K z - p‖ ^ 2) (u : Space) := by
      apply Filter.Eventually.of_forall
      intro z
      change ‖normalSupport K z - p‖ ^ 2 ≤ ‖normalSupport K (u : Space) - p‖ ^ 2
      rw [hactive]
      exact pow_le_pow_left₀ (norm_nonneg _) (hball _ (normalSupport_mem K z)) 2
    have hzero := hmax.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub_const p).norm_sq
    have h := congrArg (fun A : Space →L[ℝ] ℝ ↦ A v) hzero
    simp only [two_smul, zero_apply] at h
    change ⟪normalSupport K (u : Space) - p, sphereCurvature K u v⟫_ℝ +
      ⟪normalSupport K (u : Space) - p, sphereCurvature K u v⟫_ℝ = 0 at h
    linarith
  · simp only [sphereCurvature, fderiv_zero_of_not_differentiableAt hd,
      zero_apply, inner_zero_right]

theorem sphereCurvature_apply_active_ball {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) {p : Space} {r : ℝ}
    (hball : ∀ x ∈ K, ‖x - p‖ ≤ r)
    (hactive : ‖normalSupport K (u : Space) - p‖ = r) :
    sphereCurvature K u (normalSupport K (u : Space) - p) = 0 := by
  let q := normalSupport K (u : Space) - p
  have h := (sphereCurvature_isPositive hKL u).isSymmetric q (sphereCurvature K u q)
  change ⟪sphereCurvature K u q, sphereCurvature K u q⟫_ℝ =
    ⟪q, sphereCurvature K u (sphereCurvature K u q)⟫_ℝ at h
  rw [sphereCurvature_inner_active_ball K u hball hactive] at h
  rw [real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.1 (sq_eq_zero_iff.1 h)

theorem augmentedCurvature_injective_of_det_ne_zero (K : ConvexBody Space) (u : UnitSphere)
    (hdet : curvatureDet K u ≠ 0) : Function.Injective (augmentedCurvature K u) := by
  apply LinearMap.ker_eq_bot.1
  by_contra hn
  exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 hn)

theorem active_ball_parallel_of_curvatureDet_ne_zero {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) {p : Space} {r : ℝ}
    (hball : ∀ x ∈ K, ‖x - p‖ ≤ r)
    (hactive : ‖normalSupport K (u : Space) - p‖ = r) (hdet : curvatureDet K u ≠ 0) :
    normalSupport K (u : Space) - p =
      ⟪(u : Space), normalSupport K (u : Space) - p⟫_ℝ • (u : Space) := by
  apply augmentedCurvature_injective_of_det_ne_zero K u hdet
  rw [map_smul, augmentedCurvature_apply_normal]
  simp only [augmentedCurvature, add_apply,
    sphereCurvature_apply_active_ball hKL u hball hactive, normalProjection_apply, zero_add]

/-- Positive area density at an active ball identifies its actual outward face point. -/
theorem normalSupport_eq_ball_face_of_curvatureDet_ne_zero {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere) (h0 : (0 : Space) ∈ K)
    {p : Space} {r : ℝ} (hp : ‖p‖ < r) (hball : ∀ x ∈ K, ‖x - p‖ ≤ r)
    (hactive : ‖normalSupport K (u : Space) - p‖ = r) (hdet : curvatureDet K u ≠ 0) :
    normalSupport K (u : Space) = p + r • (u : Space) := by
  let t := ⟪(u : Space), normalSupport K (u : Space) - p⟫_ℝ
  have hparallel : normalSupport K (u : Space) - p = t • (u : Space) :=
    active_ball_parallel_of_curvatureDet_ne_zero hKL u hball hactive hdet
  have ht : |t| = r := by
    rw [hparallel, norm_smul, Real.norm_eq_abs, u.norm_eq_one, mul_one] at hactive
    exact hactive
  have hsupport : 0 ≤ ⟪(u : Space), normalSupport K (u : Space)⟫_ℝ := by
    rw [inner_normalSupport]
    simpa only [inner_zero_right] using inner_le_support K (u : Space) h0
  have hip := real_inner_le_norm (u : Space) p
  rw [u.norm_eq_one, one_mul] at hip
  have htpos : 0 ≤ t := by
    by_contra! hneg
    rw [abs_of_neg hneg] at ht
    dsimp [t] at ht
    rw [inner_sub_right] at ht
    linarith
  rw [abs_of_nonneg htpos] at ht
  rw [ht] at hparallel
  exact sub_eq_iff_eq_add'.1 hparallel

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)
  {hne : (clippedOuter c.radius (range c.point)).Nonempty}

theorem normalSupport_clipped_has_active_ball (u : UnitSphere) :
    ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ = c.radius ∨
      ∃ i, ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1 := by
  let C := clippedOuterBody c.radius (range c.point) hne
  let x := normalSupport C (u : Space)
  have hx := (c.mem_clippedOuter_range_iff x).1 (normalSupport_mem C (u : Space))
  by_cases hR : ‖x‖ = c.radius
  · exact Or.inl hR
  right
  by_contra hbad
  have hstrict : ∀ i, ‖x - c.point i‖ < 1 := by
    intro i
    exact lt_of_le_of_ne (hx.2 i) (fun he ↦ hbad ⟨i, he⟩)
  let U : Set Space := {y | ‖y‖ < c.radius} ∩ ⋂ i, {y | ‖y - c.point i‖ < 1}
  have hU : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_iInter_of_finite fun i ↦ isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have hUx : x ∈ U := ⟨lt_of_le_of_ne hx.1 hR, mem_iInter.2 hstrict⟩
  have hUC : U ⊆ (C : Set Space) := by
    intro y hy
    apply (c.mem_clippedOuter_range_iff y).2
    exact ⟨hy.1.le, fun i ↦ (mem_iInter.1 hy.2 i).le⟩
  have hxint : x ∈ interior (C : Set Space) :=
    mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (hU.mem_nhds hUx) hUC)
  have hh := inner_lt_support_of_mem_interior C hxint u.norm_eq_one
  change ⟪(u : Space), normalSupport C (u : Space)⟫_ℝ < _ at hh
  rw [inner_normalSupport] at hh
  exact (lt_irrefl _ hh)

/-- The actual determinant vanishes everywhere outside the spherical face regions. -/
theorem curvatureDet_clipped_zero_off_faces (hR : 0 < c.radius) (u : UnitSphere)
    (huR : u ∉ c.radiusFaceNormals) (hu : ∀ i, u ∉ c.unitFaceNormals i) :
    curvatureDet (clippedOuterBody c.radius (range c.point) hne) u = 0 := by
  let C := clippedOuterBody c.radius (range c.point) hne
  have hR1 : c.radius < 1 := by nlinarith [c.radius_sq_le (by decide)]
  have hsum := clippedBodies_complement c.radius (range c.point) hne hR1.le
  have h0 : (0 : Space) ∈ C := (c.mem_clippedOuter_range_iff 0).2
    ⟨by simpa only [norm_zero] using hR.le, fun i ↦ by
      simpa only [zero_sub, norm_neg, c.on_sphere] using hR1.le⟩
  by_contra hd
  rcases c.normalSupport_clipped_has_active_ball (hne := hne) u with ha | ⟨i, ha⟩
  · have he := normalSupport_eq_ball_face_of_curvatureDet_ne_zero hsum u h0
      (show ‖(0 : Space)‖ < c.radius by simpa only [norm_zero] using hR)
      (fun y hy ↦ by simpa only [sub_zero] using clippedOuterBody_norm_le hy)
      (by simpa only [sub_zero] using ha) hd
    simp only [zero_add] at he
    apply huR
    change c.radius • (u : Space) ∈ C
    rw [← he]
    exact normalSupport_mem C (u : Space)
  · have he := normalSupport_eq_ball_face_of_curvatureDet_ne_zero hsum u h0
      (show ‖c.point i‖ < 1 by rw [c.on_sphere]; exact hR1)
      (fun y hy ↦ hy.2 _ ⟨i, rfl⟩) ha hd
    simp only [one_smul] at he
    apply hu i
    change c.point i + (u : Space) ∈ C
    rw [← he]
    exact normalSupport_mem C (u : Space)

end BalancedContacts

end BlaschkeLebesgue
