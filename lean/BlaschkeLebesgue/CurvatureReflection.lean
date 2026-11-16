module

public import BlaschkeLebesgue.CircleSupportRegion
public import BlaschkeLebesgue.AntipodalIntegration

/-! # Pointwise curvature identities for reflection and complementation -/

public noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem normalSupport_reflectBody_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {x : Space} (hx : x ≠ 0) :
    normalSupport (reflectBody K) x = -normalSupport K (-x) := by
  simp only [normalSupport, NormedSpace.normalize_neg,
    supportPoint_reflectBody_of_ball_sum hKL (NormedSpace.norm_normalize hx)]

theorem hasFDerivAt_normalSupport_reflectBody {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {x : Space} (hx : x ≠ 0) {A : Space →L[ℝ] Space}
    (hd : HasFDerivAt (normalSupport K) A x) :
    HasFDerivAt (normalSupport (reflectBody K)) A (-x) := by
  have hd' : HasFDerivAt (normalSupport K) A (-(-x)) := by simpa using hd
  have h := (hd'.comp (-x) (hasFDerivAt_id (-x)).neg).neg
  have hA : -(A.comp (-(ContinuousLinearMap.id ℝ Space))) = A := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  rw [hA] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds (neg_ne_zero.mpr hx)] with y hy
  exact normalSupport_reflectBody_of_ball_sum hKL hy

theorem curvatureDet_reflectBody_at {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere)
    (hd : DifferentiableAt ℝ (normalSupport K) (u : Space)) :
    curvatureDet (reflectBody K) (sphereAntipode u) = curvatureDet K u := by
  have href := hasFDerivAt_normalSupport_reflectBody hKL u.ne_zero hd.hasFDerivAt
  have heq : sphereCurvature (reflectBody K) (sphereAntipode u) = sphereCurvature K u :=
    href.fderiv
  have hnormal : normalProjection (sphereAntipode u : Space) = normalProjection (u : Space) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [normalProjection_apply, sphereAntipode_val]
  simp only [curvatureDet, augmentedCurvature, heq, hnormal]

theorem curvatureDet_complement_at {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (u : UnitSphere)
    (hd : DifferentiableAt ℝ (normalSupport K) (u : Space)) :
    curvatureDet L u = 1 - curvatureTrace K u + curvatureDet K u := by
  have hu : sphereCurvature L u = tangentProjection u - sphereCurvature K u :=
    (normalSupport_complement_derivative hKL u.norm_eq_one hd.hasFDerivAt).fderiv
  have h := det_tangent_smul_shift u (sphereCurvature K u) (sphereCurvature_apply_normal K u)
    (sphereCurvature_apply_tangent hKL u) (-1) 1
  rw [curvatureDet, augmentedCurvature, hu]
  have he : tangentProjection u - sphereCurvature K u + normalProjection u =
      (-1 : ℝ) • sphereCurvature K u + (1 : ℝ) • tangentProjection u + normalProjection u := by
    module
  rw [he, h]
  change (-1 : ℝ) ^ 2 * curvatureDet K u + (-1 : ℝ) * 1 * curvatureTrace K u + 1 ^ 2 = _
  ring

namespace BalancedContacts.Opposite

/-- On every verified open circle-support region, the actual forced inner
body's opposite curvature determinant is one minus the circle radius term. -/
theorem clipped_circle_complement_det (c : BalancedContacts 4 Space)
    (ha : edgeBudget c < 1)
    {hne : (clippedOuter c.radius (Set.range c.point)).Nonempty} (hbound : c.radius ≤ 1)
    (n : UnitSphere) (hcone : |⟪firstAxis c, (n : Space)⟫_ℝ| < ‖firstEdge c‖ / 2)
    (hR : ‖circleCandidate c n‖ < c.radius)
    (h2 : ‖circleCandidate c n - c.point 2‖ < 1)
    (h3 : ‖circleCandidate c n - c.point 3‖ < 1) :
    curvatureDet (clippedInnerBody c.radius (Set.range c.point) hne hbound) (sphereAntipode n) =
      1 - circleRadius c / Real.sqrt (1 - ⟪firstAxis c, (n : Space)⟫_ℝ ^ 2) := by
  let C := clippedOuterBody c.radius (Set.range c.point) hne
  let D := clippedInnerBody c.radius (Set.range c.point) hne hbound
  have hCD : C + reflectBody D = unitBallBody :=
    clippedBodies_complement c.radius (Set.range c.point) hne hbound
  have hd := hasFDerivAt_normalSupport_clipped_circle c ha (hne := hne)
    n.norm_eq_one hcone hR h2 h3
  have hD := normalSupport_complement_derivative hCD n.norm_eq_one hd
  have hcurv := clipped_circle_curvature c ha (hne := hne) n hcone hR h2 h3
  have href := curvatureDet_reflectBody_at (show reflectBody D + C = unitBallBody by
    rw [add_comm]; exact hCD) n hD.differentiableAt
  rw [reflectBody_reflectBody] at href
  change curvatureDet D (sphereAntipode n) = _
  rw [href, curvatureDet_complement_at hCD n hd.differentiableAt]
  rw [hcurv.1, hcurv.2, add_zero]

end BalancedContacts.Opposite
end BlaschkeLebesgue
