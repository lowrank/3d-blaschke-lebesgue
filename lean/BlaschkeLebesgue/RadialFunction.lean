module

public import BlaschkeLebesgue.Basic
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The radial function of an actual convex body

For a body containing the origin in its interior, the reciprocal of its Minkowski
functional is the radial boundary distance in every unit direction. Compactness
gives positivity, and Hahn–Banach separation gives a supporting unit normal at
each radial boundary point, without any smoothness hypothesis.
-/

public noncomputable section

open scoped InnerProductSpace Topology

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On unit vectors, the distance from the origin to the body's boundary. -/
@[expose] def radialFunction (K : ConvexBody E) (u : E) : ℝ :=
  (gauge (K : Set E) u)⁻¹

theorem body_gauge_pos {K : ConvexBody E} (h0 : (0 : E) ∈ interior (K : Set E))
    {u : E} (hu : u ≠ 0) : 0 < gauge (K : Set E) u :=
  (gauge_pos (absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 h0))
    (K.isCompact.isVonNBounded ℝ)).2 hu

theorem radialFunction_pos {K : ConvexBody E} (h0 : (0 : E) ∈ interior (K : Set E))
    {u : E} (hu : u ≠ 0) : 0 < radialFunction K u :=
  inv_pos.2 (body_gauge_pos h0 hu)

/-- Membership along a nonnegative ray is exactly the radial interval. -/
theorem smul_mem_iff_le_radialFunction {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) {u : E} (hu : u ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) : r • u ∈ K ↔ r ≤ radialFunction K u := by
  have hmem := gauge_le_one_iff_mem_closure K.convex (mem_interior_iff_mem_nhds.1 h0)
    (x := r • u)
  rw [K.isClosed.closure_eq, gauge_smul_of_nonneg hr] at hmem
  simp only [SetLike.mem_coe, smul_eq_mul] at hmem
  rw [← hmem]
  rw [radialFunction, ← one_div]
  exact (le_div_iff₀ (body_gauge_pos h0 hu)).symm

/-- Interior membership along a ray is the strict radial interval. -/
theorem smul_mem_interior_iff_lt_radialFunction {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) {u : E} (hu : u ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    r • u ∈ interior (K : Set E) ↔ r < radialFunction K u := by
  have hmem := gauge_lt_one_iff_mem_interior K.convex
    (mem_interior_iff_mem_nhds.1 h0) (x := r • u)
  rw [gauge_smul_of_nonneg hr, smul_eq_mul] at hmem
  rw [← hmem, radialFunction, ← one_div]
  exact (lt_div_iff₀ (body_gauge_pos h0 hu)).symm

theorem radialFunction_smul_mem {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) {u : E} (hu : u ≠ 0) :
    radialFunction K u • u ∈ K :=
  (smul_mem_iff_le_radialFunction h0 hu (radialFunction_pos h0 hu).le).2 le_rfl

theorem radialFunction_smul_mem_frontier {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) {u : E} (hu : u ≠ 0) :
    radialFunction K u • u ∈ frontier (K : Set E) := by
  apply (gauge_eq_one_iff_mem_frontier K.convex (mem_interior_iff_mem_nhds.1 h0)).1
  rw [gauge_smul_of_nonneg (radialFunction_pos h0 hu).le]
  exact inv_mul_cancel₀ (body_gauge_pos h0 hu).ne'

theorem continuousOn_radialFunction {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ContinuousOn (radialFunction K) ({0}ᶜ : Set E) := by
  exact (continuous_gauge K.convex (mem_interior_iff_mem_nhds.1 h0)).continuousOn.inv₀
    (fun _ hu ↦ (body_gauge_pos h0 hu).ne')

theorem radialFunction_le_of_norm_le {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    {u : E} (hu : ‖u‖ = 1) : radialFunction K u ≤ R := by
  have hu' : u ≠ 0 := by intro h; simp [h] at hu
  have h := hR _ (radialFunction_smul_mem h0 hu')
  simpa [norm_smul, hu, abs_of_pos (radialFunction_pos h0 hu')] using h

theorem le_radialFunction_of_innerBall {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall (0 : E) r ⊆ (K : Set E)) {u : E} (hu : ‖u‖ = 1) :
    r ≤ radialFunction K u := by
  apply (smul_mem_iff_le_radialFunction h0 (by intro h; simp [h] at hu) hr).1
  apply hball
  simp [norm_smul, hu, abs_of_nonneg hr]

theorem radialFunction_eq_of_contact {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ R) {u : E} (hu : ‖u‖ = 1) (hx : R • u ∈ K) :
    radialFunction K u = R := by
  apply le_antisymm (radialFunction_le_of_norm_le h0 hbound hu)
  exact (smul_mem_iff_le_radialFunction h0 (by intro h; simp [h] at hu) hR).1 hx

/-- Every boundary point has a supporting unit normal, including nonsmooth points. -/
theorem exists_supporting_unit_normal [CompleteSpace E] {K : ConvexBody E}
    (hint : (interior (K : Set E)).Nonempty) {x : E} (hx : x ∈ frontier (K : Set E)) :
    ∃ n : E, ‖n‖ = 1 ∧ ⟪n, x⟫_ℝ = support K n := by
  obtain ⟨f, hf, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point
    K.convex hx.2 hint
  let v := (InnerProductSpace.toDual ℝ E).symm f
  have hv : v ≠ 0 := by
    intro h
    have hh := congrArg (InnerProductSpace.toDual ℝ E) h
    exact hf (by simpa [v] using hh)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  let n := ‖v‖⁻¹ • v
  refine ⟨n, by simp [n, norm_smul, hvpos.ne'], le_antisymm ?_ ?_⟩
  · exact inner_le_support K n
      (by simpa only [K.isClosed.closure_eq, SetLike.mem_coe] using hx.1)
  · apply (support_le_iff _ _ _).2
    intro y hy
    have hh := mul_le_mul_of_nonneg_left (hmax y hy) (inv_nonneg.2 hvpos.le)
    simpa [n, v, real_inner_smul_left] using hh

/-- A radial boundary point comes with an actual supporting unit normal. -/
theorem radialFunction_supporting_normal [CompleteSpace E] {K : ConvexBody E}
    (h0 : (0 : E) ∈ interior (K : Set E)) {u : E} (hu : u ≠ 0) :
    ∃ n : E, ‖n‖ = 1 ∧
      ⟪n, radialFunction K u • u⟫_ℝ = support K n :=
  exists_supporting_unit_normal ⟨0, h0⟩ (radialFunction_smul_mem_frontier h0 hu)

end BlaschkeLebesgue
