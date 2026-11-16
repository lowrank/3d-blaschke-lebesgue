module

public import BlaschkeLebesgue.RadialVolume
public import BlaschkeLebesgue.RadialGeometry
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Spherical caps and their solid cones

Spherical cap measure is three times the ordinary volume of the cone cut out
inside the unit ball. This identifies the spherical measure used in the radial
integral with a concrete Euclidean volume and proves its rotation invariance.
-/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace Pointwise

namespace BlaschkeLebesgue

/-- A cap as a measurable subset of the unit sphere. -/
@[expose] def sphereCap (u : Space) (c : ℝ) : Set UnitSphere :=
  {v | c ≤ ⟪u, (v : Space)⟫_ℝ}

theorem measurableSet_sphereCap (u : Space) (c : ℝ) : MeasurableSet (sphereCap u c) :=
  isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
    |>.measurableSet

theorem mem_sphereCap_iff {u : Space} {c : ℝ} {v : UnitSphere} :
    v ∈ sphereCap u c ↔ (v : Space) ∈ sphericalCap u c := by
  simp only [sphereCap, sphericalCap, mem_ofPred_eq, UnitSphere.norm_eq_one, true_and]

/-- The closed solid cone over a spherical cap, truncated at radius one. -/
@[expose] def capCone (u : Space) (c : ℝ) : Set Space :=
  {x | ‖x‖ ≤ 1 ∧ c * ‖x‖ ≤ ⟪u, x⟫_ℝ}

theorem isClosed_capCone (u : Space) (c : ℝ) : IsClosed (capCone u c) :=
  (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le (continuous_const.mul continuous_norm) (continuous_const.inner continuous_id))

theorem sphericalCap_cone_image (u : Space) (c : ℝ) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' sphereCap u c) =
      capCone u c \ (sphere (0 : Space) 1 ∪ {0}) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, rfl⟩
    have hn : ‖r • (v : Space)‖ = r := by
      simp [norm_smul, abs_of_pos hr.1]
    refine ⟨⟨by simpa only [hn] using hr.2.le, ?_⟩, ?_⟩
    · change c * ‖r • (v : Space)‖ ≤ _
      rw [hn, inner_smul_right]
      simpa only [mul_comm c r] using mul_le_mul_of_nonneg_left hv hr.1.le
    · simp only [mem_union, mem_sphere, dist_zero_right, mem_singleton_iff, not_or]
      exact ⟨by rw [hn]; exact hr.2.ne,
        by intro h; have := hn; simp [h] at this; linarith [hr.1]⟩
  · rintro ⟨hx, hboundary⟩
    have hx0 : x ≠ 0 := fun h ↦ hboundary (Or.inr h)
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hn1 : ‖x‖ < 1 := lt_of_le_of_ne hx.1 (fun h ↦ hboundary
      (Or.inl (by simpa only [mem_sphere, dist_zero_right] using h)))
    let v : UnitSphere := ⟨‖x‖⁻¹ • x, by
      simp [norm_smul, hn.ne']⟩
    refine ⟨‖x‖, ⟨hn, hn1⟩, v, ⟨v, ?_, rfl⟩, ?_⟩
    · change c ≤ ⟪u, ‖x‖⁻¹ • x⟫_ℝ
      rw [inner_smul_right]
      have h := mul_le_mul_of_nonneg_left hx.2 (inv_nonneg.2 hn.le)
      simpa [← mul_assoc, hn.ne', mul_comm, mul_left_comm] using h
    · simp [v, smul_smul, hn.ne']

theorem sphereMeasure_capCone (u : Space) (c : ℝ) :
    sphereMeasure (sphereCap u c) = 3 * volume (capCone u c) := by
  rw [sphereMeasure, Measure.toSphere_apply' _ (measurableSet_sphereCap u c),
    sphericalCap_cone_image, measure_sdiff_null]
  · simp [Space]
  · exact measure_union_null (Measure.addHaar_sphere volume _ _) (measure_singleton _)

/-- Orthogonal changes of coordinates preserve the cone and hence its cap measure. -/
theorem capCone_preimage_isometry (e : Space ≃ₗᵢ[ℝ] Space) (u : Space) (c : ℝ) :
    e ⁻¹' capCone (e u) c = capCone u c := by
  ext x
  simp only [capCone, mem_preimage, mem_ofPred_eq, e.norm_map, e.inner_map_map]

theorem sphereMeasure_cap_isometry (e : Space ≃ₗᵢ[ℝ] Space) (u : Space) (c : ℝ) :
    sphereMeasure (sphereCap (e u) c) = sphereMeasure (sphereCap u c) := by
  rw [sphereMeasure_capCone, sphereMeasure_capCone,
    ← capCone_preimage_isometry e u c,
    e.measurePreserving.measure_preimage (isClosed_capCone _ _).measurableSet.nullMeasurableSet]

end BlaschkeLebesgue
