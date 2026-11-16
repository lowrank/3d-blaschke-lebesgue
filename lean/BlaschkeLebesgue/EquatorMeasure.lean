module

public import BlaschkeLebesgue.OrthogonalWedge

/-! # Lengths and null boundaries of actual equatorial arcs -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

theorem volume_angle_cos_eq (q : ℝ) :
    volume {a : AddCircle (2 * Real.pi) | Real.Angle.cos a = q} = 0 := by
  let : NullSingletonClass (volume : Measure (AddCircle (2 * Real.pi))) := ⟨fun a ↦ by
    simpa only [closedBall_zero, mul_zero, min_eq_right (by positivity : 0 ≤ 2 * Real.pi),
      ENNReal.ofReal_zero] using AddCircle.volume_closedBall (2 * Real.pi) (x := a) 0⟩
  by_cases h : ∃ b : AddCircle (2 * Real.pi), Real.Angle.cos b = q
  · obtain ⟨b, hb⟩ := h
    have he : {a : AddCircle (2 * Real.pi) | Real.Angle.cos a = q} = {b, -b} := by
      ext a
      change Real.Angle.cos a = q ↔ a = b ∨ a = -b
      rw [← hb]
      exact Real.Angle.cos_eq_iff_eq_or_eq_neg
    rw [he]
    exact ((Set.finite_singleton (-b)).insert b).measure_zero volume
  · have he : {a : AddCircle (2 * Real.pi) | Real.Angle.cos a = q} = ∅ := by
      exact eq_empty_iff_forall_notMem.2 fun a ha ↦ h ⟨a, ha⟩
    rw [he, measure_empty]

theorem volume_angle_cos_sub_ge (q : ℝ) (b : AddCircle (2 * Real.pi)) :
    volume {a : AddCircle (2 * Real.pi) | q ≤ Real.Angle.cos (a - b)} =
      ENNReal.ofReal (2 * Real.arccos q) := by
  simp_rw [sub_eq_add_neg]
  change volume ((fun a ↦ a + -b) ⁻¹' {a : AddCircle (2 * Real.pi) | q ≤ Real.Angle.cos a}) = _
  rw [measure_preimage_add_right, volume_angle_cos_ge]

theorem volume_angle_cos_sub_eq (q : ℝ) (b : AddCircle (2 * Real.pi)) :
    volume {a : AddCircle (2 * Real.pi) | Real.Angle.cos (a - b) = q} = 0 := by
  simp_rw [sub_eq_add_neg]
  change volume ((fun a ↦ a + -b) ⁻¹' {a : AddCircle (2 * Real.pi) | Real.Angle.cos a = q}) = _
  rw [measure_preimage_add_right, volume_angle_cos_eq]

theorem equatorPoint_longitude {v : Space} (hv : ‖v‖ = 1) (hp : ⟪coordinatePole, v⟫_ℝ = 0) :
    equatorPoint (longitude ⟨v, by simpa only [mem_sphere, dist_zero_right] using hv⟩) = v := by
  have h := heightLongitudePoint_longitude
    (⟨v, by simpa only [mem_sphere, dist_zero_right] using hv⟩ : UnitSphere)
  simpa only [hp, equatorPoint] using h

theorem volume_equator_inner_ge {v : Space} (hv : ‖v‖ = 1)
    (hp : ⟪coordinatePole, v⟫_ℝ = 0) (q : ℝ) :
    volume {a : AddCircle (2 * Real.pi) | q ≤ ⟪v, equatorPoint a⟫_ℝ} =
      ENNReal.ofReal (2 * Real.arccos q) := by
  let b := longitude (⟨v, by simpa only [mem_sphere, dist_zero_right] using hv⟩ : UnitSphere)
  have he (a : AddCircle (2 * Real.pi)) : ⟪v, equatorPoint a⟫_ℝ = Real.Angle.cos (a - b) := by
    rw [real_inner_comm, ← equatorPoint_longitude hv hp, inner_equatorPoint]
  simp_rw [he]
  exact volume_angle_cos_sub_ge q b

theorem volume_equator_inner_eq {v : Space} (hv : ‖v‖ = 1)
    (hp : ⟪coordinatePole, v⟫_ℝ = 0) (q : ℝ) :
    volume {a : AddCircle (2 * Real.pi) | ⟪v, equatorPoint a⟫_ℝ = q} = 0 := by
  let b := longitude (⟨v, by simpa only [mem_sphere, dist_zero_right] using hv⟩ : UnitSphere)
  have he (a : AddCircle (2 * Real.pi)) : ⟪v, equatorPoint a⟫_ℝ = Real.Angle.cos (a - b) := by
    rw [real_inner_comm, ← equatorPoint_longitude hv hp, inner_equatorPoint]
  simp_rw [he]
  exact volume_angle_cos_sub_eq q b

theorem volume_equator_inner_gt {v : Space} (hv : ‖v‖ = 1)
    (hp : ⟪coordinatePole, v⟫_ℝ = 0) (q : ℝ) :
    volume {a : AddCircle (2 * Real.pi) | q < ⟪v, equatorPoint a⟫_ℝ} =
      ENNReal.ofReal (2 * Real.arccos q) := by
  have hn : ∀ᵐ a : AddCircle (2 * Real.pi), ⟪v, equatorPoint a⟫_ℝ ≠ q := by
    rw [ae_iff]
    simpa only [not_not] using volume_equator_inner_eq hv hp q
  rw [← volume_equator_inner_ge hv hp q]
  apply measure_congr
  filter_upwards [hn] with a ha
  exact propext (lt_iff_le_and_ne.trans (and_iff_left ha.symm))

theorem volume_real_equator_inner_ge {v : Space} (hv : ‖v‖ = 1)
    (hp : ⟪coordinatePole, v⟫_ℝ = 0) (q : ℝ) :
    volume.real {a : AddCircle (2 * Real.pi) | q ≤ ⟪v, equatorPoint a⟫_ℝ} =
      2 * Real.arccos q := by
  rw [measureReal_def, volume_equator_inner_ge hv hp q,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (Real.arccos_nonneg q))]

theorem sphereMeasure_normal_direction_level (e : Space ≃ₗᵢ[ℝ] Space) {k v : Space}
    (hek : e k = coordinatePole) (hv : ‖v‖ = 1) (hkv : ⟪k, v⟫_ℝ = 0) (q : ℝ) :
    sphereMeasure {u : UnitSphere | axisProjection k (u : Space) ≠ 0 ∧
      ⟪v, NormedSpace.normalize (axisProjection k (u : Space))⟫_ℝ = q} = 0 := by
  have hv' : ‖e v‖ = 1 := by rw [e.norm_map, hv]
  have hp' : ⟪coordinatePole, e v⟫_ℝ = 0 := by rw [← hek, e.inner_map_map, hkv]
  have hc : Continuous (fun a : AddCircle (2 * Real.pi) ↦ ⟪e v, equatorPoint a⟫_ℝ) := by fun_prop
  have hz := sphereMeasure_orthogonal_longitude_null e
    (isClosed_eq hc continuous_const).measurableSet (volume_equator_inner_eq hv' hp' q)
  apply measure_mono_null _ hz
  intro u hu
  obtain ⟨hup, hui⟩ := hu
  change ⟪e v, equatorPoint (longitude (sphereIsometry e u))⟫_ℝ = q
  rw [normalize_axisProjection_eq_equator e hek u hup] at hui
  rw [← e.apply_symm_apply (equatorPoint (longitude (sphereIsometry e u))), e.inner_map_map]
  exact hui

end BlaschkeLebesgue
