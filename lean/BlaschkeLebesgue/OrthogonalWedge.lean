module

public import BlaschkeLebesgue.ClippingCircleDerivative
public import BlaschkeLebesgue.LongitudeWedgeIntegral
public import BlaschkeLebesgue.CapLensCoordinates

/-! # Equatorial directions and normal wedges about an arbitrary axis -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

@[expose] def equatorPoint (a : AddCircle (2 * Real.pi)) : Space := heightLongitudePoint 0 a

@[fun_prop] theorem continuous_equatorPoint : Continuous equatorPoint :=
  continuous_heightLongitudePoint.comp (continuous_const.prodMk continuous_id)

theorem norm_equatorPoint (a : AddCircle (2 * Real.pi)) : ‖equatorPoint a‖ = 1 :=
  norm_heightLongitudePoint (by norm_num) a

theorem inner_coordinatePole_equatorPoint (a : AddCircle (2 * Real.pi)) :
    ⟪coordinatePole, equatorPoint a⟫_ℝ = 0 := by rw [inner_coordinatePole]; rfl

theorem inner_equatorPoint (a b : AddCircle (2 * Real.pi)) :
    ⟪equatorPoint a, equatorPoint b⟫_ℝ = Real.Angle.cos (a - b) := by
  have hc : Real.Angle.cos (a - b) =
      Real.Angle.cos a * Real.Angle.cos b + Real.Angle.sin a * Real.Angle.sin b := by
    have h (x y : Real.Angle) : (x - y).cos = x.cos * y.cos + x.sin * y.sin := by
      rw [sub_eq_add_neg, Real.Angle.cos_add, Real.Angle.cos_neg, Real.Angle.sin_neg]
      ring
    exact h a b
  simp [equatorPoint, heightLongitudePoint, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three, hc]
  ring

theorem heightLongitudePoint_decomposition (z : ℝ) (a : AddCircle (2 * Real.pi)) :
    heightLongitudePoint z a = z • coordinatePole + Real.sqrt (1 - z ^ 2) • equatorPoint a := by
  ext i
  fin_cases i <;> simp [heightLongitudePoint, equatorPoint, coordinatePole]

theorem axisProjection_coordinatePole (u : UnitSphere) :
    axisProjection coordinatePole (u : Space) =
      Real.sqrt (1 - ⟪coordinatePole, (u : Space)⟫_ℝ ^ 2) • equatorPoint (longitude u) := by
  have he := heightLongitudePoint_longitude u
  rw [heightLongitudePoint_decomposition] at he
  unfold axisProjection
  rw [← he]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_coordinatePole_equatorPoint, mul_zero, add_zero,
    real_inner_self_eq_norm_sq, norm_coordinatePole, one_pow, mul_one]
  module

theorem normalize_axisProjection_coordinatePole (u : UnitSphere)
    (hp : axisProjection coordinatePole (u : Space) ≠ 0) :
    NormedSpace.normalize (axisProjection coordinatePole (u : Space)) = equatorPoint (longitude u) := by
  have hn : Real.sqrt (1 - ⟪coordinatePole, (u : Space)⟫_ℝ ^ 2) > 0 := by
    have he : ‖axisProjection coordinatePole (u : Space)‖ =
        Real.sqrt (1 - ⟪coordinatePole, (u : Space)⟫_ℝ ^ 2) := by
      rw [axisProjection_coordinatePole, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), norm_equatorPoint, mul_one]
    exact he ▸ norm_pos_iff.2 hp
  rw [axisProjection_coordinatePole, NormedSpace.normalize_smul_of_pos hn,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_equatorPoint _)]

theorem isometry_axisProjection (e : Space ≃ₗᵢ[ℝ] Space) (k u : Space) :
    e (axisProjection k u) = axisProjection (e k) (e u) := by
  simp only [axisProjection, e.map_sub, e.map_smul, e.inner_map_map]

theorem isometry_normalize (e : Space ≃ₗᵢ[ℝ] Space) (u : Space) :
    e (NormedSpace.normalize u) = NormedSpace.normalize (e u) := by
  simp only [NormedSpace.normalize, e.map_smul, e.norm_map]

theorem normalize_axisProjection_eq_equator (e : Space ≃ₗᵢ[ℝ] Space) {k : Space}
    (hek : e k = coordinatePole) (u : UnitSphere) (hp : axisProjection k (u : Space) ≠ 0) :
    NormedSpace.normalize (axisProjection k (u : Space)) =
      e.symm (equatorPoint (longitude (sphereIsometry e u))) := by
  apply e.injective
  rw [e.apply_symm_apply, isometry_normalize, isometry_axisProjection, hek]
  apply normalize_axisProjection_coordinatePole (sphereIsometry e u)
  change axisProjection coordinatePole (e (u : Space)) ≠ 0
  rw [← hek, ← isometry_axisProjection]
  exact fun h ↦ hp (e.injective (by simpa only [e.map_zero] using h))

@[expose] def orthogonalWedge (e : Space ≃ₗᵢ[ℝ] Space) (a b : ℝ)
    (s : Set (AddCircle (2 * Real.pi))) : Set UnitSphere :=
  sphereIsometry e ⁻¹' longitudeWedge a b s

theorem mem_orthogonalWedge (e : Space ≃ₗᵢ[ℝ] Space) {k : Space} (hek : e k = coordinatePole)
    (a b : ℝ) (s : Set (AddCircle (2 * Real.pi))) (u : UnitSphere) :
    u ∈ orthogonalWedge e a b s ↔
      ⟪k, (u : Space)⟫_ℝ ∈ Icc a b ∧ longitude (sphereIsometry e u) ∈ s := by
  change (⟪coordinatePole, e (u : Space)⟫_ℝ ∈ Icc a b ∧ _) ↔ _
  rw [← hek, e.inner_map_map]
  rfl

theorem measurableSet_orthogonalWedge (e : Space ≃ₗᵢ[ℝ] Space) (a b : ℝ)
    {s : Set (AddCircle (2 * Real.pi))} (hs : MeasurableSet s) :
    MeasurableSet (orthogonalWedge e a b s) :=
  (measurableSet_longitudeWedge a b hs).preimage (sphereIsometry e).measurable

theorem integral_orthogonalWedge_circleDensity (e : Space ≃ₗᵢ[ℝ] Space) {k : Space}
    (hek : e k = coordinatePole) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b)
    {s : Set (AddCircle (2 * Real.pi))} (hs : MeasurableSet s) (r : ℝ) :
    (∫ u in orthogonalWedge e a b s,
      r / Real.sqrt (1 - ⟪k, (u : Space)⟫_ℝ ^ 2) ∂sphereMeasure) =
      r * volume.real s * (Real.arcsin b - Real.arcsin a) := by
  have h := (sphereIsometry_measurePreserving e).setIntegral_preimage_emb
    (sphereIsometry e).measurableEmbedding
    (fun u : UnitSphere ↦ r / Real.sqrt (1 - ⟪coordinatePole, (u : Space)⟫_ℝ ^ 2))
    (longitudeWedge a b s)
  have he (u : UnitSphere) : ⟪coordinatePole, (sphereIsometry e u : Space)⟫_ℝ =
      ⟪k, (u : Space)⟫_ℝ := by rw [sphereIsometry_val, ← hek, e.inner_map_map]
  simp_rw [he] at h
  exact h.trans (integral_longitudeWedge_circleDensity ha hb hab hs r)

theorem integral_orthogonalWedge_height (e : Space ≃ₗᵢ[ℝ] Space) {k : Space}
    (hek : e k = coordinatePole) (a b : ℝ) (s : Set (AddCircle (2 * Real.pi))) (f : ℝ → ℝ) :
    (∫ u in orthogonalWedge e a b s, f ⟪k, (u : Space)⟫_ℝ ∂sphereMeasure) =
      ∫ u in longitudeWedge a b s, f ⟪coordinatePole, (u : Space)⟫_ℝ ∂sphereMeasure := by
  have h := (sphereIsometry_measurePreserving e).setIntegral_preimage_emb
    (sphereIsometry e).measurableEmbedding
    (fun u : UnitSphere ↦ f ⟪coordinatePole, (u : Space)⟫_ℝ) (longitudeWedge a b s)
  have he (u : UnitSphere) : ⟪coordinatePole, (sphereIsometry e u : Space)⟫_ℝ =
      ⟪k, (u : Space)⟫_ℝ := by rw [sphereIsometry_val, ← hek, e.inner_map_map]
  simpa only [he, orthogonalWedge] using h

theorem sphereMeasure_longitude_preimage {s : Set (AddCircle (2 * Real.pi))}
    (hs : MeasurableSet s) : sphereMeasure (longitude ⁻¹' s) = 2 * volume s := by
  have h := congrArg (fun μ : Measure (AddCircle (2 * Real.pi)) ↦ μ s)
    (longitudeCapMeasure_eq_smul (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1))
  rw [longitudeCapMeasure, sphereCap_eq_univ_of_le_neg_one norm_coordinatePole (le_refl (-1 : ℝ)),
    Measure.restrict_univ, Measure.map_apply measurable_longitude hs, Measure.smul_apply, smul_eq_mul] at h
  norm_num at h ⊢
  exact h

theorem sphereMeasure_orthogonal_longitude_null (e : Space ≃ₗᵢ[ℝ] Space)
    {s : Set (AddCircle (2 * Real.pi))} (hs : MeasurableSet s) (hzero : volume s = 0) :
    sphereMeasure {u | longitude (sphereIsometry e u) ∈ s} = 0 := by
  have h := (sphereIsometry_measurePreserving e).measure_preimage
    (hs.preimage measurable_longitude).nullMeasurableSet
  change sphereMeasure (sphereIsometry e ⁻¹' (longitude ⁻¹' s)) = 0
  rw [h, sphereMeasure_longitude_preimage hs, hzero, mul_zero]

end BlaschkeLebesgue
