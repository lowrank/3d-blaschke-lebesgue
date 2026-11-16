module

public import BlaschkeLebesgue.ClippingCircle
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The two corner angles at a clipped vertex

Project the other two sphere normals into a face's tangent plane and take
their actual Euclidean angle. The resulting angles are exactly the manuscript's
`U` and `V`, including the choice of supplementary angle.
-/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace ClippingCircle

@[expose] def faceTangent (u v : E) : E := v - ⟪u, v⟫_ℝ • u

@[expose] def faceAngle (u v w : E) : ℝ :=
  InnerProductGeometry.angle (faceTangent u v) (faceTangent u w)

theorem faceTangent_inner {u v w : E} (hu : ‖u‖ = 1) :
    ⟪faceTangent u v, faceTangent u w⟫_ℝ =
      ⟪v, w⟫_ℝ - ⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ := by
  simp only [faceTangent, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
  rw [real_inner_comm v u]
  ring

theorem faceTangent_norm_sq {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖faceTangent u v‖ ^ 2 = 1 - ⟪u, v⟫_ℝ ^ 2 := by
  have h := faceTangent_inner (u := u) (v := v) (w := v) hu
  simpa only [real_inner_self_eq_norm_sq, hv, one_pow, pow_two, one_mul] using h

theorem faceTangent_norm {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖faceTangent u v‖ = Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by
  rw [← faceTangent_norm_sq hu hv, Real.sqrt_sq (norm_nonneg _)]

theorem faceTangent_norm_unit_pair {u v : E} {s : ℝ} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 1 - s ^ 2 / 2) (hs : 0 ≤ s) :
    ‖faceTangent u v‖ = s * Real.sqrt (1 - s ^ 2 / 4) := by
  rw [faceTangent_norm hu hv, huv,
    show 1 - (1 - s ^ 2 / 2) ^ 2 = s ^ 2 * (1 - s ^ 2 / 4) by ring,
    Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

theorem faceTangent_norm_radius_pair {u v : E} {R : ℝ} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 1 / (2 * R)) :
    ‖faceTangent u v‖ = radius R := by
  rw [faceTangent_norm hu hv, huv, radius]
  congr 1
  ring

theorem unit_corner_cos {u v w : E} {R s : ℝ} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (huv : ⟪u, v⟫_ℝ = 1 - s ^ 2 / 2)
    (huw : ⟪u, w⟫_ℝ = 1 / (2 * R)) (hvw : ⟪v, w⟫_ℝ = 1 / (2 * R))
    (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    ⟪faceTangent u v, faceTangent u w⟫_ℝ /
        (‖faceTangent u v‖ * ‖faceTangent u w‖) =
      s / (4 * R * Real.sqrt (1 - s ^ 2 / 4) * radius R) := by
  have hR0 : R ≠ 0 := by linarith
  have hr : 0 < Real.sqrt (1 - s ^ 2 / 4) := Real.sqrt_pos.2 (by nlinarith)
  have hk := radius_pos hR
  rw [faceTangent_inner hu, huv, huw, hvw,
    faceTangent_norm_unit_pair hu hv huv hs.le,
    faceTangent_norm_radius_pair hu hw huw]
  field_simp
  ring

theorem radius_corner_cos {u v w : E} {R s : ℝ} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (huv : ⟪u, v⟫_ℝ = 1 - s ^ 2 / 2)
    (huw : ⟪u, w⟫_ℝ = 1 / (2 * R)) (hvw : ⟪v, w⟫_ℝ = 1 / (2 * R))
    (hR : 1 / 2 < R) :
    ⟪faceTangent w u, faceTangent w v⟫_ℝ /
        (‖faceTangent w u‖ * ‖faceTangent w v‖) =
      1 - s ^ 2 / (2 * radius R ^ 2) := by
  have hR0 : R ≠ 0 := by linarith
  have hk := radius_pos hR
  have hwu : ⟪w, u⟫_ℝ = 1 / (2 * R) := (real_inner_comm _ _).trans huw
  have hwv : ⟪w, v⟫_ℝ = 1 / (2 * R) := (real_inner_comm _ _).trans hvw
  rw [faceTangent_inner hw, huv, hwu, hwv,
    faceTangent_norm_radius_pair hw hu hwu, faceTangent_norm_radius_pair hw hv hwv]
  have hnum : 1 - s ^ 2 / 2 - 1 / (2 * R) * (1 / (2 * R)) = radius R ^ 2 - s ^ 2 / 2 := by
    rw [radius_sq hR]
    field_simp
    ring
  rw [hnum]
  field_simp

theorem unit_corner_angle {u v w : E} {R s : ℝ} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (huv : ⟪u, v⟫_ℝ = 1 - s ^ 2 / 2)
    (huw : ⟪u, w⟫_ℝ = 1 / (2 * R)) (hvw : ⟪v, w⟫_ℝ = 1 / (2 * R))
    (hR : 1 / 2 < R) (hs : 0 < s) (hs1 : s ≤ 1) :
    faceAngle u v w = Real.arccos (s / (4 * R * Real.sqrt (1 - s ^ 2 / 4) * radius R)) := by
  rw [faceAngle, InnerProductGeometry.angle, unit_corner_cos hu hv hw huv huw hvw hR hs hs1]

theorem radius_corner_angle {u v w : E} {R s : ℝ} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (huv : ⟪u, v⟫_ℝ = 1 - s ^ 2 / 2)
    (huw : ⟪u, w⟫_ℝ = 1 / (2 * R)) (hvw : ⟪v, w⟫_ℝ = 1 / (2 * R))
    (hR : 1 / 2 < R) :
    faceAngle w u v = Real.arccos (1 - s ^ 2 / (2 * radius R ^ 2)) := by
  rw [faceAngle, InnerProductGeometry.angle, radius_corner_cos hu hv hw huv huw hvw hR]

end ClippingCircle

namespace BalancedContacts

variable {n : ℕ} (c : BalancedContacts n E)

theorem clipped_vertex_radius_normal_norm (hR : 0 < c.radius) {x : E}
    (hx : ‖x‖ = c.radius) : ‖c.radius⁻¹ • x‖ = 1 := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, hx, inv_mul_cancel₀ hR.ne']

theorem clipped_vertex_unit_radius_inner (hR : 0 < c.radius) {i : Fin n} {x : E}
    (hx : ‖x‖ = c.radius) (hi : ‖x - c.point i‖ = 1) :
    ⟪x - c.point i, c.radius⁻¹ • x⟫_ℝ = 1 / (2 * c.radius) := by
  have hp : ⟪c.point i, x⟫_ℝ = c.radius ^ 2 - 1 / 2 :=
    (real_inner_comm _ _).trans (c.clippingCircle_inner_contact hx hi)
  simp only [real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq, hx, hp]
  field_simp
  ring

theorem clipped_vertex_unit_unit_inner {i j : Fin n} {x : E}
    (hi : ‖x - c.point i‖ = 1) (hj : ‖x - c.point j‖ = 1) :
    ⟪x - c.point i, x - c.point j⟫_ℝ = 1 - ‖c.point i - c.point j‖ ^ 2 / 2 := by
  have hsub : (x - c.point i) - (x - c.point j) = c.point j - c.point i := by abel
  have h := norm_sub_sq_real (x - c.point i) (x - c.point j)
  rw [hsub, norm_sub_rev, hi, hj] at h
  nlinarith

/-- The actual tangent-plane angle on either unit face is the manuscript's `U`. -/
theorem clipped_vertex_unit_face_angle (hR : 1 / 2 < c.radius) {i j : Fin n} {x : E}
    (hx : ‖x‖ = c.radius) (hi : ‖x - c.point i‖ = 1) (hj : ‖x - c.point j‖ = 1)
    (hs : 0 < ‖c.point i - c.point j‖) :
    ClippingCircle.faceAngle (x - c.point i) (x - c.point j) (c.radius⁻¹ • x) =
      Real.arccos (‖c.point i - c.point j‖ /
        (4 * c.radius * Real.sqrt (1 - ‖c.point i - c.point j‖ ^ 2 / 4) *
          ClippingCircle.radius c.radius)) := by
  have hR0 : 0 < c.radius := by linarith
  exact ClippingCircle.unit_corner_angle hi hj (c.clipped_vertex_radius_normal_norm hR0 hx)
    (c.clipped_vertex_unit_unit_inner hi hj) (c.clipped_vertex_unit_radius_inner hR0 hx hi)
    (c.clipped_vertex_unit_radius_inner hR0 hx hj) hR hs (c.diameter_le i j)

/-- The actual tangent-plane angle on the enclosing sphere is the manuscript's `V`. -/
theorem clipped_vertex_radius_face_angle (hR : 1 / 2 < c.radius) {i j : Fin n} {x : E}
    (hx : ‖x‖ = c.radius) (hi : ‖x - c.point i‖ = 1) (hj : ‖x - c.point j‖ = 1) :
    ClippingCircle.faceAngle (c.radius⁻¹ • x) (x - c.point i) (x - c.point j) =
      Real.arccos (1 - ‖c.point i - c.point j‖ ^ 2 / (2 * ClippingCircle.radius c.radius ^ 2)) := by
  have hR0 : 0 < c.radius := by linarith
  exact ClippingCircle.radius_corner_angle hi hj (c.clipped_vertex_radius_normal_norm hR0 hx)
    (c.clipped_vertex_unit_unit_inner hi hj) (c.clipped_vertex_unit_radius_inner hR0 hx hi)
    (c.clipped_vertex_unit_radius_inner hR0 hx hj) hR

end BalancedContacts
end BlaschkeLebesgue
