module

public import BlaschkeLebesgue.ProjectiveCurvature

/-! # The projective rectangle chart and its exact inverse on a hemisphere -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.ObliqueFrame

variable (f : ObliqueFrame)

theorem axis₁_inner_transverse₂ : ⟪f.axis₁, f.transverse₂⟫_ℝ = -f.sine := by
  simp only [transverse₂, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, f.axis₁_norm]
  change f.sine⁻¹ * (f.chi * f.chi - 1 ^ 2) = -f.sine
  field_simp [f.sine_pos.ne']
  rw [f.sine_sq]
  ring

theorem normal_transverse_ext {p q : Space}
    (hz : ⟪f.normal, p⟫_ℝ = ⟪f.normal, q⟫_ℝ)
    (h1 : ⟪f.transverse₁, p⟫_ℝ = ⟪f.transverse₁, q⟫_ℝ)
    (h2 : ⟪f.transverse₂, p⟫_ℝ = ⟪f.transverse₂, q⟫_ℝ) : p = q := by
  have hp := congrArg (fun v : Space ↦ ⟪f.transverse₂, v⟫_ℝ) (f.decompose_first p)
  have hq := congrArg (fun v : Space ↦ ⟪f.transverse₂, v⟫_ℝ) (f.decompose_first q)
  simp only [inner_add_right, real_inner_smul_right,
    real_inner_comm f.normal f.transverse₂, f.normal_inner_transverse₂,
    real_inner_comm f.axis₁ f.transverse₂, f.axis₁_inner_transverse₂,
    real_inner_comm f.transverse₁ f.transverse₂, f.transverse_inner] at hp hq
  have haxis : ⟪f.axis₁, p⟫_ℝ = ⟪f.axis₁, q⟫_ℝ := by
    rw [h1, h2] at hp
    nlinarith [f.sine_pos]
  calc
    p = _ := f.decompose_first p
    _ = _ := by rw [hz, h1, haxis]
    _ = q := (f.decompose_first q).symm

@[expose] def projectiveCoordinates (n : Space) : ℝ × ℝ :=
  (⟪f.transverse₁, n⟫_ℝ / ⟪f.normal, n⟫_ℝ, ⟪f.transverse₂, n⟫_ℝ / ⟪f.normal, n⟫_ℝ)

theorem projectiveCoordinates_normal (x y : ℝ) :
    f.projectiveCoordinates (f.projectiveNormal x y) = (x, y) := by
  have hs := (Real.sqrt_pos.2 (f.W_pos x y)).ne'
  unfold projectiveCoordinates
  rw [f.normal_inner_projectiveNormal, f.projectiveNormal_eq]
  simp only [real_inner_smul_right, inner_add_right,
    real_inner_comm f.normal f.transverse₁, real_inner_comm f.normal f.transverse₂,
    f.normal_inner_transverse₁, f.normal_inner_transverse₂,
    f.planeVector_first_coordinate, f.planeVector_second_coordinate, zero_add]
  congr 1 <;> field_simp

theorem normal_add_planeVector_reconstruct (n : Space) (hn : ⟪f.normal, n⟫_ℝ ≠ 0) :
    f.normal + f.planeVector (f.projectiveCoordinates n).1 (f.projectiveCoordinates n).2 =
      (⟪f.normal, n⟫_ℝ)⁻¹ • n := by
  apply f.normal_transverse_ext
  · simp only [inner_add_right, real_inner_self_eq_norm_sq, f.normal_norm,
      f.normal_inner_planeVector, real_inner_smul_right]
    field_simp
    norm_num
  · simp only [inner_add_right, real_inner_comm f.normal f.transverse₁,
      f.normal_inner_transverse₁, f.planeVector_first_coordinate, zero_add, real_inner_smul_right,
      projectiveCoordinates]
    ring
  · simp only [inner_add_right, real_inner_comm f.normal f.transverse₂,
      f.normal_inner_transverse₂, f.planeVector_second_coordinate, zero_add, real_inner_smul_right,
      projectiveCoordinates]
    ring

theorem projectiveNormal_coordinates {n : Space} (hn : ‖n‖ = 1) (hpos : 0 < ⟪f.normal, n⟫_ℝ) :
    f.projectiveNormal (f.projectiveCoordinates n).1 (f.projectiveCoordinates n).2 = n := by
  rw [projectiveNormal, f.normal_add_planeVector_reconstruct n hpos.ne']
  simp only [NormedSpace.normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, hn,
    mul_one, inv_inv, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

theorem projectiveNormal_injective : Function.Injective (fun p : ℝ × ℝ ↦ f.projectiveNormal p.1 p.2) := by
  intro p q hpq
  have h := congrArg f.projectiveCoordinates hpq
  simpa only [f.projectiveCoordinates_normal, Prod.mk.eta] using h

theorem projectiveNormal_range : Set.range (fun p : ℝ × ℝ ↦ f.projectiveNormal p.1 p.2) =
    {n : Space | ‖n‖ = 1 ∧ 0 < ⟪f.normal, n⟫_ℝ} := by
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨f.projectiveNormal_norm p.1 p.2, by
      rw [f.normal_inner_projectiveNormal]; exact inv_pos.2 (Real.sqrt_pos.2 (f.W_pos p.1 p.2))⟩
  · rintro ⟨hn, hp⟩
    exact ⟨f.projectiveCoordinates n, f.projectiveNormal_coordinates hn hp⟩

theorem continuous_planeVector : Continuous (fun p : ℝ × ℝ ↦ f.planeVector p.1 p.2) := by
  unfold planeVector
  fun_prop

theorem continuous_projectiveNormal : Continuous (fun p : ℝ × ℝ ↦ f.projectiveNormal p.1 p.2) := by
  rw [show (fun p : ℝ × ℝ ↦ f.projectiveNormal p.1 p.2) =
      (fun p ↦ (Real.sqrt (f.W p.1 p.2))⁻¹ • (f.normal + f.planeVector p.1 p.2)) from
        funext fun p ↦ f.projectiveNormal_eq p.1 p.2]
  have hW : Continuous (fun p : ℝ × ℝ ↦ Real.sqrt (f.W p.1 p.2)) := by
    unfold W
    fun_prop
  have hA := hW.inv₀ (fun p ↦ (Real.sqrt_pos.2 (f.W_pos p.1 p.2)).ne')
  have hconst : Continuous (fun _ : ℝ × ℝ ↦ f.normal) := continuous_const
  convert hA.smul (hconst.add f.continuous_planeVector) using 1

@[expose] def projectiveHemisphere : Set UnitSphere := {u | 0 < ⟪f.normal, (u : Space)⟫_ℝ}

@[expose] def projectiveHomeomorph : (ℝ × ℝ) ≃ₜ f.projectiveHemisphere where
  toFun p := ⟨f.projectiveUnitNormal p.1 p.2, by
    change 0 < ⟪f.normal, f.projectiveNormal p.1 p.2⟫_ℝ
    rw [f.normal_inner_projectiveNormal]
    exact inv_pos.2 (Real.sqrt_pos.2 (f.W_pos p.1 p.2))⟩
  invFun u := f.projectiveCoordinates (u.val : Space)
  left_inv p := f.projectiveCoordinates_normal p.1 p.2
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    exact f.projectiveNormal_coordinates u.val.norm_eq_one u.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact f.continuous_projectiveNormal
  continuous_invFun := by
    have hu : Continuous (fun u : f.projectiveHemisphere ↦ (u.val : Space)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have h0 : Continuous (fun u : f.projectiveHemisphere ↦ ⟪f.normal, (u.val : Space)⟫_ℝ) :=
      continuous_const.inner hu
    have h1 : Continuous (fun u : f.projectiveHemisphere ↦ ⟪f.transverse₁, (u.val : Space)⟫_ℝ) :=
      continuous_const.inner hu
    have h2 : Continuous (fun u : f.projectiveHemisphere ↦ ⟪f.transverse₂, (u.val : Space)⟫_ℝ) :=
      continuous_const.inner hu
    exact (h1.div h0 (fun u ↦ u.property.ne')).prodMk (h2.div h0 (fun u ↦ u.property.ne'))

end BlaschkeLebesgue.ObliqueFrame
