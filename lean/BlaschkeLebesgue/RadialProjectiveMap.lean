module

public import BlaschkeLebesgue.ProjectiveChart

/-! # A smooth, injective radial extension of the projective hemisphere chart -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.ObliqueFrame

variable (f : ObliqueFrame)

theorem planeVector_eq_first (x y : ℝ) :
    f.planeVector x y = ((f.chi * x - y) / f.sine) • f.axis₁ + x • f.transverse₁ := by
  apply f.normal_transverse_ext
  · simp only [f.normal_inner_planeVector, inner_add_right, real_inner_smul_right,
      f.normal_inner_axis₁, f.normal_inner_transverse₁, mul_zero, add_zero]
  · simp only [f.planeVector_first_coordinate, inner_add_right, real_inner_smul_right,
      real_inner_comm f.axis₁ f.transverse₁, f.axis₁_inner_transverse₁,
      real_inner_self_eq_norm_sq, f.transverse₁_norm]
    ring
  · simp only [f.planeVector_second_coordinate, inner_add_right, real_inner_smul_right,
      real_inner_comm f.axis₁ f.transverse₂, f.axis₁_inner_transverse₂,
      real_inner_comm f.transverse₁ f.transverse₂, f.transverse_inner]
    field_simp [f.sine_pos.ne']
    ring

@[expose] def projectivePlaneMap : Space →L[ℝ] Space :=
  ((f.chi / f.sine) • innerSL ℝ f.axis₁ - (1 / f.sine) • innerSL ℝ f.transverse₁).smulRight f.axis₁ +
    (innerSL ℝ f.axis₁).smulRight f.transverse₁

theorem projectivePlaneMap_apply (p : Space) : f.projectivePlaneMap p =
    ((f.chi * ⟪f.axis₁, p⟫_ℝ - ⟪f.transverse₁, p⟫_ℝ) / f.sine) • f.axis₁ +
      ⟪f.axis₁, p⟫_ℝ • f.transverse₁ := by
  simp only [projectivePlaneMap, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  congr 2
  ring

theorem projectivePlaneMap_eq (p : Space) :
    f.projectivePlaneMap p = f.planeVector ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ := by
  rw [f.projectivePlaneMap_apply, f.planeVector_eq_first]

@[expose] def projectiveLift (p : Space) : Space := f.normal + f.projectivePlaneMap p

theorem projectiveLift_eq (p : Space) :
    f.projectiveLift p = f.normal + f.planeVector ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ := by
  rw [projectiveLift, f.projectivePlaneMap_eq]

theorem projectiveLift_norm (p : Space) :
    ‖f.projectiveLift p‖ = Real.sqrt (f.W ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ) := by
  rw [f.projectiveLift_eq, f.normal_add_planeVector_norm]

theorem projectiveLift_ne_zero (p : Space) : f.projectiveLift p ≠ 0 := by
  rw [f.projectiveLift_eq]
  exact f.normal_add_planeVector_ne_zero _ _

@[expose] def radialProjectiveMap (p : Space) : Space :=
  ⟪f.normal, p⟫_ℝ • NormedSpace.normalize (f.projectiveLift p)

@[expose] def radialProjectiveDeriv (p : Space) : Space →L[ℝ] Space :=
  (⟪f.normal, p⟫_ℝ / ‖f.projectiveLift p‖) •
      (tangentProjection (NormedSpace.normalize (f.projectiveLift p))).comp f.projectivePlaneMap +
    (innerSL ℝ f.normal).smulRight (NormedSpace.normalize (f.projectiveLift p))

theorem radialProjectiveMap_eq (p : Space) :
    f.radialProjectiveMap p = ⟪f.normal, p⟫_ℝ • f.projectiveNormal ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ := by
  rw [radialProjectiveMap, f.projectiveLift_eq]
  rfl

theorem hasFDerivAt_radialProjectiveMap (p : Space) :
    HasFDerivAt f.radialProjectiveMap (f.radialProjectiveDeriv p) p := by
  have hl := (hasFDerivAt_const f.normal p).add f.projectivePlaneMap.hasFDerivAt
  have hn := (hasFDerivAt_normalize (f.projectiveLift_ne_zero p)).comp p hl
  have h := (innerSL ℝ f.normal).hasFDerivAt.smul hn
  have he : ((innerSL ℝ f.normal : Space → ℝ) •
      (NormedSpace.normalize ∘ f.projectiveLift)) =
      f.radialProjectiveMap := by
    funext q
    rfl
  rw [he] at h
  simpa only [radialProjectiveDeriv, zero_add, innerSL_apply_apply,
    ContinuousLinearMap.smul_comp, smul_smul, div_eq_mul_inv, Function.comp_def] using h

theorem radialProjectiveMap_norm {p : Space} (hp : 0 < ⟪f.normal, p⟫_ℝ) :
    ‖f.radialProjectiveMap p‖ = ⟪f.normal, p⟫_ℝ := by
  rw [f.radialProjectiveMap_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hp,
    f.projectiveNormal_norm, mul_one]

theorem radialProjectiveMap_injOn :
    Set.InjOn f.radialProjectiveMap {p : Space | 0 < ⟪f.normal, p⟫_ℝ} := by
  intro p hp q hq heq
  change 0 < ⟪f.normal, p⟫_ℝ at hp
  change 0 < ⟪f.normal, q⟫_ℝ at hq
  have hr : ⟪f.normal, p⟫_ℝ = ⟪f.normal, q⟫_ℝ := by
    simpa only [f.radialProjectiveMap_norm hp, f.radialProjectiveMap_norm hq] using congrArg norm heq
  have hn := congrArg (fun v : Space ↦ (⟪f.normal, p⟫_ℝ)⁻¹ • v) heq
  rw [f.radialProjectiveMap_eq, f.radialProjectiveMap_eq, ← hr,
    smul_smul, smul_smul, inv_mul_cancel₀ hp.ne', one_smul, one_smul] at hn
  have hc : (⟪f.axis₁, p⟫_ℝ, ⟪f.transverse₁, p⟫_ℝ) = (⟪f.axis₁, q⟫_ℝ, ⟪f.transverse₁, q⟫_ℝ) :=
    f.projectiveNormal_injective hn
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  dsimp only at hx hy
  calc
    p = _ := f.decompose_first p
    _ = _ := by rw [hr, hx, hy]
    _ = q := (f.decompose_first q).symm

theorem projectivePlaneMap_normal : f.projectivePlaneMap f.normal = 0 := by
  simp only [f.projectivePlaneMap_apply, real_inner_comm f.normal f.axis₁,
    real_inner_comm f.normal f.transverse₁, f.normal_inner_axis₁, f.normal_inner_transverse₁,
    mul_zero, sub_zero, zero_div, zero_smul, add_zero]

theorem projectivePlaneMap_axis₁ :
    f.projectivePlaneMap f.axis₁ = (f.chi / f.sine) • f.axis₁ + f.transverse₁ := by
  simp only [f.projectivePlaneMap_apply, real_inner_self_eq_norm_sq, f.axis₁_norm,
    real_inner_comm f.axis₁ f.transverse₁, f.axis₁_inner_transverse₁,
    one_pow, mul_one, sub_zero, one_smul]

theorem projectivePlaneMap_transverse₁ :
    f.projectivePlaneMap f.transverse₁ = -(1 / f.sine) • f.axis₁ := by
  simp only [f.projectivePlaneMap_apply, f.axis₁_inner_transverse₁,
    real_inner_self_eq_norm_sq, f.transverse₁_norm, one_pow, mul_zero,
    zero_sub, neg_div, zero_smul, add_zero]

theorem radialProjectiveDeriv_apply (p v : Space) :
    f.radialProjectiveDeriv p v =
      (⟪f.normal, p⟫_ℝ / ‖f.projectiveLift p‖) •
        (f.projectivePlaneMap v - ⟪NormedSpace.normalize (f.projectiveLift p), f.projectivePlaneMap v⟫_ℝ •
          NormedSpace.normalize (f.projectiveLift p)) +
      ⟪f.normal, v⟫_ℝ • NormedSpace.normalize (f.projectiveLift p) := by
  simp only [radialProjectiveDeriv, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, tangentProjection_apply]

end BlaschkeLebesgue.ObliqueFrame
