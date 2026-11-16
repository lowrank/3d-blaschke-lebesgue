module

public import BlaschkeLebesgue.ProjectiveJacobian

/-! # The radial chart maps parameter cylinders onto actual spherical annulus patches -/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue.ObliqueFrame

variable (f : ObliqueFrame)

@[expose] def radialPoint (r x y : ℝ) : Space := r • f.normal + x • f.axis₁ + y • f.transverse₁

theorem normal_inner_radialPoint (r x y : ℝ) : ⟪f.normal, f.radialPoint r x y⟫_ℝ = r := by
  simp only [radialPoint, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    f.normal_norm, f.normal_inner_axis₁, f.normal_inner_transverse₁]
  ring

theorem axis₁_inner_radialPoint (r x y : ℝ) : ⟪f.axis₁, f.radialPoint r x y⟫_ℝ = x := by
  simp only [radialPoint, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    f.axis₁_norm, real_inner_comm f.normal f.axis₁, f.normal_inner_axis₁, f.axis₁_inner_transverse₁]
  ring

theorem transverse₁_inner_radialPoint (r x y : ℝ) : ⟪f.transverse₁, f.radialPoint r x y⟫_ℝ = y := by
  simp only [radialPoint, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    f.transverse₁_norm, real_inner_comm f.normal f.transverse₁, f.normal_inner_transverse₁,
    real_inner_comm f.axis₁ f.transverse₁, f.axis₁_inner_transverse₁]
  ring

theorem radialProjectiveMap_radialPoint (r x y : ℝ) :
    f.radialProjectiveMap (f.radialPoint r x y) = r • f.projectiveNormal x y := by
  rw [f.radialProjectiveMap_eq, f.normal_inner_radialPoint, f.axis₁_inner_radialPoint,
    f.transverse₁_inner_radialPoint]

theorem projectiveCoordinates_smul (n : Space) {r : ℝ} (hr : r ≠ 0) :
    f.projectiveCoordinates (r • n) = f.projectiveCoordinates n := by
  simp only [projectiveCoordinates, real_inner_smul_right]
  congr 1 <;> rw [mul_div_mul_left _ _ hr]

theorem projectiveNormal_coordinates_normalize {n : Space} (hp : 0 < ⟪f.normal, n⟫_ℝ) :
    f.projectiveNormal (f.projectiveCoordinates n).1 (f.projectiveCoordinates n).2 = NormedSpace.normalize n := by
  rw [projectiveNormal, f.normal_add_planeVector_reconstruct n hp.ne',
    NormedSpace.normalize_smul_of_pos (inv_pos.2 hp)]

theorem radialProjectiveMap_coordinates {p : Space} (hp : 0 < ⟪f.normal, p⟫_ℝ) :
    f.projectiveCoordinates (f.radialProjectiveMap p) = (⟪f.axis₁, p⟫_ℝ, ⟪f.transverse₁, p⟫_ℝ) := by
  rw [f.radialProjectiveMap_eq, f.projectiveCoordinates_smul _ hp.ne', f.projectiveCoordinates_normal]

theorem radialProjectiveMap_normal_pos {p : Space} (hp : 0 < ⟪f.normal, p⟫_ℝ) :
    0 < ⟪f.normal, f.radialProjectiveMap p⟫_ℝ := by
  rw [f.radialProjectiveMap_eq, real_inner_smul_right, f.normal_inner_projectiveNormal]
  exact mul_pos hp (inv_pos.2 (Real.sqrt_pos.2 (f.W_pos _ _)))

@[expose] def projectiveCylinder (s : Set (ℝ × ℝ)) : Set Space :=
  {p | ⟪f.normal, p⟫_ℝ ∈ Icc (1 : ℝ) 2 ∧ (⟪f.axis₁, p⟫_ℝ, ⟪f.transverse₁, p⟫_ℝ) ∈ s}

@[expose] def projectiveAnnulus (s : Set (ℝ × ℝ)) : Set Space :=
  {q | ‖q‖ ∈ Icc (1 : ℝ) 2 ∧ 0 < ⟪f.normal, q⟫_ℝ ∧ f.projectiveCoordinates q ∈ s}

theorem measurableSet_projectiveCylinder {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (f.projectiveCylinder s) :=
  (isClosed_Icc.preimage (continuous_const.inner continuous_id)).measurableSet.inter
    (hs.preimage ((continuous_const.inner continuous_id).prodMk (continuous_const.inner continuous_id)).measurable)

theorem projectiveCylinder_pos {s : Set (ℝ × ℝ)} :
    f.projectiveCylinder s ⊆ {p : Space | 0 < ⟪f.normal, p⟫_ℝ} :=
  fun _ hp ↦ lt_of_lt_of_le zero_lt_one hp.1.1

theorem radialProjectiveMap_image_cylinder (s : Set (ℝ × ℝ)) :
    f.radialProjectiveMap '' f.projectiveCylinder s = f.projectiveAnnulus s := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpos := f.projectiveCylinder_pos hp
    exact ⟨by rw [f.radialProjectiveMap_norm hpos]; exact hp.1, f.radialProjectiveMap_normal_pos hpos,
      by rw [f.radialProjectiveMap_coordinates hpos]; exact hp.2⟩
  · rintro ⟨hqn, hqz, hqs⟩
    refine ⟨f.radialPoint ‖q‖ (f.projectiveCoordinates q).1 (f.projectiveCoordinates q).2, ?_, ?_⟩
    · change _ ∈ Icc (1 : ℝ) 2 ∧ _ ∈ s
      rw [f.normal_inner_radialPoint, f.axis₁_inner_radialPoint, f.transverse₁_inner_radialPoint,
        Prod.mk.eta]
      exact ⟨hqn, hqs⟩
    · rw [f.radialProjectiveMap_radialPoint, f.projectiveNormal_coordinates_normalize hqz,
        NormedSpace.normalize]
      have hn : ‖q‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hqn.1)
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem integral_projectiveAnnulus {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (g : Space → ℝ) :
    (∫ q in f.projectiveAnnulus s, g q) =
      ∫ p in f.projectiveCylinder s, (⟪f.normal, p⟫_ℝ ^ 2 /
        (f.sine * Real.sqrt (f.W ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ) ^ 3)) * g (f.radialProjectiveMap p) := by
  rw [← f.radialProjectiveMap_image_cylinder]
  exact f.integral_image_radialProjectiveMap (f.measurableSet_projectiveCylinder hs) f.projectiveCylinder_pos g

end BlaschkeLebesgue.ObliqueFrame
