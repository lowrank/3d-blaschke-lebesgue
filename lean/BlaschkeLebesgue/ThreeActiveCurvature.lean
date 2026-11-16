module

public import BlaschkeLebesgue.ActiveBallCurvature
public import BlaschkeLebesgue.ClippedLensParameters
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! # Vanishing curvature at three independent active constraints -/

public noncomputable section

open Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem det_gram_three_unit {x y z : Space} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    (Matrix.gram ℝ ![x, y, z]).det = lensGram ⟪x, y⟫_ℝ ⟪x, z⟫_ℝ ⟪y, z⟫_ℝ := by
  simp [Matrix.det_fin_three, hx, hy, hz, lensGram, real_inner_comm]
  ring

theorem lensGram_pos_of_half_to_twentyseven_fiftieths {a b c : ℝ}
    (ha : a ∈ Icc (1 / 2 : ℝ) (27 / 50)) (hb : b ∈ Icc (1 / 2 : ℝ) (27 / 50))
    (hc : c ∈ Icc (1 / 2 : ℝ) (27 / 50)) : 0 < lensGram a b c := by
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hc0 : 0 ≤ c := by linarith [hc.1]
  have ha2 := pow_le_pow_left₀ ha0 ha.2 2
  have hb2 := pow_le_pow_left₀ hb0 hb.2 2
  have hc2 := pow_le_pow_left₀ hc0 hc.2 2
  have hab := mul_le_mul ha.1 hb.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) ha0
  have habc := mul_le_mul hab hc.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (mul_nonneg ha0 hb0)
  unfold lensGram
  nlinarith

theorem linearIndependent_three_unit_of_inner_bounds {x y z : Space}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hxy : ⟪x, y⟫_ℝ ∈ Icc (1 / 2 : ℝ) (27 / 50))
    (hxz : ⟪x, z⟫_ℝ ∈ Icc (1 / 2 : ℝ) (27 / 50))
    (hyz : ⟪y, z⟫_ℝ ∈ Icc (1 / 2 : ℝ) (27 / 50)) :
    LinearIndependent ℝ ![x, y, z] := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_three_unit hx hy hz]
  exact (lensGram_pos_of_half_to_twentyseven_fiftieths hxy hxz hyz).ne'

theorem sphereCurvature_eq_zero_of_annihilates_basis (K : ConvexBody Space) (u : UnitSphere)
    (n : Fin 3 → Space) (hn : LinearIndependent ℝ n)
    (hz : ∀ i, sphereCurvature K u (n i) = 0) : sphereCurvature K u = 0 := by
  let b := basisOfLinearIndependentOfCardEqFinrank hn (by simp [Space])
  have he : (sphereCurvature K u).toLinearMap = 0 := by
    apply b.ext
    intro i
    change sphereCurvature K u (b i) = 0
    have hb : b i = n i := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hn (by simp [Space])) i
    rw [hb]
    exact hz i
  ext x : 1
  exact LinearMap.congr_fun he x

namespace BalancedContacts

variable (c : BalancedContacts 4 Space)

theorem clipped_active_unit_inner_bounds (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) {x : Space}
    (hi : ‖x - c.point i‖ = 1) (hj : ‖x - c.point j‖ = 1) :
    ⟪x - c.point i, x - c.point j⟫_ℝ ∈ Icc (1 / 2 : ℝ) (27 / 50) := by
  obtain ⟨_, _, _, hs, hs1, hslo⟩ := c.clipped_lens_parameter_bounds hA (Ne.symm hij)
  rw [c.clipped_vertex_unit_unit_inner hi hj]
  constructor <;> nlinarith

theorem clipped_three_unit_normals_independent (hA : c.totalDeficit ≤ 2 / 25)
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {x : Space}
    (hi : ‖x - c.point i‖ = 1) (hj : ‖x - c.point j‖ = 1) (hk : ‖x - c.point k‖ = 1) :
    LinearIndependent ℝ ![x - c.point i, x - c.point j, x - c.point k] :=
  linearIndependent_three_unit_of_inner_bounds hi hj hk
    (c.clipped_active_unit_inner_bounds hA hij hi hj)
    (c.clipped_active_unit_inner_bounds hA hik hi hk)
    (c.clipped_active_unit_inner_bounds hA hjk hj hk)

theorem clipped_two_unit_radius_normals_independent (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) {x : Space} (hx : ‖x‖ = c.radius)
    (hi : ‖x - c.point i‖ = 1) (hj : ‖x - c.point j‖ = 1) :
    LinearIndependent ℝ ![x - c.point i, x - c.point j, c.radius⁻¹ • x] := by
  obtain ⟨hR, hRlo, _, hs, hs1, _⟩ := c.clipped_lens_parameter_bounds hA (Ne.symm hij)
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_three_unit hi hj (c.clipped_vertex_radius_normal_norm hR hx),
    c.clipped_vertex_unit_unit_inner hi hj, c.clipped_vertex_unit_radius_inner hR hx hi,
    c.clipped_vertex_unit_radius_inner hR hx hj]
  have he : lensGram (1 - ‖c.point i - c.point j‖ ^ 2 / 2)
      (1 / (2 * c.radius)) (1 / (2 * c.radius)) =
      ‖c.point i - c.point j‖ ^ 2 * (c.radius ^ 2 * (4 - ‖c.point i - c.point j‖ ^ 2) - 1) /
        (4 * c.radius ^ 2) := by
    unfold lensGram
    field_simp
    ring
  rw [he]
  have hs2 : ‖c.point i - c.point j‖ ^ 2 ≤ 1 := by nlinarith
  have hp := mul_nonneg (sq_nonneg c.radius) (sub_nonneg.2 hs2)
  exact (div_pos (mul_pos (sq_pos_of_pos hs) (by nlinarith)) (by positivity)).ne'

variable {hne : (clippedOuter c.radius (range c.point)).Nonempty}

theorem sphereCurvature_clipped_apply_unit_normal
    (u : UnitSphere) (i : Fin 4)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1) :
    sphereCurvature (clippedOuterBody c.radius (range c.point) hne) u
      (normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i) = 0 := by
  have hR1 : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
  exact sphereCurvature_apply_active_ball (clippedBodies_complement c.radius (range c.point) hne hR1) u
    (fun x hx ↦ ((c.mem_clippedOuter_range_iff x).1 hx).2 i) hi

theorem sphereCurvature_clipped_zero_three_unit (hA : c.totalDeficit ≤ 2 / 25)
    (u : UnitSphere) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hj : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ = 1)
    (hk : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point k‖ = 1) :
    sphereCurvature (clippedOuterBody c.radius (range c.point) hne) u = 0 := by
  apply sphereCurvature_eq_zero_of_annihilates_basis _ _ _
    (c.clipped_three_unit_normals_independent hA hij hik hjk hi hj hk)
  intro l
  fin_cases l
  · exact c.sphereCurvature_clipped_apply_unit_normal u i hi
  · exact c.sphereCurvature_clipped_apply_unit_normal u j hj
  · exact c.sphereCurvature_clipped_apply_unit_normal u k hk

theorem sphereCurvature_clipped_zero_two_unit_radius (hA : c.totalDeficit ≤ 2 / 25)
    (u : UnitSphere) {i j : Fin 4} (hij : i ≠ j)
    (hx : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ = c.radius)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hj : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ = 1) :
    sphereCurvature (clippedOuterBody c.radius (range c.point) hne) u = 0 := by
  apply sphereCurvature_eq_zero_of_annihilates_basis _ _ _
    (c.clipped_two_unit_radius_normals_independent hA hij hx hi hj)
  intro l
  fin_cases l
  · exact c.sphereCurvature_clipped_apply_unit_normal u i hi
  · exact c.sphereCurvature_clipped_apply_unit_normal u j hj
  · change sphereCurvature _ u (c.radius⁻¹ • normalSupport _ (u : Space)) = 0
    rw [map_smul]
    have hR1 : c.radius ≤ 1 := by nlinarith [c.radius_sq_le (by decide)]
    have h := sphereCurvature_apply_active_ball
      (clippedBodies_complement c.radius (range c.point) hne hR1) u (p := 0) (r := c.radius)
      (by intro x hx; simpa using ((c.mem_clippedOuter_range_iff x).1 hx).1)
      (by simpa using hx)
    simp only [sub_zero] at h
    rw [h, smul_zero]

theorem curvatureTrace_clipped_zero_three_unit (hA : c.totalDeficit ≤ 2 / 25)
    (u : UnitSphere) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hj : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ = 1)
    (hk : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point k‖ = 1) :
    curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u = 0 := by
  rw [curvatureTrace, c.sphereCurvature_clipped_zero_three_unit hA u hij hik hjk hi hj hk]
  simp

theorem curvatureTrace_clipped_zero_two_unit_radius (hA : c.totalDeficit ≤ 2 / 25)
    (u : UnitSphere) {i j : Fin 4} (hij : i ≠ j)
    (hx : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space)‖ = c.radius)
    (hi : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point i‖ = 1)
    (hj : ‖normalSupport (clippedOuterBody c.radius (range c.point) hne) (u : Space) - c.point j‖ = 1) :
    curvatureTrace (clippedOuterBody c.radius (range c.point) hne) u = 0 := by
  rw [curvatureTrace, c.sphereCurvature_clipped_zero_two_unit_radius hA u hij hx hi hj]
  simp

end BalancedContacts
end BlaschkeLebesgue
