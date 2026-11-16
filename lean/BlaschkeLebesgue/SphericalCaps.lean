module

public import BlaschkeLebesgue.PositivePropagation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Subdivision of a spherical cap along its great-circle arcs -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eq_of_mem_sphericalCap_one {w u : E} (hw : ‖w‖ = 1)
    (hu : u ∈ sphericalCap w 1) : u = w := by
  have hinner : 1 ≤ ⟪u, w⟫_ℝ := by simpa only [real_inner_comm u w] using hu.2
  have hsquare := norm_sub_sq_real u w
  rw [hu.1, hw] at hsquare
  have hzero : ‖u - w‖ ^ 2 = 0 := by
    nlinarith only [hsquare, hinner, sq_nonneg ‖u - w‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

/-- Every point of a larger cap is within the difference of the half-angles of
some point of the smaller cap. The witness is constructed in their two-dimensional
span, including the case where the original point already lies in the smaller cap. -/
theorem exists_nearby_cap_point {w u : E} (hw : ‖w‖ = 1) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi / 2)
    (hu : u ∈ sphericalCap w (Real.cos β)) :
    ∃ v ∈ sphericalCap w (Real.cos α), Real.cos (β - α) ≤ ⟪v, u⟫_ℝ := by
  have hβ0 : 0 ≤ β := hα.trans hαβ
  have hαπ : α ≤ Real.pi := by linarith [Real.pi_pos]
  have hβπ : β ≤ Real.pi := by linarith [Real.pi_pos]
  by_cases hprev : Real.cos α ≤ ⟪w, u⟫_ℝ
  · refine ⟨u, ⟨hu.1, hprev⟩, ?_⟩
    simpa [real_inner_self_eq_norm_sq, hu.1] using Real.cos_le_one (β - α)
  let t := ⟪u, w⟫_ℝ
  let θ := Real.arccos t
  have ht : -1 ≤ t ∧ t ≤ 1 := real_inner_mem_Icc_of_norm_eq_one hu.1 hw
  have hcos : Real.cos θ = t := Real.cos_arccos ht.1 ht.2
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg t
  have hθβ : θ ≤ β := by
    calc
      θ ≤ Real.arccos (Real.cos β) :=
        Real.arccos_le_arccos (by simpa only [real_inner_comm u w] using hu.2)
      _ = β := Real.arccos_cos hβ0 hβπ
  have hαθ : α < θ := by
    by_contra! hh
    have hcontra := Real.cos_le_cos_of_nonneg_of_le_pi hθ0 hαπ hh
    rw [hcos] at hcontra
    exact hprev (by simpa only [t, real_inner_comm u w] using hcontra)
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_lt hα hαθ) (by linarith [Real.pi_pos])
  let U := u - t • w
  have hU : ‖U‖ ^ 2 = Real.sin θ ^ 2 := by
    have hh := norm_orthogonal_component_sq u hw
    rw [hu.1] at hh
    have htrig := Real.sin_sq_add_cos_sq θ
    rw [hcos] at htrig
    change ‖U‖ ^ 2 = 1 ^ 2 - t ^ 2 at hh
    nlinarith only [hh, htrig]
  have hUnorm : ‖U‖ = Real.sin θ :=
    (sq_eq_sq₀ (norm_nonneg _) hsin.le).1 hU
  let e := (Real.sin θ)⁻¹ • U
  have henorm : ‖e‖ = 1 := by simp [e, norm_smul, hUnorm, abs_of_pos hsin, hsin.ne']
  have hwe : ⟪w, e⟫_ℝ = 0 := by
    dsimp [e, U, t]
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hw, real_inner_comm u w]
    ring
  have hue : ⟪u, e⟫_ℝ = Real.sin θ := by
    dsimp [e, U]
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu.1]
    change (Real.sin θ)⁻¹ * (1 ^ 2 - t * t) = Real.sin θ
    have htrig := Real.sin_sq_add_cos_sq θ
    rw [hcos] at htrig
    have hh : 1 - t * t = Real.sin θ ^ 2 := by nlinarith only [htrig]
    rw [one_pow, hh]
    field_simp
  let v := Real.cos α • w + Real.sin α • e
  have hv : ‖v‖ = 1 := by
    have hsquare : ‖v‖ ^ 2 = 1 := by
      dsimp [v]
      rw [norm_add_sq_real, norm_smul, norm_smul, hw, henorm, mul_one, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
        real_inner_smul_left, real_inner_smul_right, hwe]
      nlinarith only [Real.sin_sq_add_cos_sq α]
    nlinarith only [hsquare, norm_nonneg v]
  have hwv : ⟪w, v⟫_ℝ = Real.cos α := by
    dsimp [v]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hwe,
      real_inner_self_eq_norm_sq, hw]
    ring
  have hvu : ⟪v, u⟫_ℝ = Real.cos (θ - α) := by
    dsimp [v]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm u w, real_inner_comm u e, hue, Real.cos_sub, hcos]
    change Real.cos α * t + Real.sin α * Real.sin θ =
      t * Real.cos α + Real.sin θ * Real.sin α
    ring
  refine ⟨v, ⟨hv, hwv.ge⟩, ?_⟩
  rw [hvu]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.2 hαθ.le)
    (by linarith [Real.pi_pos]) (sub_le_sub_right hθβ α)

end BlaschkeLebesgue
