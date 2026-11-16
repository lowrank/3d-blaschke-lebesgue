module

public import BlaschkeLebesgue.Certificates.RadialGeometry
public import BlaschkeLebesgue.SphericalCaps

/-! # Exact spherical geometry of the rational radial grid -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.Certificates.RadialArithmetic

theorem cosine_bounds (k : ℕ) : -1 ≤ cosine k ∧ cosine k ≤ 1 := by
  have hden : 0 < (gridSize : ℚ) ^ 2 + (k : ℚ) ^ 2 := by norm_num [gridSize]; positivity
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith only [sq_nonneg (gridSize : ℚ)]
  · apply (div_le_iff₀ hden).2
    nlinarith only [sq_nonneg (k : ℚ)]

theorem sine_nonneg (k : ℕ) : 0 ≤ sine k := by unfold sine; positivity

theorem cosine_antitone : Antitone cosine := by
  intro k l hkl
  have hk : 0 < (gridSize : ℚ) ^ 2 + (k : ℚ) ^ 2 := by norm_num [gridSize]; positivity
  have hl : 0 < (gridSize : ℚ) ^ 2 + (l : ℚ) ^ 2 := by norm_num [gridSize]; positivity
  apply (div_le_div_iff₀ hl hk).2
  have hcast : (k : ℚ) ≤ (l : ℚ) := by exact_mod_cast hkl
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg k : (0 : ℚ) ≤ k) (Nat.cast_nonneg l)).2 hcast
  norm_num [gridSize] at *
  nlinarith only [hsq]

/-- Angles are used only to establish the geometry; all certificate inputs stay rational. -/
@[expose] def gridAngle (k : ℕ) : ℝ := Real.arccos (cosine k)

theorem gridAngle_nonneg (k : ℕ) : 0 ≤ gridAngle k := Real.arccos_nonneg _

theorem gridAngle_le_pi_div_two {k : ℕ} (hk : k ≤ gridSize) :
    gridAngle k ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.2 (by exact_mod_cast cosine_nonneg hk)

theorem gridAngle_monotone : Monotone gridAngle := by
  intro k l hkl
  exact Real.arccos_le_arccos (by exact_mod_cast cosine_antitone hkl)

theorem cos_gridAngle (k : ℕ) : Real.cos (gridAngle k) = (cosine k : ℝ) :=
  Real.cos_arccos (by exact_mod_cast (cosine_bounds k).1)
    (by exact_mod_cast (cosine_bounds k).2)

theorem sin_gridAngle (k : ℕ) : Real.sin (gridAngle k) = (sine k : ℝ) := by
  rw [gridAngle, Real.sin_arccos]
  have heq : 1 - (cosine k : ℝ) ^ 2 = (sine k : ℝ) ^ 2 := by
    linarith only [grid_circle k]
  rw [heq, Real.sqrt_sq (by exact_mod_cast sine_nonneg k)]

theorem stepCosine_eq {k : ℕ} (hk : 1 ≤ k) :
    stepCosine k = cosine k * cosine (k - 1) + sine k * sine (k - 1) := by
  have hcast : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by rw [Nat.cast_sub hk]; norm_num
  simp only [stepCosine, cosine, sine, hcast]
  norm_num [gridSize]
  field_simp
  ring

theorem stepSine_eq {k : ℕ} (hk : 1 ≤ k) :
    stepSine k = sine k * cosine (k - 1) - cosine k * sine (k - 1) := by
  have hcast : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by rw [Nat.cast_sub hk]; norm_num
  simp only [stepSine, cosine, sine, hcast]
  norm_num [gridSize]
  field_simp
  ring

theorem cos_gridAngle_sub {k : ℕ} (hk : 1 ≤ k) :
    Real.cos (gridAngle k - gridAngle (k - 1)) = (stepCosine k : ℝ) := by
  rw [Real.cos_sub, cos_gridAngle, cos_gridAngle, sin_gridAngle, sin_gridAngle]
  exact_mod_cast (stepCosine_eq hk).symm

theorem sin_gridAngle_sub {k : ℕ} (hk : 1 ≤ k) :
    Real.sin (gridAngle k - gridAngle (k - 1)) = (stepSine k : ℝ) := by
  rw [Real.sin_sub, cos_gridAngle, cos_gridAngle, sin_gridAngle, sin_gridAngle]
  exact_mod_cast (stepSine_eq hk).symm

theorem step_nonneg {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ gridSize) :
    0 ≤ stepCosine k ∧ 0 ≤ stepSine k := by
  have hδ : 0 ≤ gridAngle k - gridAngle (k - 1) :=
    sub_nonneg.2 (gridAngle_monotone (Nat.sub_le k 1))
  have hδ' : gridAngle k - gridAngle (k - 1) ≤ Real.pi / 2 := by
    linarith only [gridAngle_le_pi_div_two hkN, gridAngle_nonneg (k - 1)]
  constructor
  · have hh := Real.cos_nonneg_of_mem_Icc
      (show gridAngle k - gridAngle (k - 1) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
    rw [cos_gridAngle_sub hk] at hh
    exact_mod_cast hh
  · have hh := Real.sin_nonneg_of_nonneg_of_le_pi hδ (by linarith [Real.pi_pos])
    rw [sin_gridAngle_sub hk] at hh
    exact_mod_cast hh

theorem step_circle {k : ℕ} (hk : 1 ≤ k) :
    (stepCosine k : ℝ) ^ 2 + (stepSine k : ℝ) ^ 2 = 1 := by
  have hh := Real.sin_sq_add_cos_sq (gridAngle k - gridAngle (k - 1))
  rw [cos_gridAngle_sub hk, sin_gridAngle_sub hk] at hh
  linarith only [hh]

/-- Every direction in the next rational cap has a preceding direction in the
previous cap within the checked rational angular step. -/
theorem exists_preceding_grid_cap_point {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {w u : E} (hw : ‖w‖ = 1) {k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ gridSize) (hu : u ∈ sphericalCap w (cosine k : ℝ)) :
    ∃ v ∈ sphericalCap w (cosine (k - 1) : ℝ), (stepCosine k : ℝ) ≤ ⟪v, u⟫_ℝ := by
  obtain ⟨v, hv, hnear⟩ := exists_nearby_cap_point hw (gridAngle_nonneg (k - 1))
    (gridAngle_monotone (Nat.sub_le k 1)) (gridAngle_le_pi_div_two hkN)
      (by simpa only [cos_gridAngle] using hu)
  rw [cos_gridAngle] at hv
  rw [cos_gridAngle_sub hk] at hnear
  exact ⟨v, hv, hnear⟩

end BlaschkeLebesgue.Certificates.RadialArithmetic
