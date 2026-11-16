module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-!
# Support functions and constant width

The support function is defined from the underlying compact set. Constant width is the
usual equality of opposite supports, not a structure containing any volume estimate.
This file formalizes the width and opposite-point lemma and unit-ball duality in §2
of `volume_bound_04144.tex`.
-/

public noncomputable section

open scoped InnerProductSpace Pointwise

namespace BlaschkeLebesgue

abbrev Space := EuclideanSpace ℝ (Fin 3)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The positively homogeneous support function of a nonempty compact convex set. -/
@[expose] def support (K : ConvexBody E) (n : E) : ℝ :=
  sSup ((fun x ↦ ⟪n, x⟫_ℝ) '' (K : Set E))

theorem exists_support_point (K : ConvexBody E) (n : E) :
    ∃ x ∈ K, support K n = ⟪n, x⟫_ℝ ∧ ∀ y ∈ K, ⟪n, y⟫_ℝ ≤ ⟪n, x⟫_ℝ :=
  K.isCompact.exists_sSup_image_eq_and_ge K.nonempty (by fun_prop)

theorem inner_le_support (K : ConvexBody E) (n : E) {x : E} (hx : x ∈ K) :
    ⟪n, x⟫_ℝ ≤ support K n := by
  obtain ⟨y, _, hy, hmax⟩ := exists_support_point K n
  rw [hy]
  exact hmax x hx

theorem support_le_iff (K : ConvexBody E) (n : E) (a : ℝ) :
    support K n ≤ a ↔ ∀ x ∈ K, ⟪n, x⟫_ℝ ≤ a := by
  constructor
  · intro h x hx
    exact (inner_le_support K n hx).trans h
  · intro h
    obtain ⟨x, hx, hmax, _⟩ := exists_support_point K n
    rw [hmax]
    exact h x hx

theorem support_smul_direction (K : ConvexBody E) (n : E) {a : ℝ} (ha : 0 ≤ a) :
    support K (a • n) = a * support K n := by
  apply le_antisymm
  · apply (support_le_iff _ _ _).2
    intro x hx
    simpa only [real_inner_smul_left] using mul_le_mul_of_nonneg_left
      (inner_le_support K n hx) ha
  · obtain ⟨x, hx, hmax, _⟩ := exists_support_point K n
    simpa only [real_inner_smul_left, hmax] using inner_le_support K (a • n) hx

theorem support_smul (K : ConvexBody E) (n : E) {a : ℝ} (ha : 0 ≤ a) :
    support (a • K) n = a * support K n := by
  apply le_antisymm
  · apply (support_le_iff _ _ _).2
    rintro x ⟨y, hy, rfl⟩
    simpa only [real_inner_smul_right] using
      mul_le_mul_of_nonneg_left (inner_le_support K n hy) ha
  · obtain ⟨x, hx, hmax, _⟩ := exists_support_point K n
    have hx' : a • x ∈ a • K := Set.smul_mem_smul_set hx
    simpa only [real_inner_smul_right, hmax] using inner_le_support (a • K) n hx'

/-- Width is the separation of the two supporting planes in every unit direction. -/
@[expose] def HasConstantWidth (K : ConvexBody E) (w : ℝ) : Prop :=
  ∀ n : E, ‖n‖ = 1 → support K n + support K (-n) = w

theorem HasConstantWidth.smul {K : ConvexBody E} {w a : ℝ}
    (hK : HasConstantWidth K w) (ha : 0 ≤ a) : HasConstantWidth (a • K) (a * w) := by
  intro n hn
  rw [support_smul K n ha, support_smul K (-n) ha, ← mul_add, hK n hn]

theorem HasConstantWidth.norm_sub_le {K : ConvexBody E} {w : ℝ}
    (hK : HasConstantWidth K w) (hw : 0 ≤ w) {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    ‖x - y‖ ≤ w := by
  by_cases hxy : x - y = 0
  · simpa [hxy] using hw
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr hxy
  let n := ‖x - y‖⁻¹ • (x - y)
  have hn : ‖n‖ = 1 := by simp [n, norm_smul, hnorm.ne']
  have hdiff : ⟪n, x - y⟫_ℝ = ‖x - y‖ := by
    simp [n, real_inner_smul_left, pow_two, hnorm.ne']
  have h₁ := inner_le_support K n hx
  have h₂ := inner_le_support K (-n) hy
  have hwidth := hK n hn
  rw [inner_neg_left] at h₂
  rw [inner_sub_right] at hdiff
  linarith

/-- The point opposite a support point is in the body (Lemma 2.1). -/
theorem HasConstantWidth.opposite_point {K : ConvexBody E}
    (hK : HasConstantWidth K 1) {n x : E} (hn : ‖n‖ = 1) (hx : x ∈ K)
    (hsupport : ⟪n, x⟫_ℝ = support K n) : x - n ∈ K := by
  obtain ⟨y, hy, hymax, _⟩ := exists_support_point K (-n)
  have hd := hK.norm_sub_le (by norm_num) hx hy
  have hinner : ⟪x - y, n⟫_ℝ = 1 := by
    have hwidth := hK n hn
    rw [hymax, inner_neg_left, ← hsupport] at hwidth
    rw [real_inner_comm, inner_sub_right]
    linarith
  have heq : x - y = n := by
    have hnorm : ‖(x - y) - n‖ ^ 2 = 0 := by
      have hle := (sq_le_sq₀ (norm_nonneg (x - y)) zero_le_one).2 hd
      have hexpand := norm_sub_sq_real (x - y) n
      rw [hn, hinner] at hexpand
      nlinarith [sq_nonneg ‖(x - y) - n‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
  have : x - n = y := by rw [← heq]; abel
  simpa [this] using hy

theorem mem_iff_inner_le_support (K : ConvexBody E) (x : E) :
    x ∈ K ↔ ∀ n : E, ⟪n, x⟫_ℝ ≤ support K n := by
  constructor
  · intro hx n
    exact inner_le_support K n hx
  · intro h
    obtain ⟨y, hy, hmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex K.nonempty K.isCompact.isComplete K.convex x
    have hproj := (norm_eq_iInf_iff_real_inner_le_zero K.convex hy).1 hmin
    obtain ⟨z, hz, hzmax, _⟩ := exists_support_point K (x - y)
    have hp := hproj z hz
    have hh := h (x - y)
    rw [hzmax] at hh
    rw [inner_sub_right] at hp
    have hnorm : ‖x - y‖ ^ 2 = 0 := by
      have hi := real_inner_self_eq_norm_sq (x - y)
      rw [inner_sub_right] at hi
      nlinarith [sq_nonneg ‖x - y‖]
    have hxy := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
    simpa [hxy] using hy

theorem mem_iff_unit_inner_le_support (K : ConvexBody E) (x : E) :
    x ∈ K ↔ ∀ n : E, ‖n‖ = 1 → ⟪n, x⟫_ℝ ≤ support K n := by
  constructor
  · intro hx n _
    exact inner_le_support K n hx
  · intro h
    apply (mem_iff_inner_le_support K x).2
    intro n
    by_cases hn : n = 0
    · subst n
      obtain ⟨y, hy⟩ := K.nonempty
      simpa using inner_le_support K 0 hy
    have hpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
    have hu : ‖‖n‖⁻¹ • n‖ = 1 := by
      simp [norm_smul, hpos.ne']
    have hh := h (‖n‖⁻¹ • n) hu
    rw [support_smul_direction K n (by positivity), real_inner_smul_left] at hh
    exact (mul_le_mul_iff_right₀ (inv_pos.mpr hpos)).mp hh

/-- Intersection of all closed unit balls centered in a set. -/
@[expose] def ballTransform (s : Set E) : Set E := {x | ∀ y ∈ s, ‖x - y‖ ≤ 1}

omit [InnerProductSpace ℝ E] in
theorem ballTransform_antitone : Antitone (ballTransform (E := E)) := by
  intro s t h x hx y hy
  exact hx y (h hy)

/-- A width-one convex body equals its unit-ball transform, equation (2.3). -/
theorem HasConstantWidth.ballTransform_eq {K : ConvexBody E} (hK : HasConstantWidth K 1) :
    ballTransform (K : Set E) = (K : Set E) := by
  ext x
  constructor
  · intro hx
    apply (mem_iff_unit_inner_le_support K x).2
    intro n hn
    obtain ⟨y, hy, hymax, _⟩ := exists_support_point K (-n)
    have hnorm := hx y hy
    have hi := real_inner_le_norm n (x - y)
    rw [hn, one_mul, inner_sub_right] at hi
    have hw := hK n hn
    rw [hymax, inner_neg_left] at hw
    linarith
  · intro hx y hy
    exact hK.norm_sub_le (by norm_num) hx hy

/-- Every outer approximation supplies a forced inner approximation, equation (4.2). -/
theorem HasConstantWidth.forced_inner {K : ConvexBody E} (hK : HasConstantWidth K 1)
    {C : Set E} (hC : (K : Set E) ⊆ C) : ballTransform C ⊆ (K : Set E) := by
  rw [← hK.ballTransform_eq]
  exact ballTransform_antitone hC

/-- The radial divergence argument's normal inequality (`eq:radialnormal` in the manuscript). -/
theorem HasConstantWidth.radial_normal {K : ConvexBody E} (hK : HasConstantWidth K 1)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ y ∈ K, ‖y‖ ≤ R)
    {x n : E} (hx : x ∈ K) (hn : ‖n‖ = 1) (hs : ⟪n, x⟫_ℝ = support K n) :
    ‖x‖ ^ 2 + 1 - R ^ 2 ≤ 2 * ⟪x, n⟫_ℝ := by
  have hop := hbound (x - n) (hK.opposite_point hn hx hs)
  have hsq := sq_le_sq₀ (norm_nonneg (x - n)) hR |>.2 hop
  rw [norm_sub_sq_real, hn] at hsq
  nlinarith

end BlaschkeLebesgue
