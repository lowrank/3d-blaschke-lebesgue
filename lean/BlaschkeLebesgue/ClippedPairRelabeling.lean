module

public import BlaschkeLebesgue.ClippedFaceCaps
public import BlaschkeLebesgue.ClippingCircleCuts
public import BlaschkeLebesgue.ClippedRelabeling

/-! # Relabeling any contact pair as the first two contacts -/

public noncomputable section

open Set
open scoped InnerProductSpace

namespace BlaschkeLebesgue.BalancedContacts

theorem exists_perm_first_pair (i j : Fin 4) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin 4), e 0 = i ∧ e 1 = j := by
  have h : ∀ i j : Fin 4, i ≠ j → ∃ e : Equiv.Perm (Fin 4), e 0 = i ∧ e 1 = j := by
    decide +kernel
  exact h i j hij

variable (c : BalancedContacts 4 Space)

@[expose] def clippingPairProjection (i j : Fin 4) : Space :=
  ClippingCircle.faceTangent (c.clippingCircleAxis i) (c.point j)

@[expose] def clippingPairDirection (i j : Fin 4) : Space :=
  -NormedSpace.normalize (c.clippingPairProjection i j)

@[expose] def clippingPairCos (i j : Fin 4) : ℝ :=
  (1 - 2 * c.radius ^ 2) * ‖c.point j - c.point i‖ /
    (4 * c.radius * ClippingCircle.radius c.radius * ‖(1 / 2 : ℝ) • (c.point i + c.point j)‖)

theorem clippingPairDirection_norm (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) : ‖c.clippingPairDirection i j‖ = 1 := by
  obtain ⟨e, he₀, he₁⟩ := exists_perm_first_pair i j hij
  have h := Opposite.enclosingCutDirection_norm (c.relabel e)
    (by simpa only [c.totalDeficit_relabel] using hA)
  simpa only [clippingPairDirection, norm_neg, Opposite.enclosingCutDirection,
    Opposite.enclosingCutProjection, clippingPairProjection, clippingCircleAxis, relabel, he₀, he₁] using h

theorem clippingPairProjection_norm (hR : 0 < c.radius) {i j : Fin 4} (hij : i ≠ j) :
    ‖c.clippingPairProjection i j‖ =
      ‖c.point j - c.point i‖ * ‖(1 / 2 : ℝ) • (c.point i + c.point j)‖ / c.radius := by
  obtain ⟨e, he₀, he₁⟩ := exists_perm_first_pair i j hij
  have h := Opposite.enclosingCutProjection_norm (c.relabel e) hR
  simpa only [clippingPairProjection, clippingCircleAxis, Opposite.enclosingCutProjection,
    Opposite.firstEdge, Opposite.firstMidpoint, relabel, he₀, he₁] using h

theorem clippingPairProjection_norm_pos (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) : 0 < ‖c.clippingPairProjection i j‖ := by
  apply norm_pos_iff.2
  intro he
  have h := c.clippingPairDirection_norm hA hij
  simp only [clippingPairDirection, he, NormedSpace.normalize_zero_eq_zero, neg_zero,
    norm_zero, zero_ne_one] at h

theorem clippingPairDirection_inner_axis (hR : 0 < c.radius) (i j : Fin 4) :
    ⟪c.clippingCircleAxis i, c.clippingPairDirection i j⟫_ℝ = 0 := by
  simp only [clippingPairDirection, NormedSpace.normalize, inner_neg_right, real_inner_smul_right,
    clippingPairProjection, ClippingCircle.faceTangent, inner_sub_right,
    real_inner_self_eq_norm_sq, c.clippingCircleAxis_norm hR i, one_pow, mul_one,
    sub_self, mul_zero, neg_zero]

theorem clippingPairCos_bounds (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) : 0 < c.clippingPairCos i j ∧ c.clippingPairCos i j < 1 := by
  obtain ⟨e, he₀, he₁⟩ := exists_perm_first_pair i j hij
  have h := Opposite.enclosingCutCos_bounds (c.relabel e)
    (by simpa only [c.totalDeficit_relabel] using hA)
  simpa only [clippingPairCos, Opposite.enclosingCutCos, Opposite.firstEdge,
    Opposite.firstMidpoint, relabel, he₀, he₁] using h

theorem clippingCircle_excluded_pair_iff (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) {v : Space} (hv : ‖v‖ = 1) (hp : ⟪c.point i, v⟫_ℝ = 0) :
    1 < ‖c.clippingCirclePoint i v - c.point j‖ ↔
      c.clippingPairCos i j < ⟪c.clippingPairDirection i j, v⟫_ℝ := by
  obtain ⟨e, he₀, he₁⟩ := exists_perm_first_pair i j hij
  have hp' : ⟪(c.relabel e).point 0, v⟫_ℝ = 0 := by simpa only [relabel, he₀] using hp
  have h := Opposite.clippingCircle_excluded_iff_inner (c.relabel e)
    (by simpa only [c.totalDeficit_relabel] using hA) hv hp'
  simpa only [clippingCirclePoint, clippingCircleAxis, clippingPairCos, clippingPairDirection,
    clippingPairProjection, Opposite.enclosingCutCos, Opposite.firstEdge,
    Opposite.firstMidpoint, Opposite.enclosingCutDirection, Opposite.enclosingCutProjection,
    relabel, he₀, he₁, real_inner_comm v] using h

theorem inner_clippingPairDirection (i j : Fin 4) {v : Space}
    (hp : ⟪c.point i, v⟫_ℝ = 0) :
    ‖c.clippingPairProjection i j‖ * ⟪c.clippingPairDirection i j, v⟫_ℝ = -⟪v, c.point j⟫_ℝ := by
  have hvk : ⟪c.clippingCircleAxis i, v⟫_ℝ = 0 := by
    simp only [clippingCircleAxis, real_inner_smul_left, hp, mul_zero]
  have hi : ⟪c.clippingPairProjection i j, v⟫_ℝ = ⟪c.point j, v⟫_ℝ := by
    simp only [clippingPairProjection, ClippingCircle.faceTangent, inner_sub_left,
      real_inner_smul_left, hvk, mul_zero, sub_zero]
  rw [← real_inner_smul_left, clippingPairDirection, smul_neg, NormedSpace.norm_smul_normalize,
    inner_neg_left, hi, real_inner_comm]

theorem clippingPairCos_relation (hA : c.totalDeficit ≤ 2 / 25) {i j : Fin 4} (hij : i ≠ j) :
    (2 * ClippingCircle.radius c.radius * ‖c.clippingPairProjection i j‖) * c.clippingPairCos i j =
      -(ClippingCircle.height c.radius / c.radius * ‖c.point i - c.point j‖ ^ 2) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  have hR0 : 0 < c.radius := by linarith
  have hκ := ClippingCircle.radius_pos hR
  have hp := c.clippingPairProjection_norm_pos hA hij
  have hm : ‖(1 / 2 : ℝ) • (c.point i + c.point j)‖ ≠ 0 := by
    intro hm
    rw [c.clippingPairProjection_norm hR0 hij, hm, mul_zero, zero_div] at hp
    exact (lt_irrefl 0) hp
  rw [c.clippingPairProjection_norm hR0 hij]
  unfold clippingPairCos ClippingCircle.height
  rw [norm_sub_rev (c.point i)]
  field_simp
  ring

theorem clippingCircle_distance_sq_pair (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) {v : Space} (hv : ‖v‖ = 1) (hp : ⟪c.point i, v⟫_ℝ = 0) :
    ‖c.clippingCirclePoint i v - c.point j‖ ^ 2 = 1 +
      (2 * ClippingCircle.radius c.radius * ‖c.clippingPairProjection i j‖) *
        (⟪c.clippingPairDirection i j, v⟫_ℝ - c.clippingPairCos i j) := by
  have hR := Opposite.radius_gt_half_of_small_deficit c hA
  rw [c.clippingCirclePoint_sub_sq hR hv hp j, mul_sub, c.clippingPairCos_relation hA hij]
  have hi := c.inner_clippingPairDirection i j hp
  linear_combination -2 * ClippingCircle.radius c.radius * hi

theorem clippingCircle_distance_eq_pair_iff (hA : c.totalDeficit ≤ 2 / 25)
    {i j : Fin 4} (hij : i ≠ j) {v : Space} (hv : ‖v‖ = 1) (hp : ⟪c.point i, v⟫_ℝ = 0) :
    ‖c.clippingCirclePoint i v - c.point j‖ = 1 ↔
      ⟪c.clippingPairDirection i j, v⟫_ℝ = c.clippingPairCos i j := by
  have hr := ClippingCircle.radius_pos (Opposite.radius_gt_half_of_small_deficit c hA)
  have hproj := c.clippingPairProjection_norm_pos hA hij
  have he := c.clippingCircle_distance_sq_pair hA hij hv hp
  have hscale : 0 < 2 * ClippingCircle.radius c.radius * ‖c.clippingPairProjection i j‖ := by positivity
  constructor
  · intro h
    rw [h] at he
    have hz : (2 * ClippingCircle.radius c.radius * ‖c.clippingPairProjection i j‖) *
        (⟪c.clippingPairDirection i j, v⟫_ℝ - c.clippingPairCos i j) = 0 := by nlinarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left hscale.ne')
  · intro h
    rw [h, sub_self, mul_zero, add_zero] at he
    nlinarith [norm_nonneg (c.clippingCirclePoint i v - c.point j)]

end BlaschkeLebesgue.BalancedContacts
