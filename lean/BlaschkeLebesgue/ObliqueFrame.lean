module

public import BlaschkeLebesgue.ContactNormal
public import BlaschkeLebesgue.NormalFrame

/-!
# Two nonparallel axes and their common-normal coordinates

The transverse vectors are obtained algebraically from the two axes. Their
simultaneous sign is immaterial; they have the same Gram matrix as the axes.
All frame hypotheses are constructed from the actual contact configuration.
-/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue

structure ObliqueFrame where
  axis₁ : Space
  axis₂ : Space
  normal : Space
  axis₁_norm : ‖axis₁‖ = 1
  axis₂_norm : ‖axis₂‖ = 1
  normal_norm : ‖normal‖ = 1
  normal_inner_axis₁ : ⟪normal, axis₁⟫_ℝ = 0
  normal_inner_axis₂ : ⟪normal, axis₂⟫_ℝ = 0
  nonparallel : |⟪axis₁, axis₂⟫_ℝ| < 1

namespace ObliqueFrame

variable (f : ObliqueFrame)

@[expose] def chi : ℝ := ⟪f.axis₁, f.axis₂⟫_ℝ
@[expose] def sine : ℝ := Real.sqrt (1 - f.chi ^ 2)
@[expose] def transverse₁ : Space := f.sine⁻¹ • (f.axis₂ - f.chi • f.axis₁)
@[expose] def transverse₂ : Space := f.sine⁻¹ • (f.chi • f.axis₂ - f.axis₁)

theorem one_sub_chi_sq_pos : 0 < 1 - f.chi ^ 2 := by
  have h : |f.chi| < 1 := f.nonparallel
  have hh := (sq_lt_sq₀ (abs_nonneg _) zero_le_one).2 h
  rw [sq_abs, one_pow] at hh
  linarith

theorem sine_pos : 0 < f.sine := Real.sqrt_pos.2 f.one_sub_chi_sq_pos

theorem sine_sq : f.sine ^ 2 = 1 - f.chi ^ 2 := Real.sq_sqrt f.one_sub_chi_sq_pos.le

theorem transverse₁_norm : ‖f.transverse₁‖ = 1 := by
  have hs : ‖f.axis₂ - f.chi • f.axis₁‖ ^ 2 = f.sine ^ 2 := by
    rw [f.sine_sq]
    simp only [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      f.axis₁_norm, f.axis₂_norm, real_inner_smul_right, real_inner_comm f.axis₁ f.axis₂]
    change 1 ^ 2 - 2 * (f.chi * f.chi) + f.chi ^ 2 * 1 ^ 2 = 1 - f.chi ^ 2
    ring
  have hn : ‖f.axis₂ - f.chi • f.axis₁‖ = f.sine := by
    nlinarith [f.sine_pos, norm_nonneg (f.axis₂ - f.chi • f.axis₁)]
  simp only [transverse₁, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos f.sine_pos,
    hn, inv_mul_cancel₀ f.sine_pos.ne']

theorem transverse₂_norm : ‖f.transverse₂‖ = 1 := by
  have hs : ‖f.chi • f.axis₂ - f.axis₁‖ ^ 2 = f.sine ^ 2 := by
    rw [f.sine_sq]
    simp only [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      f.axis₁_norm, f.axis₂_norm, real_inner_smul_left, real_inner_comm f.axis₁ f.axis₂]
    change f.chi ^ 2 * 1 ^ 2 - 2 * (f.chi * f.chi) + 1 ^ 2 = 1 - f.chi ^ 2
    ring
  have hn : ‖f.chi • f.axis₂ - f.axis₁‖ = f.sine := by
    nlinarith [f.sine_pos, norm_nonneg (f.chi • f.axis₂ - f.axis₁)]
  simp only [transverse₂, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos f.sine_pos,
    hn, inv_mul_cancel₀ f.sine_pos.ne']

theorem axis₁_inner_transverse₁ : ⟪f.axis₁, f.transverse₁⟫_ℝ = 0 := by
  simp only [transverse₁, real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq,
    f.axis₁_norm]
  change f.sine⁻¹ * (f.chi - f.chi * 1 ^ 2) = 0
  ring

theorem axis₂_inner_transverse₂ : ⟪f.axis₂, f.transverse₂⟫_ℝ = 0 := by
  simp only [transverse₂, real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq,
    f.axis₂_norm, real_inner_comm f.axis₁ f.axis₂]
  change f.sine⁻¹ * (f.chi * 1 ^ 2 - f.chi) = 0
  ring

theorem normal_inner_transverse₁ : ⟪f.normal, f.transverse₁⟫_ℝ = 0 := by
  simp only [transverse₁, real_inner_smul_right, inner_sub_right,
    f.normal_inner_axis₁, f.normal_inner_axis₂, mul_zero, sub_self]

theorem normal_inner_transverse₂ : ⟪f.normal, f.transverse₂⟫_ℝ = 0 := by
  simp only [transverse₂, real_inner_smul_right, inner_sub_right,
    f.normal_inner_axis₁, f.normal_inner_axis₂, mul_zero, sub_self]

theorem transverse_inner : ⟪f.transverse₁, f.transverse₂⟫_ℝ = f.chi := by
  simp only [transverse₁, transverse₂, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
    f.axis₁_norm, f.axis₂_norm, real_inner_comm f.axis₁ f.axis₂]
  change f.sine⁻¹ * (f.chi * (f.sine⁻¹ * (1 ^ 2 - f.chi * f.chi)) -
    f.sine⁻¹ * (f.chi - f.chi * 1 ^ 2)) = f.chi
  field_simp [f.sine_pos.ne']
  rw [f.sine_sq]
  ring

theorem exists_first_basis : ∃ b : OrthonormalBasis (Fin 3) ℝ Space,
    b 0 = f.normal ∧ b 1 = f.axis₁ ∧ b 2 = f.transverse₁ := by
  let v : Fin 3 → Space := ![f.normal, f.axis₁, f.transverse₁]
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [v, f.normal_norm, f.axis₁_norm, f.transverse₁_norm,
        f.normal_inner_axis₁, f.normal_inner_transverse₁, f.axis₁_inner_transverse₁,
        real_inner_comm f.normal f.axis₁, real_inner_comm f.normal f.transverse₁,
        real_inner_comm f.axis₁ f.transverse₁]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range v) :=
    (hv.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [Space])).ge
  refine ⟨OrthonormalBasis.mk hv hspan, ?_, ?_, ?_⟩ <;>
    simp [OrthonormalBasis.coe_mk, v]

theorem decompose_first (x : Space) :
    x = ⟪f.normal, x⟫_ℝ • f.normal + ⟪f.axis₁, x⟫_ℝ • f.axis₁ +
      ⟪f.transverse₁, x⟫_ℝ • f.transverse₁ := by
  obtain ⟨b, hb0, hb1, hb2⟩ := f.exists_first_basis
  have h := b.sum_repr' x
  norm_num [Fin.sum_univ_succ, Fin.succ, hb0, hb1, hb2] at h
  simpa only [add_assoc] using h.symm

@[expose] def swap : ObliqueFrame where
  axis₁ := f.axis₂
  axis₂ := f.axis₁
  normal := -f.normal
  axis₁_norm := f.axis₂_norm
  axis₂_norm := f.axis₁_norm
  normal_norm := by rw [norm_neg, f.normal_norm]
  normal_inner_axis₁ := by rw [inner_neg_left, f.normal_inner_axis₂, neg_zero]
  normal_inner_axis₂ := by rw [inner_neg_left, f.normal_inner_axis₁, neg_zero]
  nonparallel := by simpa only [real_inner_comm f.axis₁ f.axis₂] using f.nonparallel

theorem swap_chi : f.swap.chi = f.chi := real_inner_comm f.axis₁ f.axis₂
theorem swap_sine : f.swap.sine = f.sine := by simp only [sine, swap_chi]

theorem swap_transverse₁ : f.swap.transverse₁ = -f.transverse₂ := by
  simp only [transverse₁, transverse₂]
  rw [f.swap_chi, f.swap_sine]
  change f.sine⁻¹ • (f.axis₁ - f.chi • f.axis₂) = - (f.sine⁻¹ • (f.chi • f.axis₂ - f.axis₁))
  module

theorem swap_transverse₂ : f.swap.transverse₂ = -f.transverse₁ := by
  simp only [transverse₁, transverse₂]
  rw [f.swap_chi, f.swap_sine]
  change f.sine⁻¹ • (f.chi • f.axis₁ - f.axis₂) = - (f.sine⁻¹ • (f.axis₂ - f.chi • f.axis₁))
  module

theorem decompose_second (x : Space) :
    x = ⟪f.normal, x⟫_ℝ • f.normal + ⟪f.axis₂, x⟫_ℝ • f.axis₂ +
      ⟪f.transverse₂, x⟫_ℝ • f.transverse₂ := by
  have h := f.swap.decompose_first x
  rw [f.swap_transverse₁] at h
  simpa only [swap, inner_neg_left, neg_smul, smul_neg, neg_neg] using h

theorem norm_sq_of_perp_firstAxis {x : Space} (hx : ⟪f.axis₁, x⟫_ℝ = 0) :
    ‖x‖ ^ 2 = ⟪f.normal, x⟫_ℝ ^ 2 + ⟪f.transverse₁, x⟫_ℝ ^ 2 := by
  have h := congrArg (fun y : Space ↦ ‖y‖ ^ 2) (f.decompose_first x)
  simp only [hx, zero_smul, add_zero, norm_add_sq_real, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, f.normal_norm, f.transverse₁_norm,
    real_inner_smul_left, real_inner_smul_right, f.normal_inner_transverse₁] at h
  nlinarith

theorem norm_sq_of_perp_secondAxis {x : Space} (hx : ⟪f.axis₂, x⟫_ℝ = 0) :
    ‖x‖ ^ 2 = ⟪f.normal, x⟫_ℝ ^ 2 + ⟪f.transverse₂, x⟫_ℝ ^ 2 := by
  have h := congrArg (fun y : Space ↦ ‖y‖ ^ 2) (f.decompose_second x)
  simp only [hx, zero_smul, add_zero, norm_add_sq_real, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, f.normal_norm, f.transverse₂_norm,
    real_inner_smul_left, real_inner_smul_right, f.normal_inner_transverse₂] at h
  nlinarith

theorem normal_alignment_first {x : Space} (hx : ‖x‖ = 1)
    (haxis : ⟪f.axis₁, x⟫_ℝ = 0) (hn : 0 ≤ ⟪f.normal, x⟫_ℝ)
    {η : ℝ} (hη : |⟪f.transverse₁, x⟫_ℝ| ≤ η) :
    Real.sqrt (1 - η ^ 2) ≤ ⟪f.normal, x⟫_ℝ := by
  have h := f.norm_sq_of_perp_firstAxis haxis
  rw [hx, one_pow] at h
  have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hη)).2 hη
  rw [sq_abs] at hsq
  apply (Real.sqrt_le_left hn).2
  linarith

theorem normal_alignment_second {x : Space} (hx : ‖x‖ = 1)
    (haxis : ⟪f.axis₂, x⟫_ℝ = 0) (hn : 0 ≤ ⟪f.normal, x⟫_ℝ)
    {η : ℝ} (hη : |⟪f.transverse₂, x⟫_ℝ| ≤ η) :
    Real.sqrt (1 - η ^ 2) ≤ ⟪f.normal, x⟫_ℝ := by
  have h := f.norm_sq_of_perp_secondAxis haxis
  rw [hx, one_pow] at h
  have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hη)).2 hη
  rw [sq_abs] at hsq
  apply (Real.sqrt_le_left hn).2
  linarith

end ObliqueFrame

namespace BalancedContacts.Opposite

theorem exists_obliqueFrame (c : BalancedContacts 4 Space) (hA : c.totalDeficit ≤ 2 / 25) :
    ∃ f : ObliqueFrame, f.axis₁ = firstAxis c ∧ f.axis₂ = secondAxis c ∧
      ⟪firstMidpoint c, f.normal⟫_ℝ < 0 ∧ 0 < ⟪secondMidpoint c, f.normal⟫_ℝ := by
  obtain ⟨z, hz, h1, h2, hm1, hm2⟩ := oriented_common_normal c hA
  have ha : edgeBudget c < 1 := by linarith [budgets_sum c, crossBudget_nonneg c]
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  have hc := (axes_inner_abs c ha).trans
    (Completion.obliquity_bounds (edgeBudget_nonneg c) (crossBudget_nonneg c) hab).2
  exact ⟨{
    axis₁ := firstAxis c
    axis₂ := secondAxis c
    normal := z
    axis₁_norm := firstAxis_norm c ha
    axis₂_norm := secondAxis_norm c ha
    normal_norm := hz
    normal_inner_axis₁ := h1
    normal_inner_axis₂ := h2
    nonparallel := by linarith }, rfl, rfl, hm1, hm2⟩

end BalancedContacts.Opposite
end BlaschkeLebesgue
