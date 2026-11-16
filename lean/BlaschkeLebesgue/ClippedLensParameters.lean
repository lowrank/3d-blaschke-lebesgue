module

public import BlaschkeLebesgue.CapLensFormula
public import BlaschkeLebesgue.ClippingCircleCuts

/-! # Verified scalar parameters of the clipped face lenses -/

public noncomputable section

open Set

namespace BlaschkeLebesgue

namespace ClippedLens

@[expose] def unitHeight (R : ℝ) : ℝ := 1 / (2 * R)
@[expose] def neighborHeight (s : ℝ) : ℝ := s / 2
@[expose] def unitAxisInner (R s : ℝ) : ℝ := s / (2 * R)
@[expose] def radiusHeight (R : ℝ) : ℝ := 1 / (2 * R ^ 2) - 1
@[expose] def radiusAxisInner (R s : ℝ) : ℝ := 1 - s ^ 2 / (2 * R ^ 2)

theorem unit_gram (R s : ℝ) (hR : R ≠ 0) :
    lensGram (unitHeight R) (neighborHeight s) (unitAxisInner R s) =
      (R ^ 2 * (4 - s ^ 2) - 1) / (4 * R ^ 2) := by
  unfold lensGram unitHeight neighborHeight unitAxisInner
  field_simp
  ring

theorem radius_gram (R s : ℝ) (hR : R ≠ 0) :
    lensGram (radiusHeight R) (radiusHeight R) (radiusAxisInner R s) =
      s ^ 2 * (R ^ 2 * (4 - s ^ 2) - 1) / (4 * R ^ 6) := by
  unfold lensGram radiusHeight radiusAxisInner
  field_simp
  ring

theorem unit_parameters {R s : ℝ} (hR : 0 < R) (hRlo : 37 / 100 ≤ R ^ 2)
    (hRhi : R ^ 2 ≤ 3 / 8) (hs : 0 < s) (hs1 : s ≤ 1) :
    unitHeight R ∈ Ioo (-1 : ℝ) 1 ∧ neighborHeight s ∈ Ioo (-1 : ℝ) 1 ∧
      unitAxisInner R s ∈ Ioo (-1 : ℝ) 1 ∧ neighborHeight s ≠ unitAxisInner R s ∧
      0 < lensGram (unitHeight R) (neighborHeight s) (unitAxisInner R s) := by
  have hRhalf : 1 / 2 < R := by nlinarith
  have hR1 : R < 1 := by nlinarith
  have hden : 0 < 2 * R := by positivity
  have ha : 0 < unitHeight R := by unfold unitHeight; positivity
  have hb : 0 < neighborHeight s := by unfold neighborHeight; positivity
  have hc : 0 < unitAxisInner R s := by unfold unitAxisInner; positivity
  have ha1 : unitHeight R < 1 := by
    unfold unitHeight
    exact (div_lt_one hden).2 (by linarith)
  have hc1 : unitAxisInner R s < 1 := by
    unfold unitAxisInner
    exact (div_lt_one hden).2 (by linarith)
  have hbc : neighborHeight s < unitAxisInner R s := by
    unfold neighborHeight unitAxisInner
    apply (lt_div_iff₀ hden).2
    nlinarith [mul_pos hs (sub_pos.2 hR1)]
  refine ⟨⟨by linarith, ha1⟩, ⟨by linarith, by dsimp [neighborHeight]; linarith⟩,
    ⟨by linarith, hc1⟩, ne_of_lt hbc, ?_⟩
  rw [unit_gram R s hR.ne']
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hp := mul_nonneg (sq_nonneg R) (sub_nonneg.2 hs2)
  exact div_pos (by nlinarith) (by positivity)

theorem radius_parameters {R s : ℝ} (hR : 0 < R) (hRlo : 37 / 100 ≤ R ^ 2)
    (hRhi : R ^ 2 ≤ 3 / 8) (hs : 0 < s) (hs1 : s ≤ 1) (hslo : 23 / 25 ≤ s ^ 2) :
    radiusHeight R ∈ Ioo (-1 : ℝ) 1 ∧ radiusAxisInner R s ∈ Ioo (-1 : ℝ) 1 ∧
      radiusHeight R ≠ radiusAxisInner R s ∧
      0 < lensGram (radiusHeight R) (radiusHeight R) (radiusAxisInner R s) := by
  have hden : 0 < 2 * R ^ 2 := by positivity
  have hq0 : 0 < radiusHeight R := by
    unfold radiusHeight
    have h := (lt_div_iff₀ hden).2 (show 1 * (2 * R ^ 2) < 1 by nlinarith)
    linarith
  have hq1 : radiusHeight R < 1 := by
    unfold radiusHeight
    have h := (div_lt_iff₀ hden).2 (show 1 < 2 * (2 * R ^ 2) by nlinarith)
    linarith
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hc0 : -1 < radiusAxisInner R s := by
    unfold radiusAxisInner
    have h := (div_lt_iff₀ hden).2 (show s ^ 2 < 2 * (2 * R ^ 2) by nlinarith)
    linarith
  have hc1 : radiusAxisInner R s < 1 := by
    unfold radiusAxisInner
    have h := div_pos (sq_pos_of_pos hs) hden
    linarith
  have hcb : radiusAxisInner R s < radiusHeight R := by
    unfold radiusAxisInner radiusHeight
    have h : 2 < (1 + s ^ 2) / (2 * R ^ 2) := (lt_div_iff₀ hden).2 (by nlinarith)
    rw [add_div] at h
    linarith
  refine ⟨⟨by linarith, hq1⟩, ⟨hc0, hc1⟩, ne_of_gt hcb, ?_⟩
  rw [radius_gram R s hR.ne']
  have hp := mul_nonneg (sq_nonneg R) (sub_nonneg.2 hs2)
  exact div_pos (mul_pos (sq_pos_of_pos hs) (by nlinarith)) (by positivity)

end ClippedLens

namespace BalancedContacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (c : BalancedContacts 4 E)

theorem edgeDeficit_le_totalDeficit {i j : Fin 4} (hij : i ≠ j) :
    c.edgeDeficit i j ≤ c.totalDeficit := by
  have h01 := c.edgeDeficit_nonneg 0 1
  have h02 := c.edgeDeficit_nonneg 0 2
  have h03 := c.edgeDeficit_nonneg 0 3
  have h12 := c.edgeDeficit_nonneg 1 2
  have h13 := c.edgeDeficit_nonneg 1 3
  have h23 := c.edgeDeficit_nonneg 2 3
  have h01' : c.edgeDeficit 0 1 ≤ c.totalDeficit := by unfold totalDeficit; linarith
  have h02' : c.edgeDeficit 0 2 ≤ c.totalDeficit := by unfold totalDeficit; linarith
  have h03' : c.edgeDeficit 0 3 ≤ c.totalDeficit := by unfold totalDeficit; linarith
  have h12' : c.edgeDeficit 1 2 ≤ c.totalDeficit := by unfold totalDeficit; linarith
  have h13' : c.edgeDeficit 1 3 ≤ c.totalDeficit := by unfold totalDeficit; linarith
  have h23' : c.edgeDeficit 2 3 ≤ c.totalDeficit := by unfold totalDeficit; linarith
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals first
    | exact h01' | exact h02' | exact h03' | exact h12' | exact h13' | exact h23'
    | exact (c.edgeDeficit_symm _ _).le.trans h01'
    | exact (c.edgeDeficit_symm _ _).le.trans h02'
    | exact (c.edgeDeficit_symm _ _).le.trans h03'
    | exact (c.edgeDeficit_symm _ _).le.trans h12'
    | exact (c.edgeDeficit_symm _ _).le.trans h13'
    | exact (c.edgeDeficit_symm _ _).le.trans h23'

theorem clipped_lens_parameter_bounds (hA : c.totalDeficit ≤ 2 / 25) {i j : Fin 4} (hij : i ≠ j) :
    0 < c.radius ∧ 37 / 100 ≤ c.radius ^ 2 ∧ c.radius ^ 2 ≤ 3 / 8 ∧
      0 < ‖c.point j - c.point i‖ ∧ ‖c.point j - c.point i‖ ≤ 1 ∧
      23 / 25 ≤ ‖c.point j - c.point i‖ ^ 2 := by
  have hR : 0 < c.radius := lt_trans (by norm_num)
    (Opposite.radius_gt_half_of_small_deficit c hA)
  have he := (c.edgeDeficit_le_totalDeficit (Ne.symm hij)).trans hA
  unfold edgeDeficit at he
  refine ⟨hR, by linarith [c.deficit_lower], c.radius_sq_le (by decide),
    ?_, c.diameter_le j i, by linarith⟩
  nlinarith [norm_nonneg (c.point j - c.point i)]

end BalancedContacts
end BlaschkeLebesgue
