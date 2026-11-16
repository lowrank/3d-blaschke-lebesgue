module

public import BlaschkeLebesgue.CompletionPhi
public import BlaschkeLebesgue.ProjectiveAllocation

/-! # Convexity averages the actual edge obliquity before taking a worst case -/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Completion

def averagedW (t x y : ℝ) : ℝ := 1 + (x ^ 2 + y ^ 2) / (1 - t ^ 2)
def uniformW (a b x y : ℝ) : ℝ := averagedW (obliquity a b) x y

theorem allocationNumerator_neg_right (a b x y : ℝ) :
    allocationNumerator a b x (-y) = allocationNumerator a b x y := by
  simp only [allocationNumerator, neg_sq]

theorem determinantFactor_neg_right (a x y : ℝ) : determinantFactor a x (-y) = determinantFactor a x y := by
  simp only [determinantFactor, neg_sq]

theorem edgeRadius_gt_four_fifths {a : ℝ} (ha : 0 ≤ a) : 4 / 5 < edgeRadius a := by
  have hp := edgeRadius_pos ha
  have hs := edgeRadius_sq ha
  nlinarith

theorem determinantFactor_pos {a : ℝ} (ha : 0 ≤ a) (x y : ℝ) : 0 < determinantFactor a x y := by
  apply div_pos (edgeRadius_pos ha)
  apply Real.sqrt_pos.2
  have h := le_min (sq_nonneg x) (sq_nonneg y)
  linarith

theorem allocationNumerator_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)
    (x y : ℝ) : 0 < allocationNumerator a b x y := by
  have hs : separationUpper a b ≤ 3 / 4 := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3 / 4)).2
    linarith
  have hmax : 1 ≤ Real.sqrt (1 + max (x ^ 2) (y ^ 2)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg x, le_max_left (x ^ 2) (y ^ 2)]
  have hmin : 1 ≤ Real.sqrt (1 + min (x ^ 2) (y ^ 2)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [le_min (sq_nonneg x) (sq_nonneg y)]
  have h0 := edgeRadius_gt_four_fifths (by norm_num : (0 : ℝ) ≤ 0)
  have hr := edgeRadius_gt_four_fifths ha
  have hm1 := mul_le_mul_of_nonneg_left hmax (edgeRadius_pos (by norm_num : (0 : ℝ) ≤ 0)).le
  have hm2 := mul_le_mul_of_nonneg_left hmin (edgeRadius_pos ha).le
  unfold allocationNumerator
  nlinarith only [hs, h0, hr, hm1, hm2]

theorem determinantFactor_sqrt_lower {a W : ℝ} (ha : 0 ≤ a) (x y : ℝ)
    (hW : 1 + max (x ^ 2) (y ^ 2) ≤ W) : 4 / 5 ≤ determinantFactor a x y * Real.sqrt W := by
  have hmin : 0 ≤ min (x ^ 2) (y ^ 2) := le_min (sq_nonneg _) (sq_nonneg _)
  have hd : 0 < Real.sqrt (1 + min (x ^ 2) (y ^ 2)) := Real.sqrt_pos.2 (by linarith)
  have hs : Real.sqrt (1 + min (x ^ 2) (y ^ 2)) ≤ Real.sqrt W := by
    apply Real.sqrt_le_sqrt
    linarith [show min (x ^ 2) (y ^ 2) ≤ max (x ^ 2) (y ^ 2) from min_le_max]
  have h := mul_le_mul_of_nonneg_left hs (determinantFactor_pos ha x y).le
  have he : determinantFactor a x y * Real.sqrt (1 + min (x ^ 2) (y ^ 2)) = edgeRadius a := by
    unfold determinantFactor
    field_simp
  rw [he] at h
  exact (edgeRadius_gt_four_fifths ha).le.trans h

theorem averagedW_ge {t x y : ℝ} (ht : |t| < 1) : 1 + max (x ^ 2) (y ^ 2) ≤ averagedW t x y := by
  have hd : 0 < 1 - t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have hsum : max (x ^ 2) (y ^ 2) ≤ x ^ 2 + y ^ 2 := by
    exact max_le (by nlinarith [sq_nonneg y]) (by nlinarith [sq_nonneg x])
  have hs : x ^ 2 + y ^ 2 ≤ (x ^ 2 + y ^ 2) / (1 - t ^ 2) := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg (add_nonneg (sq_nonneg x) (sq_nonneg y)) (sq_nonneg t)]
  unfold averagedW
  linarith

theorem averagedW_le {t v x y : ℝ} (hv : 0 ≤ v) (hv1 : v < 1) (ht : |t| ≤ v) :
    averagedW t x y ≤ averagedW v x y := by
  have hs := (sq_le_sq₀ (abs_nonneg t) hv).2 ht
  rw [sq_abs] at hs
  have hdv : 0 < 1 - v ^ 2 := by nlinarith
  have hd : 1 - v ^ 2 ≤ 1 - t ^ 2 := by linarith
  unfold averagedW
  have h := div_le_div_of_nonneg_left (add_nonneg (sq_nonneg x) (sq_nonneg y)) hdv hd
  linarith

end Completion

namespace ObliqueFrame

variable (f : ObliqueFrame)

theorem W_ge_one_add_max_sq (x y : ℝ) : 1 + max (x ^ 2) (y ^ 2) ≤ f.W x y := by
  rcases le_total (x ^ 2) (y ^ 2) with h | h
  · rw [max_eq_right h]
    exact f.W_ge_one_add_second_sq x y
  · rw [max_eq_left h]
    exact f.W_ge_one_add_first_sq x y

theorem W_sign_average (x y : ℝ) :
    (f.W x y + f.W x (-y)) / 2 = Completion.averagedW f.chi x y := by
  unfold W Completion.averagedW
  ring

theorem phi_sign_average_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)
    (hchi : |f.chi| ≤ Completion.obliquity a b) (x y : ℝ) :
    2 * Completion.phi (Completion.allocationNumerator a b x y) (Completion.determinantFactor a x y)
        (Completion.uniformW a b x y) ≤
      Completion.phi (Completion.allocationNumerator a b x y) (Completion.determinantFactor a x y) (f.W x y) +
        Completion.phi (Completion.allocationNumerator a b x y) (Completion.determinantFactor a x y) (f.W x (-y)) := by
  have hN := Completion.allocationNumerator_pos ha hb hab x y
  have hz := Completion.determinantFactor_pos ha x y
  have hL : 0 < 1 + max (x ^ 2) (y ^ 2) := by
    nlinarith [sq_nonneg x, le_max_left (x ^ 2) (y ^ 2)]
  have hv := Completion.determinantFactor_sqrt_lower ha x y (le_refl (1 + max (x ^ 2) (y ^ 2)))
  have hc := Completion.phi_convexOn hN hz hL hv
  have h1 := f.W_ge_one_add_max_sq x y
  have h2 : 1 + max (x ^ 2) (y ^ 2) ≤ f.W x (-y) := by
    simpa only [neg_sq] using f.W_ge_one_add_max_sq x (-y)
  have hj := hc.2 h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  have he : (1 / 2 : ℝ) * f.W x y + (1 / 2 : ℝ) * f.W x (-y) = (f.W x y + f.W x (-y)) / 2 := by ring
  rw [he, f.W_sign_average] at hj
  have ho := Completion.obliquity_bounds ha hb hab
  have hmean : 1 + max (x ^ 2) (y ^ 2) ≤ Completion.averagedW f.chi x y :=
    Completion.averagedW_ge (x := x) (y := y) f.nonparallel
  have hmax := Completion.averagedW_le (x := x) (y := y) ho.1 (by linarith [ho.2]) hchi
  have hm := Completion.phi_antitoneOn hN.le hz.le hL hv hmean (hmean.trans hmax) hmax
  change Completion.phi _ _ (Completion.uniformW a b x y) ≤ _ at hm
  linarith only [hj, hm]

end ObliqueFrame

namespace BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space) (f : ObliqueFrame)

theorem projective_phi_sign_average_lower (h1 : f.axis₁ = firstAxis c) (h2 : f.axis₂ = secondAxis c)
    (hA : c.totalDeficit ≤ 2 / 25) (x y : ℝ) :
    2 * Completion.phi (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
        (Completion.determinantFactor (edgeBudget c) x y) (Completion.uniformW (edgeBudget c) (crossBudget c) x y) ≤
      Completion.phi (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
        (Completion.determinantFactor (edgeBudget c) x y) (f.W x y) +
      Completion.phi (Completion.allocationNumerator (edgeBudget c) (crossBudget c) x y)
        (Completion.determinantFactor (edgeBudget c) x y) (f.W x (-y)) := by
  have hab : edgeBudget c + crossBudget c ≤ 2 / 25 := by rw [budgets_sum]; exact hA
  apply f.phi_sign_average_lower (edgeBudget_nonneg c) (crossBudget_nonneg c) hab _ x y
  have ha : edgeBudget c < 1 := by linarith [crossBudget_nonneg c]
  simpa only [ObliqueFrame.chi, h1, h2, Completion.obliquity] using axes_inner_abs c ha

end BalancedContacts.Opposite
end BlaschkeLebesgue
