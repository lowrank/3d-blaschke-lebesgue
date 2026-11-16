module

public import BlaschkeLebesgue.CompletionRegion

/-! # The exact rectangle width implies strict clipping-angle inequalities -/

public noncomputable section

namespace BlaschkeLebesgue.Completion

variable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25)

include ha hb hab

theorem rectangleRadius_angle_identity :
    arcCos a b * Real.sqrt (1 + rectangleRadius a b ^ 2) +
      midpointError a b * rectangleRadius a b = Real.sqrt (1 - midpointError a b ^ 2) := by
  let C := arcCos a b
  let S := arcSin a b
  let η := midpointError a b
  let R := Real.sqrt (1 - η ^ 2)
  let D := C * R + S * η
  let P := S * R - C * η
  have he := midpointError_bounds ha hb hab
  have hCS : C ^ 2 + S ^ 2 = 1 := by
    have h := arcSin_sq ha hb hab
    dsimp only [C, S]
    linarith
  have hR : R ^ 2 + η ^ 2 = 1 := by
    have hh : 0 ≤ 1 - η ^ 2 := by
      dsimp only [η]
      nlinarith [sq_nonneg (midpointError a b - 1 / 16)]
    dsimp only [R]
    rw [Real.sq_sqrt hh]
    ring
  have hD : 0 < D := rectangleRadius_denominator_pos ha hb hab
  have hDP : D ^ 2 + P ^ 2 = 1 := by
    calc
      _ = (C ^ 2 + S ^ 2) * (R ^ 2 + η ^ 2) := by dsimp only [D, P]; ring
      _ = 1 := by rw [hCS, hR]; ring
  have hT : rectangleRadius a b = P / D := rfl
  have hroot : Real.sqrt (1 + rectangleRadius a b ^ 2) = 1 / D := by
    have hin : 1 + rectangleRadius a b ^ 2 = 1 / D ^ 2 := by
      rw [hT]
      field_simp
      nlinarith
    rw [hin, Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq hD.le]
  have hinverse : C + η * P = R * D := by
    dsimp only [P, D]
    nlinarith [show C * (R ^ 2 + η ^ 2) = C by rw [hR]; ring]
  change C * Real.sqrt (1 + rectangleRadius a b ^ 2) + η * rectangleRadius a b = R
  rw [hroot, hT]
  rw [show C * (1 / D) + η * (P / D) = (C + η * P) / D by ring]
  exact (div_eq_iff hD.ne').2 hinverse

/-- This is the algebraic form of the angular margin; no inverse-trigonometric
identity or branch choice is needed. -/
theorem rectangle_projection_margin {x : ℝ} (hx : |x| < rectangleRadius a b) :
    arcCos a b < (Real.sqrt (1 - midpointError a b ^ 2) - midpointError a b * |x|) /
      Real.sqrt (1 + x ^ 2) := by
  have hC := (arcCos_bounds ha hb hab).1
  have hη := (midpointError_bounds ha hb hab).1
  have hT : 0 < rectangleRadius a b := by linarith [(rectangleRadius_bounds ha hb hab).1]
  have hsq := (sq_lt_sq₀ (abs_nonneg x) hT.le).2 hx
  rw [sq_abs] at hsq
  have hroots : Real.sqrt (1 + x ^ 2) < Real.sqrt (1 + rectangleRadius a b ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hsum := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hroots hC)
    (mul_le_mul_of_nonneg_left hx.le hη)
  rw [rectangleRadius_angle_identity ha hb hab] at hsum
  apply (lt_div_iff₀ (by positivity)).2
  linarith

end BlaschkeLebesgue.Completion
