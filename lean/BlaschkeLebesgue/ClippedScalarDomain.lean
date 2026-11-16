module

public import BlaschkeLebesgue.ManuscriptVolumeFormula
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Scalar domains and the differentiated arccosine quotient -/

public noncomputable section

namespace BlaschkeLebesgue

theorem hasDerivAt_arccos_quotient {u v : ℝ → ℝ} {du dv x q : ℝ}
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x) (hv0 : 0 < v x) (hq : 0 < q)
    (hgram : v x ^ 2 - u x ^ 2 = q ^ 2) :
    HasDerivAt (fun z ↦ Real.arccos (u z / v z))
      ((u x * dv - du * v x) / (v x * q)) x := by
  have hsq : 1 - (u x / v x) ^ 2 = (q / v x) ^ 2 := by
    field_simp
    nlinarith only [hgram]
  have hpos : 0 < 1 - (u x / v x) ^ 2 := by rw [hsq]; positivity
  have hrt : Real.sqrt (1 - (u x / v x) ^ 2) = q / v x := by
    rw [hsq, Real.sqrt_sq (div_pos hq hv0).le]
  have hn : u x / v x ≠ -1 := by intro h; rw [h] at hpos; norm_num at hpos
  have hp : u x / v x ≠ 1 := by intro h; rw [h] at hpos; norm_num at hpos
  have hc := (Real.hasDerivAt_arccos hn hp).comp x (hu.div hv hv0.ne')
  rw [hrt] at hc
  convert hc using 1
  · rfl
  · field_simp
    ring

namespace ClippedDifferential

@[expose] def Domain (R x : ℝ) : Prop :=
  1 / 2 < R ∧ 0 < x ∧ x ≤ 1 ∧ 0 < R ^ 2 * (4 - x) - 1

@[expose] def s (x : ℝ) : ℝ := Real.sqrt x
@[expose] def r (x : ℝ) : ℝ := Real.sqrt (1 - x / 4)
@[expose] def m (R x : ℝ) : ℝ := Real.sqrt (R ^ 2 - x / 4)
@[expose] def q (R x : ℝ) : ℝ := Real.sqrt (R ^ 2 * (4 - x) - 1)
@[expose] def k (R : ℝ) : ℝ := ClippingCircle.radius R
@[expose] def U (R x : ℝ) : ℝ := Real.arccos (s x / (4 * R * r x * k R))
@[expose] def V (R x : ℝ) : ℝ := Real.arccos ((2 * k R ^ 2 - x) / (2 * k R ^ 2))
@[expose] def Psi (R x : ℝ) : ℝ :=
  Real.arccos ((1 - 2 * R ^ 2) * s x / (4 * R * k R * m R x))
@[expose] def phi (R x : ℝ) : ℝ := 2 * Real.arccos ((1 - x / 2) / (2 * r x * m R x))
@[expose] def T (R x : ℝ) : ℝ := s x * q R x
@[expose] def theta (x : ℝ) : ℝ := Real.arcsin (s x / 2)
@[expose] def F (x : ℝ) : ℝ := s x / 2 - s x ^ 3 / 24 - r x * theta x

namespace Domain

variable {R x : ℝ} (h : Domain R x)
include h

theorem R_pos : 0 < R := by linarith [h.1]
theorem R_sq_gt_quarter : 1 / 4 < R ^ 2 := by nlinarith [h.1]
theorem r_radicand_pos : 0 < 1 - x / 4 := by linarith [h.2.2.1]
theorem m_radicand_pos : 0 < R ^ 2 - x / 4 := by linarith [h.R_sq_gt_quarter, h.2.2.1]
theorem s_pos : 0 < s x := Real.sqrt_pos.2 h.2.1
theorem r_pos : 0 < r x := Real.sqrt_pos.2 h.r_radicand_pos
theorem m_pos : 0 < m R x := Real.sqrt_pos.2 h.m_radicand_pos
theorem q_pos : 0 < q R x := Real.sqrt_pos.2 h.2.2.2
theorem k_pos : 0 < k R := ClippingCircle.radius_pos h.1
theorem s_sq : s x ^ 2 = x := Real.sq_sqrt h.2.1.le
theorem r_sq : r x ^ 2 = 1 - x / 4 := Real.sq_sqrt h.r_radicand_pos.le
theorem m_sq : m R x ^ 2 = R ^ 2 - x / 4 := Real.sq_sqrt h.m_radicand_pos.le
theorem q_sq : q R x ^ 2 = R ^ 2 * (4 - x) - 1 := Real.sq_sqrt h.2.2.2.le
theorem k_sq : k R ^ 2 = 1 - 1 / (4 * R ^ 2) := ClippingCircle.radius_sq h.1

theorem U_gram : (4 * R * r x * k R) ^ 2 - s x ^ 2 = (2 * q R x) ^ 2 := by
  simp only [mul_pow, h.r_sq, h.k_sq, h.s_sq, h.q_sq]
  have hR := h.R_pos.ne'
  field_simp
  ring

theorem V_gram : (2 * k R ^ 2) ^ 2 - (2 * k R ^ 2 - x) ^ 2 = (s x * q R x / R) ^ 2 := by
  simp only [div_pow, mul_pow, h.s_sq, h.q_sq, h.k_sq]
  have hR := h.R_pos.ne'
  field_simp
  ring

theorem Psi_gram : (4 * R * k R * m R x) ^ 2 - ((1 - 2 * R ^ 2) * s x) ^ 2 =
    (2 * R * q R x) ^ 2 := by
  simp only [mul_pow, h.m_sq, h.k_sq, h.s_sq, h.q_sq]
  have hR := h.R_pos.ne'
  field_simp
  ring

theorem phi_gram : (2 * r x * m R x) ^ 2 - (1 - x / 2) ^ 2 = q R x ^ 2 := by
  simp only [mul_pow, h.r_sq, h.m_sq, h.q_sq]
  ring

theorem hasDerivAt_s : HasDerivAt s (1 / (2 * s x)) x := Real.hasDerivAt_sqrt h.2.1.ne'

theorem hasDerivAt_r : HasDerivAt r (-1 / (8 * r x)) x := by
  have hd := (((hasDerivAt_id x).div_const 4).const_sub 1).sqrt h.r_radicand_pos.ne'
  convert hd using 1
  · rfl
  · dsimp only [r, id_eq]
    ring

theorem hasDerivAt_m : HasDerivAt (m R) (-1 / (8 * m R x)) x := by
  have hd := (((hasDerivAt_id x).div_const 4).const_sub (R ^ 2)).sqrt h.m_radicand_pos.ne'
  convert hd using 1
  · rfl
  · dsimp only [m, id_eq]
    ring

theorem hasDerivAt_q : HasDerivAt (q R) (-R ^ 2 / (2 * q R x)) x := by
  have hd := ((((hasDerivAt_id x).const_sub 4).const_mul (R ^ 2)).sub_const 1).sqrt h.2.2.2.ne'
  convert hd using 1
  · rfl
  · dsimp only [q, id_eq]
    ring

end Domain

theorem domain_of_hull_rectangle {R x : ℝ} (hR : 60849 / 100000 ≤ R)
    (hx : 23 / 25 ≤ x) (hx1 : x ≤ 1) : Domain R x := by
  have hR0 : 0 < R := by linarith
  have hR2 : 37 / 100 ≤ R ^ 2 := by nlinarith
  refine ⟨by linarith, by linarith, hx1, ?_⟩
  nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hx1)]

end ClippedDifferential
end BlaschkeLebesgue
