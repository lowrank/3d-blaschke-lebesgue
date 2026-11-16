module

public import BlaschkeLebesgue.ClippedScalarDomain

/-! # Exact edge-angle derivatives in the squared edge length -/

public noncomputable section

namespace BlaschkeLebesgue.ClippedDifferential.Domain

variable {R x : ℝ} (h : Domain R x)
include h

theorem hasDerivAt_U : HasDerivAt (U R) (-1 / (s x * (4 - x) * q R x)) x := by
  have hv := (h.hasDerivAt_r.const_mul (4 * R)).mul_const (k R)
  have hd := hasDerivAt_arccos_quotient h.hasDerivAt_s hv
    (by positivity [h.R_pos, h.r_pos, h.k_pos])
    (by positivity [h.q_pos]) h.U_gram
  have hs := h.s_pos.ne'
  have hr := h.r_pos.ne'
  have hR := h.R_pos.ne'
  have hk := h.k_pos.ne'
  have hq := h.q_pos.ne'
  have hx4 : 4 - x ≠ 0 := by linarith [h.2.2.1]
  convert hd using 1
  · rfl
  · field_simp
    ring_nf
    simp only [h.s_sq, h.r_sq]
    field_simp
    ring

theorem hasDerivAt_V : HasDerivAt (V R) (R / (s x * q R x)) x := by
  have hu := (hasDerivAt_id x).const_sub (2 * k R ^ 2)
  have hv := hasDerivAt_const x (2 * k R ^ 2)
  have hd := hasDerivAt_arccos_quotient hu hv
    (by positivity [h.k_pos]) (by positivity [h.s_pos, h.q_pos, h.R_pos]) h.V_gram
  have hs := h.s_pos.ne'
  have hk := h.k_pos.ne'
  have hR := h.R_pos.ne'
  have hq := h.q_pos.ne'
  convert hd using 1
  · rfl
  · dsimp only [id_eq]
    field_simp
    ring

theorem hasDerivAt_Psi : HasDerivAt (Psi R)
    (-R * (1 - 2 * R ^ 2) / (s x * (4 * R ^ 2 - x) * q R x)) x := by
  have hu := h.hasDerivAt_s.const_mul (1 - 2 * R ^ 2)
  have hv := h.hasDerivAt_m.const_mul (4 * R * k R)
  have hd := hasDerivAt_arccos_quotient hu hv
    (by positivity [h.R_pos, h.k_pos, h.m_pos])
    (by positivity [h.R_pos, h.q_pos]) h.Psi_gram
  have hs := h.s_pos.ne'
  have hm := h.m_pos.ne'
  have hR := h.R_pos.ne'
  have hk := h.k_pos.ne'
  have hq := h.q_pos.ne'
  have hx4 : 4 * R ^ 2 - x ≠ 0 := by linarith [h.m_radicand_pos]
  have hD1 : R ^ 2 * 4 - x ≠ 0 := by linarith [h.m_radicand_pos]
  have hD2 : -x + R ^ 2 * 4 ≠ 0 := by linarith [h.m_radicand_pos]
  convert hd using 1
  · rfl
  · field_simp
    ring_nf
    simp only [h.s_sq, h.m_sq]
    field_simp [hD1, hD2]
    ring

theorem hasDerivAt_phi : HasDerivAt (phi R)
    (2 * (6 * R ^ 2 - R ^ 2 * x - 2) / ((4 - x) * (4 * R ^ 2 - x) * q R x)) x := by
  have hu := ((hasDerivAt_id x).div_const 2).const_sub 1
  have hv := (h.hasDerivAt_r.const_mul 2).mul h.hasDerivAt_m
  have hd := (hasDerivAt_arccos_quotient hu hv
    (by dsimp; positivity [h.r_pos, h.m_pos]) h.q_pos h.phi_gram).const_mul 2
  have hr := h.r_pos.ne'
  have hm := h.m_pos.ne'
  have hq := h.q_pos.ne'
  have hx4 : 4 - x ≠ 0 := by linarith [h.2.2.1]
  have hD : 4 * R ^ 2 - x ≠ 0 := by linarith [h.m_radicand_pos]
  have hD1 : R ^ 2 * 4 - x ≠ 0 := by linarith [h.m_radicand_pos]
  have hD2 : -x + R ^ 2 * 4 ≠ 0 := by linarith [h.m_radicand_pos]
  convert hd using 1
  · rfl
  · dsimp only [id_eq, Pi.mul_apply]
    field_simp
    ring_nf
    simp only [h.r_sq, h.m_sq]
    field_simp [hD1, hD2]
    ring

theorem hasDerivAt_T : HasDerivAt (T R)
    ((4 * R ^ 2 - 1 - 2 * R ^ 2 * x) / (2 * s x * q R x)) x := by
  have hs := h.s_pos.ne'
  have hq := h.q_pos.ne'
  convert h.hasDerivAt_s.mul h.hasDerivAt_q using 1
  · rfl
  · field_simp
    ring_nf
    simp only [h.s_sq, h.q_sq]
    ring

theorem hasDerivAt_theta : HasDerivAt theta (1 / (4 * s x * r x)) x := by
  have hs := h.s_sq
  have hs0 := h.s_pos
  have hrt : Real.sqrt (1 - (s x / 2) ^ 2) = r x := by
    rw [div_pow, h.s_sq]
    norm_num [r]
  have hn : s x / 2 ≠ -1 := by intro hh; nlinarith
  have hp : s x / 2 ≠ 1 := by intro hh; nlinarith [h.2.2.1]
  have hd := (Real.hasDerivAt_arcsin hn hp).comp x (h.hasDerivAt_s.div_const 2)
  rw [hrt] at hd
  convert hd using 1
  · rfl
  · ring

theorem hasDerivAt_F : HasDerivAt F (-s x / 16 + theta x / (8 * r x)) x := by
  have hd := ((h.hasDerivAt_s.div_const 2).sub ((h.hasDerivAt_s.pow 3).div_const 24)).sub
    (h.hasDerivAt_r.mul h.hasDerivAt_theta)
  have hs := h.s_pos.ne'
  have hr := h.r_pos.ne'
  convert hd using 1
  · rfl
  · norm_num
    field_simp
    ring

end BlaschkeLebesgue.ClippedDifferential.Domain
