module

public import BlaschkeLebesgue.ClippedAngleDerivatives
public import BlaschkeLebesgue.ClippedDifferentialFormula

/-! # Cancellation-resistant derivatives of the actual clipped-volume edge terms -/

public noncomputable section

open Filter
open scoped Topology

namespace BlaschkeLebesgue.ClippedDifferential.Domain

variable {R x : ℝ} (h : Domain R x)
include h

theorem hasDerivAt_outer : HasDerivAt (outer R) (outerDx R x) x := by
  have hcoef := ((h.hasDerivAt_s.const_mul (-3)).div_const 2).add
    ((h.hasDerivAt_s.pow 3).div_const 8)
  have hd := (((((h.hasDerivAt_U.const_mul (-4)).sub
    (h.hasDerivAt_V.const_mul (2 * R ^ 3))).add (hcoef.mul h.hasDerivAt_phi)).add
    (h.hasDerivAt_T.div_const 2)).add
    (h.hasDerivAt_Psi.const_mul (4 * R ^ 3 + 3 / (2 * R)))).div_const 3
  have hs := h.s_pos.ne'
  have hq := h.q_pos.ne'
  have hR := h.R_pos.ne'
  have hx4 : 4 - x ≠ 0 := by linarith [h.2.2.1]
  have hD : 4 * R ^ 2 - x ≠ 0 := by linarith [h.m_radicand_pos]
  have hD1 : R ^ 2 * 4 - x ≠ 0 := by linarith [h.m_radicand_pos]
  have hD2 : -x + R ^ 2 * 4 ≠ 0 := by linarith [h.m_radicand_pos]
  have hs4 : s x ^ 4 = x ^ 2 := by
    calc s x ^ 4 = (s x ^ 2) ^ 2 := by ring
         _ = x ^ 2 := by rw [h.s_sq]
  convert hd using 1
  · rfl
  · unfold outerDx
    simp only [Pi.pow_apply, Pi.add_apply]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp
    ring_nf
    simp only [h.s_sq, h.q_sq, hs4]
    field_simp [hD1, hD2]
    ring

theorem hasDerivAt_inner : HasDerivAt (inner R) (innerDx R x) x := by
  have hd := (((((h.hasDerivAt_U.const_mul (4 / 3)).sub
    (h.hasDerivAt_V.const_mul (2 * ClippedFormula.z R))).add
    (h.hasDerivAt_phi.mul h.hasDerivAt_F)).sub (h.hasDerivAt_T.div_const 6)).sub
    (h.hasDerivAt_Psi.const_mul (4 * ClippedFormula.b R)))
  have hs := h.s_pos.ne'
  have hr := h.r_pos.ne'
  have hq := h.q_pos.ne'
  have hR := h.R_pos.ne'
  have hx4 : 4 - x ≠ 0 := by linarith [h.2.2.1]
  have hD : 4 * R ^ 2 - x ≠ 0 := by linarith [h.m_radicand_pos]
  have hD1 : R ^ 2 * 4 - x ≠ 0 := by linarith [h.m_radicand_pos]
  have hD2 : -x + R ^ 2 * 4 ≠ 0 := by linarith [h.m_radicand_pos]
  have hs4 : s x ^ 4 = x ^ 2 := by
    calc s x ^ 4 = (s x ^ 2) ^ 2 := by ring
         _ = x ^ 2 := by rw [h.s_sq]
  convert hd using 1
  · rfl
  · unfold innerDx F ClippedFormula.b ClippedFormula.z k
    field_simp
    ring_nf
    simp only [h.s_sq, h.r_sq, h.q_sq, hs4]
    field_simp [hD1, hD2]
    ring

theorem hasDerivAt_outerEdge :
    HasDerivAt (fun z ↦ ClippedFormula.outerEdge R (1 - z)) (outerDx R x) x := by
  apply h.hasDerivAt_outer.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds h.2.1] with z hz
  exact (outer_eq_manuscript h.1 hz.le).symm

theorem hasDerivAt_innerEdge :
    HasDerivAt (fun z ↦ ClippedFormula.innerEdge R (1 - z)) (innerDx R x) x := by
  apply h.hasDerivAt_inner.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds h.2.1] with z hz
  exact (inner_eq_manuscript h.1 hz.le).symm

theorem hasDerivAt_combinedEdge :
    HasDerivAt (fun z ↦ ClippedFormula.combinedEdge R (1 - z)) (combinedDx R x) x := by
  exact ((h.hasDerivAt_innerEdge.const_mul 47).sub h.hasDerivAt_outerEdge).div_const 46

end BlaschkeLebesgue.ClippedDifferential.Domain
