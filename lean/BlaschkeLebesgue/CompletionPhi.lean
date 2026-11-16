module

public import BlaschkeLebesgue.CompletionPhiCalculus
public import BlaschkeLebesgue.ConvexTruncation

/-!
# The clamped completion integrand

On positive `W`, the denominator `sqrt W ^ 3` is `W^(3/2)`.
Both clamps are retained in the monotonicity and convexity statements.
-/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Completion

def phi (N z W : ℝ) : ℝ :=
  max (N / Real.sqrt W - 1) 0 * q (max (1 - z * Real.sqrt W) 0) / Real.sqrt W ^ 3

def phiCut (N z : ℝ) : ℝ := min (N ^ 2) ((1 / z) ^ 2)

theorem phi_eq_raw {N z W : ℝ} (hW : 0 < W)
    (hgap : Real.sqrt W ≤ N) (hdet : z * Real.sqrt W ≤ 1) : phi N z W = rawPhi N z W := by
  have hs := Real.sqrt_pos.2 hW
  have hg : 0 ≤ N / Real.sqrt W - 1 := by
    have h := (one_le_div hs).2 hgap
    linarith
  rw [phi, rawPhi, max_eq_left hg, max_eq_left (sub_nonneg.2 hdet)]

theorem phi_eq_zero_of_gap {N z W : ℝ} (hW : 0 < W) (hgap : N ≤ Real.sqrt W) :
    phi N z W = 0 := by
  have hg : N / Real.sqrt W - 1 ≤ 0 := by
    have h := (div_le_one (Real.sqrt_pos.2 hW)).2 hgap
    linarith
  simp only [phi, max_eq_right hg, zero_mul, zero_div]

theorem phi_eq_zero_of_det {N z W : ℝ} (hdet : 1 ≤ z * Real.sqrt W) : phi N z W = 0 := by
  rw [phi, max_eq_right (sub_nonpos.2 hdet), q]
  ring

theorem phi_det_range {z W : ℝ} (hv : 4 / 5 ≤ z * Real.sqrt W) :
    max (1 - z * Real.sqrt W) 0 ∈ Set.Icc 0 (1 / 5) :=
  ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩

theorem phi_nonneg {N z W : ℝ} (hv : 4 / 5 ≤ z * Real.sqrt W) : 0 ≤ phi N z W := by
  have hd := phi_det_range hv
  exact div_nonneg (mul_nonneg (le_max_right _ _) (q_nonneg hd.1 hd.2)) (by positivity)

theorem phi_antitoneOn {N z L : ℝ} (hN : 0 ≤ N) (hz : 0 ≤ z) (hL : 0 < L)
    (hv : 4 / 5 ≤ z * Real.sqrt L) : AntitoneOn (phi N z) (Set.Ici L) := by
  intro a ha b hb hab
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 (hL.trans_le ha)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 (hL.trans_le hb)
  have hs : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hva : 4 / 5 ≤ z * Real.sqrt a :=
    hv.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ha) hz)
  have hvb : 4 / 5 ≤ z * Real.sqrt b :=
    hv.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) hz)
  have hgap : max (N / Real.sqrt b - 1) 0 ≤ max (N / Real.sqrt a - 1) 0 := by
    apply max_le_max _ le_rfl
    exact sub_le_sub_right (div_le_div_of_nonneg_left hN hsa hs) 1
  have hdet : max (1 - z * Real.sqrt b) 0 ≤ max (1 - z * Real.sqrt a) 0 := by
    apply max_le_max _ le_rfl
    have h := mul_le_mul_of_nonneg_left hs hz
    linarith
  have hq := q_monotoneOn (phi_det_range hvb) (phi_det_range hva) hdet
  have hqa := q_nonneg (phi_det_range hva).1 (phi_det_range hva).2
  have hqb := q_nonneg (phi_det_range hvb).1 (phi_det_range hvb).2
  have hnum := mul_le_mul hgap hq hqb (le_max_right (N / Real.sqrt a - 1) 0)
  apply div_le_div₀ (mul_nonneg (le_max_right _ _) hqa) hnum (pow_pos hsa 3)
  exact pow_le_pow_left₀ hsa.le hs 3

theorem phiCut_pos {N z : ℝ} (hN : 0 < N) (hz : 0 < z) : 0 < phiCut N z :=
  lt_min (sq_pos_of_pos hN) (sq_pos_of_pos (one_div_pos.2 hz))

theorem phiCut_sqrt_bounds {N z W : ℝ} (hN : 0 < N) (hz : 0 < z)
    (hcut : W ≤ phiCut N z) : Real.sqrt W ≤ N ∧ z * Real.sqrt W ≤ 1 := by
  refine ⟨(Real.sqrt_le_left hN.le).2 (hcut.trans (min_le_left _ _)), ?_⟩
  have hs : Real.sqrt W ≤ 1 / z :=
    (Real.sqrt_le_left (one_div_pos.2 hz).le).2 (hcut.trans (min_le_right _ _))
  have h := mul_le_mul_of_nonneg_left hs hz.le
  simpa only [mul_one_div_cancel hz.ne'] using h

theorem phi_eq_raw_of_le_cut {N z W : ℝ} (hN : 0 < N) (hz : 0 < z) (hW : 0 < W)
    (hcut : W ≤ phiCut N z) : phi N z W = rawPhi N z W :=
  phi_eq_raw hW (phiCut_sqrt_bounds hN hz hcut).1 (phiCut_sqrt_bounds hN hz hcut).2

theorem phi_eq_zero_of_cut_le {N z W : ℝ} (hN : 0 < N) (hz : 0 < z) (hW : 0 < W)
    (hcut : phiCut N z ≤ W) : phi N z W = 0 := by
  rcases min_le_iff.1 hcut with hgap | hdet
  · apply phi_eq_zero_of_gap hW
    have h := Real.sqrt_le_sqrt hgap
    rwa [Real.sqrt_sq hN.le] at h
  · apply phi_eq_zero_of_det
    have hs := Real.sqrt_le_sqrt hdet
    rw [Real.sqrt_sq (one_div_pos.2 hz).le] at hs
    have h := mul_le_mul_of_nonneg_left hs hz.le
    simpa only [mul_one_div_cancel hz.ne'] using h

theorem rawPhi_convexOn {N z L : ℝ} (hN : 0 < N) (hz : 0 < z) (hL : 0 < L)
    (hv : 4 / 5 ≤ z * Real.sqrt L) : ConvexOn ℝ (Set.Icc L (phiCut N z)) (rawPhi N z) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := rawPhiDeriv N z) (f'' := rawPhiDeriv2 N z)
    (convex_Icc L (phiCut N z))
  · intro W hW
    exact (hasDerivAt_rawPhi N z (hL.trans_le hW.1)).continuousAt.continuousWithinAt
  · intro W hW
    exact (hasDerivAt_rawPhi N z (hL.trans_le (interior_subset hW).1)).hasDerivWithinAt
  · intro W hW
    exact (hasDerivAt_rawPhiDeriv N z (hL.trans_le (interior_subset hW).1)).hasDerivWithinAt
  · intro W hW
    have hm := interior_subset hW
    have hb := phiCut_sqrt_bounds hN hz hm.2
    exact rawPhiDeriv2_nonneg hN (hL.trans_le hm.1) hb.1
      ⟨hv.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm.1) hz.le), hb.2⟩

theorem rawPhi_antitoneOn {N z L : ℝ} (hN : 0 < N) (hz : 0 < z) (hL : 0 < L)
    (hv : 4 / 5 ≤ z * Real.sqrt L) : AntitoneOn (rawPhi N z) (Set.Icc L (phiCut N z)) := by
  intro a ha b hb hab
  rw [← phi_eq_raw_of_le_cut hN hz (hL.trans_le ha.1) ha.2,
    ← phi_eq_raw_of_le_cut hN hz (hL.trans_le hb.1) hb.2]
  exact phi_antitoneOn hN.le hz.le hL hv ha.1 hb.1 hab

theorem phi_eq_raw_truncate {N z L W : ℝ} (hN : 0 < N) (hz : 0 < z) (hL : 0 < L)
    (hcut : L ≤ phiCut N z) (hW : L ≤ W) :
    phi N z W = rawPhi N z (min W (phiCut N z)) := by
  by_cases h : W ≤ phiCut N z
  · rw [min_eq_left h]
    exact phi_eq_raw_of_le_cut hN hz (hL.trans_le hW) h
  · rw [min_eq_right (le_of_not_ge h), phi_eq_zero_of_cut_le hN hz (hL.trans_le hW) (le_of_not_ge h),
      ← phi_eq_raw_of_le_cut hN hz (hL.trans_le hcut) le_rfl,
      phi_eq_zero_of_cut_le hN hz (hL.trans_le hcut) le_rfl]

/-- Convexity holds through the cutoff: extending the decreasing convex branch
constantly at zero preserves convexity. -/
theorem phi_convexOn {N z L : ℝ} (hN : 0 < N) (hz : 0 < z) (hL : 0 < L)
    (hv : 4 / 5 ≤ z * Real.sqrt L) : ConvexOn ℝ (Set.Ici L) (phi N z) := by
  by_cases hcut : L ≤ phiCut N z
  · have h := convexOn_truncate_right hcut (rawPhi_convexOn hN hz hL hv) (rawPhi_antitoneOn hN hz hL hv)
    apply h.congr
    intro W hW
    exact (phi_eq_raw_truncate hN hz hL hcut hW).symm
  · apply (convexOn_const (0 : ℝ) (convex_Ici L)).congr
    intro W hW
    exact (phi_eq_zero_of_cut_le hN hz (hL.trans_le hW) ((le_of_not_ge hcut).trans hW)).symm

end BlaschkeLebesgue.Completion
