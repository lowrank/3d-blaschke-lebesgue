module

public import BlaschkeLebesgue.CompletionAlgebra
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # The exact second derivative of the unclamped completion integrand -/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.Completion

def rawPhi (N z W : ℝ) : ℝ := (N / Real.sqrt W - 1) * q (1 - z * Real.sqrt W) / Real.sqrt W ^ 3

def rawPhiDeriv (N z W : ℝ) : ℝ :=
  17 * N / (16 * Real.sqrt W ^ 6) - (51 + 243 * N * z) / (64 * Real.sqrt W ^ 5) +
    (64 * N * z ^ 2 + 81 * z) / (32 * Real.sqrt W ^ 4) - z ^ 2 / Real.sqrt W ^ 3

def rawPhiDeriv2 (N z W : ℝ) : ℝ :=
  (-408 * N + 15 * (17 + 81 * N * z) * Real.sqrt W -
    8 * (64 * N * z ^ 2 + 81 * z) * Real.sqrt W ^ 2 + 192 * z ^ 2 * Real.sqrt W ^ 3) /
      (128 * Real.sqrt W ^ 8)

theorem hasDerivAt_rawPhi (N z : ℝ) {W : ℝ} (hW : 0 < W) :
    HasDerivAt (rawPhi N z) (rawPhiDeriv N z W) W := by
  have hs := Real.hasDerivAt_sqrt hW.ne'
  have hs0 := (Real.sqrt_pos.2 hW).ne'
  have hg := ((hasDerivAt_const W N).div hs hs0).sub_const 1
  have hd := (hasDerivAt_const W 1).sub (hs.const_mul z)
  have hq := (hd.const_mul (47 / 32)).sub ((hd.pow 2).const_mul 2)
  have h := (hg.mul hq).div (hs.pow 3) (pow_ne_zero 3 hs0)
  convert h using 1
  · rfl
  · unfold rawPhiDeriv
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    field_simp
    ring

theorem hasDerivAt_rawPhiDeriv (N z : ℝ) {W : ℝ} (hW : 0 < W) :
    HasDerivAt (rawPhiDeriv N z) (rawPhiDeriv2 N z W) W := by
  have hs := Real.hasDerivAt_sqrt hW.ne'
  have hs0 := (Real.sqrt_pos.2 hW).ne'
  have h1 := (hasDerivAt_const W (17 * N)).div ((hs.pow 6).const_mul 16)
    (by simpa only [Pi.pow_apply] using mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) (pow_ne_zero 6 hs0))
  have h2 := (hasDerivAt_const W (51 + 243 * N * z)).div ((hs.pow 5).const_mul 64)
    (by simpa only [Pi.pow_apply] using mul_ne_zero (by norm_num : (64 : ℝ) ≠ 0) (pow_ne_zero 5 hs0))
  have h3 := (hasDerivAt_const W (64 * N * z ^ 2 + 81 * z)).div ((hs.pow 4).const_mul 32)
    (by simpa only [Pi.pow_apply] using mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) (pow_ne_zero 4 hs0))
  have h4 := (hasDerivAt_const W (z ^ 2)).div (hs.pow 3) (pow_ne_zero 3 hs0)
  convert ((h1.sub h2).add h3).sub h4 using 1
  · rfl
  · unfold rawPhiDeriv2
    simp only [Pi.pow_apply]
    field_simp
    ring

theorem rawPhiDeriv2_eq (N z : ℝ) {W : ℝ} (hN : N ≠ 0) (hW : 0 < W) :
    rawPhiDeriv2 N z W = N / Real.sqrt W ^ 8 *
      (47 / 32 * B₁ (Real.sqrt W / N) (z * Real.sqrt W) -
        2 * B₂ (Real.sqrt W / N) (z * Real.sqrt W)) := by
  have hs0 := (Real.sqrt_pos.2 hW).ne'
  unfold rawPhiDeriv2 B₁ B₂
  field_simp
  ring

theorem rawPhiDeriv2_nonneg {N z W : ℝ} (hN : 0 < N) (hW : 0 < W)
    (hgap : Real.sqrt W ≤ N) (hv : z * Real.sqrt W ∈ Set.Icc (4 / 5) 1) :
    0 ≤ rawPhiDeriv2 N z W := by
  have hu : Real.sqrt W / N ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (Real.sqrt_nonneg _) hN.le, (div_le_one hN).2 hgap⟩
  have hB := half_le_B₁ hu ⟨by linarith [hv.1], hv.2⟩
  have hrem := convexity_remainder hu hv
  rw [rawPhiDeriv2_eq N z hN.ne' hW]
  apply mul_nonneg (div_nonneg hN.le (by positivity))
  nlinarith only [hB, hrem]

end BlaschkeLebesgue.Completion
