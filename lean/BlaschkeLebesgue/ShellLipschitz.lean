module

public import BlaschkeLebesgue.ShellParametrization

/-!
# Lipschitz regularity of the shell parametrization

Normalization is Lipschitz on the annulus, as are the actual supporting points.
Bounded products then give Lipschitz regularity of the full shell map on its
compact domain.
-/

public noncomputable section

open Set NormedSpace
open scoped NNReal

namespace BlaschkeLebesgue

theorem lipschitzOn_smul_bounded {s : Set Space} {f : Space → ℝ} {g : Space → Space}
    {Cf Cg Bf Bg : ℝ≥0} (hf : LipschitzOnWith Cf f s) (hg : LipschitzOnWith Cg g s)
    (hBf : ∀ x ∈ s, ‖f x‖ ≤ Bf) (hBg : ∀ x ∈ s, ‖g x‖ ≤ Bg) :
    LipschitzOnWith (Bf * Cg + Cf * Bg) (fun x => f x • g x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hdf := hf.dist_le_mul x hx y hy
  have hdg := hg.dist_le_mul x hx y hy
  simp only [dist_eq_norm] at hdf hdg ⊢
  have he : f x • g x - f y • g y = f x • (g x - g y) + (f x - f y) • g y := by module
  calc
    ‖f x • g x - f y • g y‖ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
      rw [he]
      simpa only [norm_smul] using norm_add_le (f x • (g x - g y)) ((f x - f y) • g y)
    _ ≤ Bf * (Cg * ‖x - y‖) + (Cf * ‖x - y‖) * Bg := by
      exact add_le_add
        (mul_le_mul (hBf x hx) hdg (norm_nonneg _) Bf.coe_nonneg)
        (mul_le_mul hdf (hBg y hy) (norm_nonneg _) (by positivity))
    _ = ↑(Bf * Cg + Cf * Bg) * ‖x - y‖ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

theorem normalize_lipschitzOn_annulus : LipschitzOnWith 2 (normalize : Space → Space) unitAnnulus := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  have h := norm_mul_normalize_sub_le (x := x) (unitAnnulus_ne_zero hy)
  have hn := (mem_unitAnnulus_iff x).1 hx
  nlinarith only [h, mul_nonneg (sub_nonneg.2 hn.1) (norm_nonneg (normalize x - normalize y))]

theorem normalSupport_lipschitzOn_annulus {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) : LipschitzOnWith 2 (normalSupport K) unitAnnulus := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := supportPoint_norm_sub_le_of_ball_sum hKL
    (norm_normalize (unitAnnulus_ne_zero hx)) (norm_normalize (unitAnnulus_ne_zero hy))
  exact h.trans (normalize_lipschitzOn_annulus.dist_le_mul x hx y hy)

theorem normalSupport_normalize (K : ConvexBody Space) (x : Space) :
    normalSupport K (normalize x) = normalSupport K x := by
  simp only [normalSupport, normalize_normalize]

theorem exists_lipschitzOn_shellMap {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody) (ε δ : ℝ) :
    ∃ C, LipschitzOnWith C (shellMap D K ε δ) unitAnnulus := by
  obtain ⟨Rd, hRd, hDbound⟩ := D.isBounded.exists_pos_norm_le
  obtain ⟨Rk, hRk, hKbound⟩ := K.isBounded.exists_pos_norm_le
  let BD : ℝ≥0 := ⟨Rd, hRd.le⟩
  let BK : ℝ≥0 := ⟨Rk, hRk.le⟩
  let τ : Space → ℝ := fun x => ‖x‖ - 1
  have hτ : LipschitzWith 1 τ := by
    simpa only [add_zero] using
      (lipschitzWith_one_norm.sub (LipschitzWith.const (1 : ℝ)) :
        LipschitzWith (1 + 0) (fun x : Space => ‖x‖ - 1))
  have hleft : LipschitzWith 1 (fun x => 1 - τ x) := by
    simpa only [zero_add] using (LipschitzWith.const (1 : ℝ)).sub hτ
  have htimeBound (x : Space) (hx : x ∈ unitAnnulus) : ‖τ x‖ ≤ (1 : ℝ≥0) := by
    have ht := unitAnnulus_time hx
    change |‖x‖ - 1| ≤ 1
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hleftBound (x : Space) (hx : x ∈ unitAnnulus) : ‖1 - τ x‖ ≤ (1 : ℝ≥0) := by
    have ht := unitAnnulus_time hx
    change |1 - (‖x‖ - 1)| ≤ 1
    rw [abs_of_nonneg (sub_nonneg.2 ht.2)]
    linarith only [ht.1]
  have hdTerm := lipschitzOn_smul_bounded hleft.lipschitzOnWith (normalSupport_lipschitzOn_annulus hD)
    hleftBound (show ∀ x ∈ unitAnnulus, ‖normalSupport D x‖ ≤ BD from
      fun x _ => hDbound _ (normalSupport_mem D x))
  have hkTerm := lipschitzOn_smul_bounded hτ.lipschitzOnWith (normalSupport_lipschitzOn_annulus hK)
    htimeBound (show ∀ x ∈ unitAnnulus, ‖normalSupport K x‖ ≤ BK from
      fun x _ => hKbound _ (normalSupport_mem K x))
  have hradius : LipschitzWith ‖δ‖₊ (fun x => ε + τ x * δ) := by
    have h := (LipschitzWith.const ε).add ((lipschitzWith_smul δ).comp hτ)
    simpa only [zero_add, mul_one, smul_eq_mul, mul_comm, Function.comp_def] using h
  have hradiusBound (x : Space) (hx : x ∈ unitAnnulus) :
      ‖ε + τ x * δ‖ ≤ (‖ε‖₊ + ‖δ‖₊ : ℝ≥0) := by
    calc
      ‖ε + τ x * δ‖ ≤ ‖ε‖ + ‖τ x‖ * ‖δ‖ := by simpa only [norm_mul] using norm_add_le ε (τ x * δ)
      _ ≤ ‖ε‖ + 1 * ‖δ‖ := by gcongr; exact htimeBound x hx
      _ = ↑(‖ε‖₊ + ‖δ‖₊) := by simp
  have hrTerm := lipschitzOn_smul_bounded hradius.lipschitzOnWith normalize_lipschitzOn_annulus
    hradiusBound (show ∀ x ∈ unitAnnulus, ‖normalize x‖ ≤ (1 : ℝ≥0) from
      fun x hx => (norm_normalize (unitAnnulus_ne_zero hx)).le)
  refine ⟨(1 * 2 + 1 * BD) + (1 * 2 + 1 * BK) +
    ((‖ε‖₊ + ‖δ‖₊) * 2 + ‖δ‖₊ * 1), ?_⟩
  convert (hdTerm.add hkTerm).add hrTerm using 1
  funext x
  simp only [shellMap, shellPoint, normalSupport_normalize, τ]

end BlaschkeLebesgue
