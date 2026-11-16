module

public import BlaschkeLebesgue.ContactCircle
public import Mathlib.Topology.Order.IntermediateValue

/-! # A continuous path inside a short spherical cap -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[expose] def capChord (e v : E) (t : ℝ) : E := (1 - t) • e + t • v
@[expose] def capPath (e v : E) (t : ℝ) : E := NormedSpace.normalize (capChord e v t)

theorem capChord_inner_gt {e v : E} {h t : ℝ} (he : ‖e‖ = 1) (hh : h < 1)
    (hv : h < ⟪v, e⟫_ℝ) (ht : t ∈ Set.Icc 0 1) : h < ⟪capChord e v t, e⟫_ℝ := by
  simp only [capChord, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
  by_cases ht1 : t = 1
  · simpa only [ht1, sub_self, zero_mul, one_mul, zero_add] using hv
  · have hp := mul_pos (show 0 < 1 - t by rcases ht with ⟨_, ht⟩; exact sub_pos.mpr (lt_of_le_of_ne ht ht1))
      (sub_pos.mpr hh)
    have hq := mul_nonneg ht.1 (sub_nonneg.mpr hv.le)
    nlinarith

theorem capChord_ne_zero {e v : E} {h t : ℝ} (he : ‖e‖ = 1) (hh0 : 0 ≤ h)
    (hh : h < 1) (hv : h < ⟪v, e⟫_ℝ) (ht : t ∈ Set.Icc 0 1) : capChord e v t ≠ 0 := by
  have hp := capChord_inner_gt he hh hv ht
  intro hz
  rw [hz, inner_zero_left] at hp
  linarith

theorem capChord_norm_le_one {e v : E} (he : ‖e‖ = 1) (hv : ‖v‖ = 1)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ‖capChord e v t‖ ≤ 1 := by
  calc
    _ ≤ ‖(1 - t) • e‖ + ‖t • v‖ := norm_add_le _ _
    _ = 1 := by
      rw [norm_smul, norm_smul, he, hv, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
      ring

theorem capPath_norm {e v : E} {h t : ℝ} (he : ‖e‖ = 1) (hh0 : 0 ≤ h)
    (hh : h < 1) (hv : h < ⟪v, e⟫_ℝ) (ht : t ∈ Set.Icc 0 1) : ‖capPath e v t‖ = 1 :=
  NormedSpace.norm_normalize (capChord_ne_zero he hh0 hh hv ht)

theorem capPath_inner_gt {e v : E} {h t : ℝ} (he : ‖e‖ = 1) (hv1 : ‖v‖ = 1)
    (hh0 : 0 ≤ h) (hh : h < 1) (hv : h < ⟪v, e⟫_ℝ) (ht : t ∈ Set.Icc 0 1) :
    h < ⟪capPath e v t, e⟫_ℝ := by
  have hp := capChord_inner_gt he hh hv ht
  have hn := norm_pos_iff.mpr (capChord_ne_zero he hh0 hh hv ht)
  have hb := capChord_norm_le_one he hv1 ht
  have hinner : ⟪capPath e v t, e⟫_ℝ = ⟪capChord e v t, e⟫_ℝ / ‖capChord e v t‖ := by
    simp only [capPath, NormedSpace.normalize, real_inner_smul_left, div_eq_mul_inv, mul_comm]
  rw [hinner]
  apply hp.trans_le
  apply (le_div_iff₀ hn).2
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ ⟪capChord e v t, e⟫_ℝ by linarith)
  simpa only [mul_one] using hm

theorem capPath_continuousOn {e v : E} {h : ℝ} (he : ‖e‖ = 1) (hh0 : 0 ≤ h)
    (hh : h < 1) (hv : h < ⟪v, e⟫_ℝ) : ContinuousOn (capPath e v) (Set.Icc 0 1) := by
  have hc : Continuous (capChord e v) := by unfold capChord; fun_prop
  exact (hc.norm.continuousOn.inv₀ (fun t ht ↦
    norm_ne_zero_iff.mpr (capChord_ne_zero he hh0 hh hv ht))).smul hc.continuousOn

theorem capPath_inner_gt_before_endpoint {e v : E} {h t : ℝ}
    (he : ‖e‖ = 1) (hv1 : ‖v‖ = 1) (hh0 : 0 ≤ h) (hh : h < 1)
    (hv : h ≤ ⟪v, e⟫_ℝ) (ht : t ∈ Set.Ico 0 1) : h < ⟪capPath e v t, e⟫_ℝ := by
  have hp : h < ⟪capChord e v t, e⟫_ℝ := by
    have hleft := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hh)
    have hright := mul_nonneg ht.1 (sub_nonneg.mpr hv)
    simp only [capChord, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
    nlinarith
  have hn : 0 < ‖capChord e v t‖ := by
    apply norm_pos_iff.mpr
    intro hz
    rw [hz, inner_zero_left] at hp
    linarith
  have hb := capChord_norm_le_one he hv1 ⟨ht.1, ht.2.le⟩
  have hinner : ⟪capPath e v t, e⟫_ℝ = ⟪capChord e v t, e⟫_ℝ / ‖capChord e v t‖ := by
    simp only [capPath, NormedSpace.normalize, real_inner_smul_left, div_eq_mul_inv, mul_comm]
  rw [hinner]
  apply hp.trans_le
  apply (le_div_iff₀ hn).2
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ ⟪capChord e v t, e⟫_ℝ by linarith)
  simpa only [mul_one] using hm

theorem capPath_zero {e v : E} (he : ‖e‖ = 1) : capPath e v 0 = e := by
  simp [capPath, capChord, NormedSpace.normalize_eq_self_of_norm_eq_one he]

theorem capPath_one {e v : E} (hv : ‖v‖ = 1) : capPath e v 1 = v := by
  simp [capPath, capChord, NormedSpace.normalize_eq_self_of_norm_eq_one hv]

theorem capPath_inner_zero {e v k : E} (he : ⟪k, e⟫_ℝ = 0) (hv : ⟪k, v⟫_ℝ = 0) (t : ℝ) :
    ⟪k, capPath e v t⟫_ℝ = 0 := by
  simp only [capPath, NormedSpace.normalize, capChord, real_inner_smul_right,
    inner_add_right, he, hv, mul_zero, add_zero]

end BlaschkeLebesgue
