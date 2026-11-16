module

public import BlaschkeLebesgue.CompletionParameterVariation
public import BlaschkeLebesgue.Certificates.ParameterCover

/-! # From signed coordinate secants to a rigorous box acceptance test -/

@[expose] public noncomputable section

open Set

namespace BlaschkeLebesgue

def SecantBounds (f : ℝ → ℝ) (l r m M : ℝ) : Prop :=
  ∀ x ∈ Icc l r, ∀ y ∈ Icc l r, x ≤ y → m * (y - x) ≤ f y - f x ∧ f y - f x ≤ M * (y - x)

theorem SecantBounds.abs_affine_sub_le {f : ℝ → ℝ} {l r m M x y : ℝ}
    (h : SecantBounds f l r m M) (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) (c : ℝ) :
    |(f y - c * y) - (f x - c * x)| ≤ max |m - c| |M - c| * |y - x| := by
  have hordered {u v : ℝ} (hu : u ∈ Icc l r) (hv : v ∈ Icc l r) (huv : u ≤ v) :
      |(f v - c * v) - (f u - c * u)| ≤ max |m - c| |M - c| * |v - u| := by
    have hs := h u hu v hv huv
    have hm : -(max |m - c| |M - c|) ≤ m - c := by
      linarith [neg_le_abs (m - c), le_max_left |m - c| |M - c|]
    have hM : M - c ≤ max |m - c| |M - c| := (le_abs_self _).trans (le_max_right _ _)
    have hm' := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr huv)
    have hM' := mul_le_mul_of_nonneg_right hM (sub_nonneg.mpr huv)
    rw [abs_of_nonneg (sub_nonneg.mpr huv)]
    exact abs_le.2 ⟨by nlinarith only [hs.1, hm'], by nlinarith only [hs.2, hM']⟩
  rcases le_total x y with hxy | hyx
  · exact hordered hx hy hxy
  · rw [abs_sub_comm (f y - c * y) (f x - c * x), abs_sub_comm y x]
    exact hordered hy hx hyx

theorem box_affine_residual_bound {H : ℝ → ℝ → ℝ}
    {am bm ha hb mA MA mB MB ca cb a b : ℝ} (hha : 0 ≤ ha) (hhb : 0 ≤ hb)
    (hA : ∀ y ∈ Icc (bm - hb) (bm + hb), SecantBounds (fun x ↦ H x y) (am - ha) (am + ha) mA MA)
    (hB : ∀ x ∈ Icc (am - ha) (am + ha), SecantBounds (H x) (bm - hb) (bm + hb) mB MB)
    (hx : a ∈ Icc (am - ha) (am + ha)) (hy : b ∈ Icc (bm - hb) (bm + hb)) :
    |(H a b - ca * a - cb * b) - (H am bm - ca * am - cb * bm)| ≤
      ha * max |mA - ca| |MA - ca| + hb * max |mB - cb| |MB - cb| := by
  have ham : am ∈ Icc (am - ha) (am + ha) := ⟨by linarith, by linarith⟩
  have hbm : bm ∈ Icc (bm - hb) (bm + hb) := ⟨by linarith, by linarith⟩
  have hax : |a - am| ≤ ha := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hby : |b - bm| ≤ hb := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsa := (hA bm hbm).abs_affine_sub_le ham hx ca
  have hsb := (hB a hx).abs_affine_sub_le hbm hy cb
  have hma : 0 ≤ max |mA - ca| |MA - ca| := (abs_nonneg _).trans (le_max_left _ _)
  have hmb : 0 ≤ max |mB - cb| |MB - cb| := (abs_nonneg _).trans (le_max_left _ _)
  have hsa' := hsa.trans (mul_le_mul_of_nonneg_left hax hma)
  have hsb' := hsb.trans (mul_le_mul_of_nonneg_left hby hmb)
  have heq : (H a b - ca * a - cb * b) - (H am bm - ca * am - cb * bm) =
      ((H a b - cb * b) - (H a bm - cb * bm)) + ((H a bm - ca * a) - (H am bm - ca * am)) := by ring
  rw [heq]
  have htriangle := abs_add_le ((H a b - cb * b) - (H a bm - cb * bm))
    ((H a bm - ca * a) - (H am bm - ca * am))
  nlinarith only [htriangle, hsa', hsb']

theorem affine_lt_of_box_center_margin {H : ℝ → ℝ → ℝ}
    {am bm ha hb mA MA mB MB c0 ca cb value a b : ℝ} (hha : 0 ≤ ha) (hhb : 0 ≤ hb)
    (hA : ∀ y ∈ Icc (bm - hb) (bm + hb), SecantBounds (fun x ↦ H x y) (am - ha) (am + ha) mA MA)
    (hB : ∀ x ∈ Icc (am - ha) (am + ha), SecantBounds (H x) (bm - hb) (bm + hb) mB MB)
    (hcenter : value ≤ H am bm)
    (hmargin : 0 < value - (c0 + ca * am + cb * bm) -
      (ha * max |mA - ca| |MA - ca| + hb * max |mB - cb| |MB - cb|))
    (hx : a ∈ Icc (am - ha) (am + ha)) (hy : b ∈ Icc (bm - hb) (bm + hb)) :
    c0 + ca * a + cb * b < H a b := by
  have h := box_affine_residual_bound hha hhb hA hB hx hy (ca := ca) (cb := cb)
  have hlower := neg_le_abs ((H a b - ca * a - cb * b) - (H am bm - ca * am - cb * bm))
  linarith only [h, hlower, hcenter, hmargin]

end BlaschkeLebesgue
