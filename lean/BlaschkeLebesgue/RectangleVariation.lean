module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # A centered lower bound from the two coordinate derivatives -/

public noncomputable section

open Set

namespace BlaschkeLebesgue

theorem rectangle_center_lower {H Hs Ht : ℝ → ℝ → ℝ} {ms mt h Ms Mt s t : ℝ}
    (hh : 0 ≤ h)
    (hS : ∀ x ∈ Icc (ms - h) (ms + h), ∀ y ∈ Icc (mt - h) (mt + h),
      HasDerivAt (fun z ↦ H z y) (Hs x y) x)
    (hT : ∀ x ∈ Icc (ms - h) (ms + h), ∀ y ∈ Icc (mt - h) (mt + h),
      HasDerivAt (H x) (Ht x y) y)
    (hMs : ∀ x ∈ Icc (ms - h) (ms + h), ∀ y ∈ Icc (mt - h) (mt + h), |Hs x y| ≤ Ms)
    (hMt : ∀ x ∈ Icc (ms - h) (ms + h), ∀ y ∈ Icc (mt - h) (mt + h), |Ht x y| ≤ Mt)
    (hs : s ∈ Icc (ms - h) (ms + h)) (ht : t ∈ Icc (mt - h) (mt + h)) :
    H ms mt - (Ms + Mt) * h ≤ H s t := by
  have hms : ms ∈ Icc (ms - h) (ms + h) := ⟨by linarith, by linarith⟩
  have hmt : mt ∈ Icc (mt - h) (mt + h) := ⟨by linarith, by linarith⟩
  have hMs0 : 0 ≤ Ms := (abs_nonneg _).trans (hMs ms hms mt hmt)
  have hMt0 : 0 ≤ Mt := (abs_nonneg _).trans (hMt ms hms mt hmt)
  have hdx : |H s t - H ms t| ≤ Ms * |s - ms| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx ↦ (hS x hx t ht).hasDerivWithinAt)
        (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hMs x hx t ht)
        (convex_Icc (ms - h) (ms + h)) hms hs
  have hdy : |H ms t - H ms mt| ≤ Mt * |t - mt| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y hy ↦ (hT ms hms y hy).hasDerivWithinAt)
        (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hMt ms hms y hy)
        (convex_Icc (mt - h) (mt + h)) hmt ht
  have hxs : |s - ms| ≤ h := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hyt : |t - mt| ≤ h := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h1 := (abs_le.1 hdx).1
  have h2 := (abs_le.1 hdy).1
  have h3 := mul_le_mul_of_nonneg_left hxs hMs0
  have h4 := mul_le_mul_of_nonneg_left hyt hMt0
  nlinarith only [h1, h2, h3, h4]

end BlaschkeLebesgue
