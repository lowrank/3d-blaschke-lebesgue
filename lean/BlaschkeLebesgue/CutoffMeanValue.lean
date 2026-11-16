module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith

/-!
# Mean value bounds through zero cutoffs

A continuous function may fail to be differentiable where it is zero.
Derivative bounds away from those points still bound every secant, provided
the derivative interval includes zero. This supplies the analytic justification
for the verifier's `hullzero` operation without assuming differentiability at
the activation boundary or that the boundary has finitely many points.
-/

public noncomputable section

open Set
open scoped Topology

namespace BlaschkeLebesgue

theorem image_sub_le_mul_sub_of_hasDerivAt {f f' : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hbnd : ∀ x ∈ Ioo a b, f' x ≤ C) :
    f b - f a ≤ C * (b - a) := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · obtain ⟨x, hx, hdx⟩ := exists_hasDerivAt_eq_slope f f' hab hf hd
    have h := hbnd x hx
    rw [hdx, div_le_iff₀ (sub_pos.2 hab)] at h
    exact h
  · simp

theorem image_sub_bounds_of_hasDerivAt {f f' : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hbnd : ∀ x ∈ Ioo a b, m ≤ f' x ∧ f' x ≤ M) :
    m * (b - a) ≤ f b - f a ∧ f b - f a ≤ M * (b - a) := by
  refine ⟨?_, image_sub_le_mul_sub_of_hasDerivAt hab hf hd (fun x hx ↦ (hbnd x hx).2)⟩
  have h := image_sub_le_mul_sub_of_hasDerivAt hab hf.neg (fun x hx ↦ (hd x hx).neg)
    (fun x hx ↦ neg_le_neg (hbnd x hx).1)
  simp only [Pi.neg_apply] at h
  linarith only [h]

/-- Differentiability is required only where the function is nonzero. -/
theorem image_sub_le_mul_sub_of_hasDerivAt_off_zero {f f' : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, f x ≠ 0 → HasDerivAt f (f' x) x)
    (hbnd : ∀ x ∈ Ioo a b, f x ≠ 0 → f' x ≤ C) :
    f b - f a ≤ C * (b - a) := by
  let Z := Icc a b ∩ f ⁻¹' {0}
  by_cases hZ : Z.Nonempty
  · have hclosed : IsClosed Z := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hcompact : IsCompact Z := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
    obtain ⟨u, hu⟩ := hcompact.exists_isLeast hZ
    obtain ⟨v, hv⟩ := hcompact.exists_isGreatest hZ
    have huab : u ∈ Icc a b := hu.1.1
    have hvab : v ∈ Icc a b := hv.1.1
    have hfu : f u = 0 := hu.1.2
    have hfv : f v = 0 := hv.1.2
    have huv : u ≤ v := hu.2 hv.1
    have hleftnz (x : ℝ) (hx : x ∈ Ioo a u) : f x ≠ 0 := by
      intro hx0
      have hxZ : x ∈ Z := ⟨⟨hx.1.le, hx.2.le.trans huab.2⟩, hx0⟩
      exact (not_le_of_gt hx.2) (hu.2 hxZ)
    have hrightnz (x : ℝ) (hx : x ∈ Ioo v b) : f x ≠ 0 := by
      intro hx0
      have hxZ : x ∈ Z := ⟨⟨hvab.1.trans hx.1.le, hx.2.le⟩, hx0⟩
      exact (not_le_of_gt hx.1) (hv.2 hxZ)
    have hleft := image_sub_le_mul_sub_of_hasDerivAt huab.1
      (hf.mono (Icc_subset_Icc le_rfl huab.2))
      (fun x hx ↦ hd x ⟨hx.1, hx.2.trans_le huab.2⟩ (hleftnz x hx))
      (fun x hx ↦ hbnd x ⟨hx.1, hx.2.trans_le huab.2⟩ (hleftnz x hx))
    have hright := image_sub_le_mul_sub_of_hasDerivAt hvab.2
      (hf.mono (Icc_subset_Icc hvab.1 le_rfl))
      (fun x hx ↦ hd x ⟨hvab.1.trans_lt hx.1, hx.2⟩ (hrightnz x hx))
      (fun x hx ↦ hbnd x ⟨hvab.1.trans_lt hx.1, hx.2⟩ (hrightnz x hx))
    rw [hfu] at hleft
    rw [hfv] at hright
    nlinarith [mul_nonneg hC (sub_nonneg.mpr huv)]
  · have hnz (x : ℝ) (hx : x ∈ Ioo a b) : f x ≠ 0 := by
      intro hx0
      exact hZ ⟨x, ⟨⟨hx.1.le, hx.2.le⟩, hx0⟩⟩
    exact image_sub_le_mul_sub_of_hasDerivAt hab hf
      (fun x hx ↦ hd x hx (hnz x hx)) (fun x hx ↦ hbnd x hx (hnz x hx))

theorem image_sub_bounds_of_hasDerivAt_off_zero {f f' : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hm : m ≤ 0) (hM : 0 ≤ M) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, f x ≠ 0 → HasDerivAt f (f' x) x)
    (hbnd : ∀ x ∈ Ioo a b, f x ≠ 0 → m ≤ f' x ∧ f' x ≤ M) :
    m * (b - a) ≤ f b - f a ∧ f b - f a ≤ M * (b - a) := by
  refine ⟨?_, image_sub_le_mul_sub_of_hasDerivAt_off_zero hab hM hf hd (fun x hx hn ↦ (hbnd x hx hn).2)⟩
  have hnz (x : ℝ) (h : -f x ≠ 0) : f x ≠ 0 := by simpa only [neg_ne_zero] using h
  have h := image_sub_le_mul_sub_of_hasDerivAt_off_zero hab (neg_nonneg.mpr hm) hf.neg
    (fun x hx hn ↦ (hd x hx (hnz x hn)).neg)
    (fun x hx hn ↦ neg_le_neg (hbnd x hx (hnz x hn)).1)
  simp only [Pi.neg_apply] at h
  linarith only [h]

theorem hasDerivAt_cutoff_of_pos {f P P' G D : ℝ → ℝ} {a b x : ℝ}
    (hG : ContinuousOn G (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (heq : ∀ z ∈ Icc a b, 0 < G z → 0 < D z → f z = P z)
    (hd : HasDerivAt P (P' x) x) (hx : x ∈ Ioo a b) (hGx : 0 < G x) (hDx : 0 < D x) :
    HasDerivAt f (P' x) x := by
  have hGn : ∀ᶠ z in 𝓝 x, 0 < G z :=
    (hG.continuousAt (Icc_mem_nhds hx.1 hx.2)).eventually (eventually_gt_nhds hGx)
  have hDn : ∀ᶠ z in 𝓝 x, 0 < D z :=
    (hD.continuousAt (Icc_mem_nhds hx.1 hx.2)).eventually (eventually_gt_nhds hDx)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hGn, hDn, Icc_mem_nhds hx.1 hx.2] with z hzG hzD hz
  exact heq z hz hzG hzD

/-- The true density agrees locally with the smooth expression at every
nonzero point, because both activation factors are then strictly positive. -/
theorem hasDerivAt_cutoff_of_ne_zero {f P P' G D : ℝ → ℝ} {a b x : ℝ}
    (hG : ContinuousOn G (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hzero : ∀ z ∈ Icc a b, G z ≤ 0 ∨ D z ≤ 0 → f z = 0)
    (heq : ∀ z ∈ Icc a b, 0 < G z → 0 < D z → f z = P z)
    (hd : HasDerivAt P (P' x) x) (hx : x ∈ Ioo a b) (hnz : f x ≠ 0) :
    HasDerivAt f (P' x) x := by
  have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
  have hGx : 0 < G x := by
    by_contra h
    exact hnz (hzero x hx' (Or.inl (le_of_not_gt h)))
  have hDx : 0 < D x := by
    by_contra h
    exact hnz (hzero x hx' (Or.inr (le_of_not_gt h)))
  exact hasDerivAt_cutoff_of_pos hG hD heq hd hx hGx hDx

theorem image_sub_bounds_of_cutoff_positive {f P P' G D : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hG : ContinuousOn G (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (heq : ∀ z ∈ Icc a b, 0 < G z → 0 < D z → f z = P z)
    (hd : ∀ z ∈ Ioo a b, HasDerivAt P (P' z) z)
    (hpos : ∀ z ∈ Ioo a b, 0 < G z ∧ 0 < D z)
    (hbnd : ∀ z ∈ Ioo a b, m ≤ P' z ∧ P' z ≤ M) :
    m * (b - a) ≤ f b - f a ∧ f b - f a ≤ M * (b - a) :=
  image_sub_bounds_of_hasDerivAt hab hf
    (fun z hz ↦ hasDerivAt_cutoff_of_pos hG hD heq (hd z hz) hz (hpos z hz).1 (hpos z hz).2) hbnd

theorem image_sub_bounds_of_cutoff {f P P' G D : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hm : m ≤ 0) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc a b)) (hG : ContinuousOn G (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hzero : ∀ z ∈ Icc a b, G z ≤ 0 ∨ D z ≤ 0 → f z = 0)
    (heq : ∀ z ∈ Icc a b, 0 < G z → 0 < D z → f z = P z)
    (hd : ∀ z ∈ Ioo a b, HasDerivAt P (P' z) z)
    (hbnd : ∀ z ∈ Ioo a b, 0 < G z → 0 < D z → m ≤ P' z ∧ P' z ≤ M) :
    m * (b - a) ≤ f b - f a ∧ f b - f a ≤ M * (b - a) := by
  apply image_sub_bounds_of_hasDerivAt_off_zero hab hm hM hf
  · intro z hz hnz
    exact hasDerivAt_cutoff_of_ne_zero hG hD hzero heq (hd z hz) hz hnz
  · intro z hz hnz
    have hz' : z ∈ Icc a b := ⟨hz.1.le, hz.2.le⟩
    have hGz : 0 < G z := by
      by_contra h
      exact hnz (hzero z hz' (Or.inl (le_of_not_gt h)))
    have hDz : 0 < D z := by
      by_contra h
      exact hnz (hzero z hz' (Or.inr (le_of_not_gt h)))
    exact hbnd z hz hGz hDz

/-- The interval hull of zero and a smooth derivative enclosure bounds all
secants of the clamped function, including cells crossing either cutoff. -/
theorem image_sub_bounds_of_cutoff_hullzero {f P P' G D : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hG : ContinuousOn G (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hzero : ∀ z ∈ Icc a b, G z ≤ 0 ∨ D z ≤ 0 → f z = 0)
    (heq : ∀ z ∈ Icc a b, 0 < G z → 0 < D z → f z = P z)
    (hd : ∀ z ∈ Ioo a b, HasDerivAt P (P' z) z)
    (hbnd : ∀ z ∈ Ioo a b, 0 < G z → 0 < D z → m ≤ P' z ∧ P' z ≤ M) :
    min 0 m * (b - a) ≤ f b - f a ∧ f b - f a ≤ max 0 M * (b - a) :=
  image_sub_bounds_of_cutoff hab (min_le_left _ _) (le_max_left _ _) hf hG hD hzero heq hd
    (fun z hz hgz hdz ↦ ⟨(min_le_right _ _).trans (hbnd z hz hgz hdz).1,
      (hbnd z hz hgz hdz).2.trans (le_max_right _ _)⟩)

end BlaschkeLebesgue
