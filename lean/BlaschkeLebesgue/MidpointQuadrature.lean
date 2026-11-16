module

public import BlaschkeLebesgue.CompletionFixedSquare

/-!
# A proved midpoint quadrature error bound

A lower bound on the second derivative gives the exact midpoint correction
`M * h^2 / 6` on a cell of half-width `h`. This is the one-dimensional input
to the certificate's two-coordinate quadrature rule.
-/

public noncomputable section

open MeasureTheory Set

namespace BlaschkeLebesgue

theorem quadratic_tangent_lower {f f' f'' : ℝ → ℝ} {a b m x M : ℝ}
    (hf : ∀ y ∈ Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc a b, HasDerivAt f' (f'' y) y)
    (hM : ∀ y ∈ Icc a b, -M ≤ f'' y) (hm : m ∈ Icc a b) (hx : x ∈ Icc a b) :
    f m + f' m * (x - m) - M / 2 * (x - m) ^ 2 ≤ f x := by
  let G : ℝ → ℝ := fun y ↦ f y + M / 2 * (y - m) ^ 2
  have hG : ∀ y ∈ Icc a b, HasDerivAt G (f' y + M * (y - m)) y := by
    intro y hy
    convert (hf y hy).add ((((hasDerivAt_id y).sub_const m).pow 2).const_mul (M / 2)) using 1
    · funext z
      simp only [G, Pi.add_apply, Pi.pow_apply, id_eq]
    · norm_num [id_eq]
      ring
  have hG' : ∀ y ∈ Icc a b,
      HasDerivAt (fun z ↦ f' z + M * (z - m)) (f'' y + M) y := by
    intro y hy
    convert (hf' y hy).add (((hasDerivAt_id y).sub_const m).const_mul M) using 1
    · funext z
      simp only [Pi.add_apply, id_eq]
    · norm_num
  have hc : ConvexOn ℝ (Icc a b) G := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
      (fun y hy ↦ (hG y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hG y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy ↦ (hG' y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    linarith [hM y (interior_subset hy)]
  have hGm : HasDerivAt G (f' m) m := by simpa only [sub_self, mul_zero, add_zero] using hG m hm
  rcases lt_trichotomy m x with hmx | rfl | hxm
  · have h := hc.le_slope_of_hasDerivAt hm hx hmx hGm
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.2 hmx)).1 h
    dsimp only [G] at hh
    nlinarith only [hh]
  · simp
  · have h := hc.slope_le_of_hasDerivAt hx hm hxm hGm
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.2 hxm)).1 h
    dsimp only [G] at hh
    nlinarith only [hh]

theorem integral_midpoint_quadratic (m h A B M : ℝ) :
    (∫ x in (m - h)..(m + h), A + B * (x - m) - M / 2 * (x - m) ^ 2) =
      2 * h * (A - M * h ^ 2 / 6) := by
  let P : ℝ → ℝ := fun x ↦ A * x + B * (x - m) ^ 2 / 2 - M * (x - m) ^ 3 / 6
  have hd (x : ℝ) : HasDerivAt P (A + B * (x - m) - M / 2 * (x - m) ^ 2) x := by
    have h1 := (hasDerivAt_id x).const_mul A
    have h2 := ((((hasDerivAt_id x).sub_const m).pow 2).const_mul B).div_const 2
    have h3 := ((((hasDerivAt_id x).sub_const m).pow 3).const_mul M).div_const 6
    convert (h1.add h2).sub h3 using 1
    · funext z
      simp only [P, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
    · norm_num [id_eq]
      ring
  have hi : IntervalIntegrable (fun x ↦ A + B * (x - m) - M / 2 * (x - m) ^ 2) volume (m - h) (m + h) :=
    (show Continuous (fun x : ℝ ↦ A + B * (x - m) - M / 2 * (x - m) ^ 2) by fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x) hi]
  dsimp only [P]
  ring

theorem midpoint_quadrature_lower {f f' f'' : ℝ → ℝ} {m h M : ℝ} (hh : 0 ≤ h)
    (hf : ∀ x ∈ Icc (m - h) (m + h), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (m - h) (m + h), HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc (m - h) (m + h), -M ≤ f'' x) :
    2 * h * (f m - M * h ^ 2 / 6) ≤ ∫ x in (m - h)..(m + h), f x := by
  have hab : m - h ≤ m + h := by linarith
  have hm : m ∈ Icc (m - h) (m + h) := ⟨by linarith, by linarith⟩
  have hc : ContinuousOn f (Icc (m - h) (m + h)) :=
    fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable f volume (m - h) (m + h) := hc.intervalIntegrable_of_Icc hab
  have hp : IntervalIntegrable (fun x ↦ f m + f' m * (x - m) - M / 2 * (x - m) ^ 2)
      volume (m - h) (m + h) :=
    (show Continuous (fun x : ℝ ↦ f m + f' m * (x - m) - M / 2 * (x - m) ^ 2) by fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hab hp hi
    (fun x hx ↦ quadratic_tangent_lower hf hf' hM hm hx)
  rwa [integral_midpoint_quadratic] at h

end BlaschkeLebesgue
