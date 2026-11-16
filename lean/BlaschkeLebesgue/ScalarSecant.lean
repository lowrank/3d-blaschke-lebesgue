module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic

/-! # Scalar principles for the six-edge secant estimate -/

public noncomputable section

open Set

namespace BlaschkeLebesgue

theorem monotoneOn_of_derivatives_nonneg {D : Set ℝ} {f : ℝ → ℝ} (hD : Convex ℝ D)
    (hf : ∀ x ∈ D, ∃ d, HasDerivAt f d x ∧ 0 ≤ d) : MonotoneOn f D := by
  have hd : DifferentiableOn ℝ f D := fun x hx ↦ (hf x hx).choose_spec.1.differentiableAt.differentiableWithinAt
  apply monotoneOn_of_deriv_nonneg hD hd.continuousOn (hd.mono interior_subset)
  intro x hx
  obtain ⟨d, hder, hd⟩ := hf x (interior_subset hx)
  rwa [hder.deriv]

theorem antitoneOn_of_derivatives_nonpos {D : Set ℝ} {f : ℝ → ℝ} (hD : Convex ℝ D)
    (hf : ∀ x ∈ D, ∃ d, HasDerivAt f d x ∧ d ≤ 0) : AntitoneOn f D := by
  have hd : DifferentiableOn ℝ f D := fun x hx ↦ (hf x hx).choose_spec.1.differentiableAt.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos hD hd.continuousOn (hd.mono interior_subset)
  intro x hx
  obtain ⟨d, hder, hd⟩ := hf x (interior_subset hx)
  rwa [hder.deriv]

theorem concaveOn_of_slope_derivatives_nonpos {D : Set ℝ} {f g : ℝ → ℝ} (hD : Convex ℝ D)
    (hf : ∀ x ∈ D, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ D, ∃ d, HasDerivAt g d x ∧ d ≤ 0) : ConcaveOn ℝ D f := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hD
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
    (f' := g) (f'' := deriv g)
  · exact fun x hx ↦ (hf x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    obtain ⟨d, hd, _⟩ := hg x (interior_subset hx)
    rw [← hd.deriv] at hd
    exact hd.hasDerivWithinAt
  · intro x hx
    obtain ⟨d, hd, hle⟩ := hg x (interior_subset hx)
    rwa [hd.deriv]

theorem concave_secant_increment {f : ℝ → ℝ} {E e : ℝ} (hE : 0 < E)
    (he : 0 ≤ e) (heE : e ≤ E) (hf : ConcaveOn ℝ (Icc (1 - E) 1) f) :
    (f (1 - E) - f 1) / E * e ≤ f (1 - e) - f 1 := by
  have hw : 0 ≤ e / E := div_nonneg he hE.le
  have hw1 : e / E ≤ 1 := (div_le_one hE).2 heE
  have h := hf.2 (show 1 - E ∈ Icc (1 - E) 1 by constructor <;> linarith)
    (show (1 : ℝ) ∈ Icc (1 - E) 1 by constructor <;> linarith)
    hw (sub_nonneg.mpr hw1) (by ring : e / E + (1 - e / E) = 1)
  have hp : e / E * (1 - E) + (1 - e / E) * 1 = 1 - e := by field_simp; ring
  simp only [smul_eq_mul, hp] at h
  calc
    (f (1 - E) - f 1) / E * e = e / E * f (1 - E) + (1 - e / E) * f 1 - f 1 := by ring
    _ ≤ f (1 - e) - f 1 := sub_le_sub_right h _

theorem derivative_order_increment {f g f' g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (horder : ∀ x ∈ Icc a b, f' x ≤ g' x) :
    g a - g b ≤ f a - f b := by
  have hm : AntitoneOn (fun x ↦ f x - g x) (Icc a b) :=
    antitoneOn_of_derivatives_nonpos (convex_Icc a b) (by
      intro x hx
      exact ⟨f' x - g' x, (hf x hx).sub (hg x hx), sub_nonpos.mpr (horder x hx)⟩)
  have h := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  linarith

end BlaschkeLebesgue
