module

public import BlaschkeLebesgue.CapArea
public import BlaschkeLebesgue.RadialAnalysis

/-!
# Integrating disjoint cap annuli

Exact spherical annulus measures and finite integration of pointwise lower
bounds, using the same sphere measure as the radial volume formula.
-/

public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BlaschkeLebesgue

theorem sphereCap_antitone (u : Space) : Antitone (sphereCap u) :=
  fun _ _ hab _ hx ↦ hab.trans hx

/-- The annulus between two parallel cap boundaries, excluding its inner cap. -/
@[expose] def sphereAnnulus (u : Space) (outer inner : ℝ) : Set UnitSphere :=
  sphereCap u outer \ sphereCap u inner

theorem measurableSet_sphereAnnulus (u : Space) (outer inner : ℝ) :
    MeasurableSet (sphereAnnulus u outer inner) :=
  (measurableSet_sphereCap u outer).diff (measurableSet_sphereCap u inner)

theorem sphereMeasure_real_annulus {u : Space} (hu : ‖u‖ = 1) {outer inner : ℝ}
    (ho : 0 < outer) (hoi : outer ≤ inner) (hi : inner ≤ 1) :
    sphereMeasure.real (sphereAnnulus u outer inner) = 2 * Real.pi * (inner - outer) := by
  rw [sphereAnnulus, measureReal_sdiff (sphereCap_antitone u hoi)
    (measurableSet_sphereCap u inner),
    sphereMeasure_real_cap hu ho (hoi.trans hi),
    sphereMeasure_real_cap hu (ho.trans_le hoi) hi]
  ring

/-- Nonoverlapping measurable pieces contribute their full lower bounds to the integral. -/
theorem sum_piece_bounds_le_integral {ι : Type*} [Fintype ι]
    {f : UnitSphere → ℝ} (hf : Integrable f sphereMeasure) (hn : ∀ x, 0 ≤ f x)
    (s : ι → Set UnitSphere) (a : ι → ℝ) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j ↦ Disjoint (s i) (s j)))
    (ha : ∀ i x, x ∈ s i → a i ≤ f x) :
    ∑ i, sphereMeasure.real (s i) * a i ≤ ∫ x, f x ∂sphereMeasure := by
  classical
  let g : ι → UnitSphere → ℝ := fun i ↦ (s i).indicator (fun _ ↦ a i)
  have hg (i : ι) : Integrable (g i) sphereMeasure :=
    (integrable_const (a i)).indicator (hs i)
  have hgint : Integrable (fun x ↦ ∑ i, g i x) sphereMeasure :=
    integrable_finsetSum _ (fun i _ ↦ hg i)
  have hpoint (x : UnitSphere) : ∑ i, g i x ≤ f x := by
    by_cases hx : ∃ i, x ∈ s i
    · obtain ⟨i, hi⟩ := hx
      rw [Finset.sum_eq_single i]
      · simpa only [g, indicator_of_mem hi] using ha i x hi
      · intro j _ hji
        have hj : x ∉ s j := fun hj ↦ (Set.disjoint_left.1 (hd hji)) hj hi
        simp only [g, indicator_of_notMem hj]
      · simp
    · have hall : ∀ i, x ∉ s i := by simpa only [not_exists] using hx
      simpa only [g, indicator_of_notMem (hall _), Finset.sum_const_zero] using hn x
  calc
    ∑ i, sphereMeasure.real (s i) * a i = ∫ x, ∑ i, g i x ∂sphereMeasure := by
      rw [integral_finsetSum _ (fun i _ ↦ hg i)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [g, integral_indicator_const (a i) (hs i), smul_eq_mul]
    _ ≤ ∫ x, f x ∂sphereMeasure := integral_mono hgint hf hpoint

theorem continuous_radial_gap {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) {m : ℝ} (hm : 0 < m) (t : ℝ) :
    Continuous (fun u : UnitSphere ↦ Radial.gap m t (radialFunction K u)) := by
  have hg : Continuous (Radial.gap m t) :=
    continuous_iff_continuousAt.2 fun s ↦ (Radial.hasDerivAt_gap hm t s).continuousAt
  exact hg.comp (continuous_radialFunction_sphere h0)

theorem integrable_radial_gap {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) {m : ℝ} (hm : 0 < m) (t : ℝ) :
    Integrable (fun u : UnitSphere ↦ Radial.gap m t (radialFunction K u)) sphereMeasure :=
  (continuous_radial_gap h0 hm t).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_radial_flux {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) {m : ℝ} (hm : 0 < m) :
    Integrable (fun u : UnitSphere ↦
      2 * radialFunction K u ^ 3 / (radialFunction K u ^ 2 + m)) sphereMeasure := by
  have hρ := continuous_radialFunction_sphere h0
  have hf : Continuous (fun u : UnitSphere ↦
      2 * radialFunction K u ^ 3 / (radialFunction K u ^ 2 + m)) :=
    (hρ.pow 3 |>.const_mul 2).div (hρ.pow 2 |>.add_const m) (fun _ ↦ by positivity)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integrated tangent identity with actual volume and the normalized sphere measure.
The geometric comparison of the flux integral with surface area is a separate obligation. -/
theorem integral_radial_gap_eq {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) {m : ℝ} (hm : 0 < m) (t : ℝ) :
    (∫ u : UnitSphere, Radial.gap m t (radialFunction K u) ∂sphereMeasure) =
      3 * Radial.slope m t * bodyVolume K + 4 * Real.pi * Radial.intercept m t -
        ∫ u : UnitSphere, 2 * radialFunction K u ^ 3 / (radialFunction K u ^ 2 + m)
          ∂sphereMeasure := by
  have hpow := (integrable_radialFunction_pow h0 3).const_mul (Radial.slope m t)
  have hadd : Integrable (fun u : UnitSphere ↦
      Radial.slope m t * radialFunction K u ^ 3 + Radial.intercept m t) sphereMeasure :=
    hpow.add (integrable_const _)
  simp only [Radial.gap]
  rw [integral_sub hadd (integrable_radial_flux h0 hm),
    integral_add hpow (integrable_const (Radial.intercept m t)), integral_const_mul,
    integral_radialFunction_cube h0, integral_const, sphereMeasure_real_univ, smul_eq_mul]
  ring

end BlaschkeLebesgue
