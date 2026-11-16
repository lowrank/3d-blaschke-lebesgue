module

public import BlaschkeLebesgue.Minkowski
public import BlaschkeLebesgue.CapIntegration
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Radial bounds for the volume of parallel bodies

The opposite-point inequality bounds how far a supporting plane can move along
each radial ray when a ball of radius `t` is added. Integrating its cubic radial
bound controls the actual outer parallel volume, including for nonsmooth bodies.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology

namespace BlaschkeLebesgue

theorem radialFunction_mono {K L : ConvexBody Space}
    (hK : (0 : Space) ∈ interior (K : Set Space))
    (hL : (0 : Space) ∈ interior (L : Set Space))
    (hKL : (K : Set Space) ⊆ (L : Set Space)) {u : Space} (hu : u ≠ 0) :
    radialFunction K u ≤ radialFunction L u :=
  (smul_mem_iff_le_radialFunction hL hu (radialFunction_pos hK hu).le).1
    (hKL (radialFunction_smul_mem hK hu))

/-- The radial expansion rate allowed by the opposite-point supporting plane. -/
@[expose] def radialExpansionSpeed (m r : ℝ) : ℝ := 2 * r / (r ^ 2 + m)

theorem radialExpansionSpeed_nonneg {m r : ℝ} (hm : 0 < m) (hr : 0 ≤ r) :
    0 ≤ radialExpansionSpeed m r := by unfold radialExpansionSpeed; positivity

theorem continuous_radialExpansionSpeed {m : ℝ} (hm : 0 < m) :
    Continuous (radialExpansionSpeed m) :=
  (continuous_id.const_mul 2).div ((continuous_id.pow 2).add_const m) (fun _ ↦ by positivity)

/-- A supporting plane gives a linear upper bound for every parallel radial distance. -/
theorem HasConstantWidth.radialFunction_parallelBody_le {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m t : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) (ht : 0 ≤ t) {u : Space} (hu : ‖u‖ = 1) :
    radialFunction (parallelBody K t) u ≤
      radialFunction K u + t * radialExpansionSpeed m (radialFunction K u) := by
  have hu0 : u ≠ 0 := by intro hh; simp [hh] at hu
  have h0t := zero_mem_interior_parallelBody h0 t
  let r := radialFunction K u
  let s := radialFunction (parallelBody K t) u
  have hr : 0 < r := radialFunction_pos h0 hu0
  have hrs : r ≤ s := radialFunction_mono h0 h0t (subset_parallelBody K t) hu0
  obtain ⟨n, hn, hns⟩ := radialFunction_supporting_normal h0 hu0
  have hp := inner_le_support (parallelBody K t) n (radialFunction_smul_mem h0t hu0)
  rw [support_parallelBody K ht hn, ← hns, inner_smul_right, inner_smul_right] at hp
  change s * ⟪n, u⟫_ℝ ≤ r * ⟪n, u⟫_ℝ + t at hp
  have hnormal := hK.radial_normal hR hbound (radialFunction_smul_mem h0 hu0) hn hns
  have hnormal' : r ^ 2 + m ≤ 2 * r * ⟪n, u⟫_ℝ := by
    change ‖r • u‖ ^ 2 + 1 - R ^ 2 ≤ 2 * ⟪r • u, n⟫_ℝ at hnormal
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one,
      real_inner_smul_left, real_inner_comm n u] at hnormal
    nlinarith only [hnormal, hmR]
  have hmul := mul_le_mul_of_nonneg_left hnormal' (sub_nonneg.2 hrs)
  have hp' : (s - r) * ⟪n, u⟫_ℝ ≤ t := by linarith only [hp]
  have hp'' := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 2 * r by positivity)
  have hstep : (s - r) * (r ^ 2 + m) ≤ t * (2 * r) := by
    nlinarith only [hmul, hp'']
  have hquot := (le_div_iff₀ (show 0 < r ^ 2 + m by positivity)).2 hstep
  change s ≤ r + t * (2 * r / (r ^ 2 + m))
  rw [← mul_div_assoc]
  linarith only [hquot]

theorem integral_cube_add_mul (f g : UnitSphere → ℝ)
    (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    (∫ u, (f u + t * g u) ^ 3 ∂sphereMeasure) =
      (∫ u, f u ^ 3 ∂sphereMeasure) + 3 * t * (∫ u, f u ^ 2 * g u ∂sphereMeasure) +
        3 * t ^ 2 * (∫ u, f u * g u ^ 2 ∂sphereMeasure) +
          t ^ 3 * (∫ u, g u ^ 3 ∂sphereMeasure) := by
  have hi (q : UnitSphere → ℝ) (hq : Continuous q) : Integrable q sphereMeasure :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : Integrable (fun u ↦ f u ^ 3) sphereMeasure := hi _ (by fun_prop)
  have h1 : Integrable (fun u ↦ 3 * t * (f u ^ 2 * g u)) sphereMeasure := hi _ (by fun_prop)
  have h2 : Integrable (fun u ↦ 3 * t ^ 2 * (f u * g u ^ 2)) sphereMeasure := hi _ (by fun_prop)
  have h3 : Integrable (fun u ↦ t ^ 3 * g u ^ 3) sphereMeasure := hi _ (by fun_prop)
  have h01 : Integrable (fun u ↦ f u ^ 3 + 3 * t * (f u ^ 2 * g u)) sphereMeasure := h0.add h1
  have h012 : Integrable (fun u ↦ f u ^ 3 + 3 * t * (f u ^ 2 * g u) +
      3 * t ^ 2 * (f u * g u ^ 2)) sphereMeasure := h01.add h2
  have hid (u : UnitSphere) : (f u + t * g u) ^ 3 =
      f u ^ 3 + 3 * t * (f u ^ 2 * g u) + 3 * t ^ 2 * (f u * g u ^ 2) +
        t ^ 3 * g u ^ 3 := by ring
  simp_rw [hid]
  rw [integral_add h012 h3, integral_add h01 h2, integral_add h0 h1,
    integral_const_mul, integral_const_mul, integral_const_mul]

/-- The radial flux integral from the manuscript, with its actual geometric measure. -/
@[expose] def radialFluxIntegral (K : ConvexBody Space) (m : ℝ) : ℝ :=
  ∫ u : UnitSphere, 2 * radialFunction K u ^ 3 / (radialFunction K u ^ 2 + m) ∂sphereMeasure

/-- The explicit quadratic error term in the parallel-volume bound. -/
@[expose] def parallelQuadraticTerm (K : ConvexBody Space) (m : ℝ) : ℝ :=
  ∫ u : UnitSphere, radialFunction K u * radialExpansionSpeed m (radialFunction K u) ^ 2
    ∂sphereMeasure

/-- The explicit cubic error term in the parallel-volume bound. -/
@[expose] def parallelCubicTerm (K : ConvexBody Space) (m : ℝ) : ℝ :=
  (∫ u : UnitSphere, radialExpansionSpeed m (radialFunction K u) ^ 3 ∂sphereMeasure) / 3

/-- A polynomial upper bound for actual parallel volume, valid for every `t ≥ 0`.
Its linear coefficient is exactly the radial flux integral. -/
theorem HasConstantWidth.parallelBody_volume_le {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m t : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) (ht : 0 ≤ t) :
    bodyVolume (parallelBody K t) ≤ bodyVolume K + t * radialFluxIntegral K m +
      t ^ 2 * parallelQuadraticTerm K m + t ^ 3 * parallelCubicTerm K m := by
  let ρ : UnitSphere → ℝ := fun u ↦ radialFunction K u
  let L : UnitSphere → ℝ := fun u ↦ radialExpansionSpeed m (ρ u)
  have hρ : Continuous ρ := continuous_radialFunction_sphere h0
  have hL : Continuous L := (continuous_radialExpansionSpeed hm).comp hρ
  have hi : Integrable (fun u ↦ (ρ u + t * L u) ^ 3) sphereMeasure :=
    (hρ.add (hL.const_mul t) |>.pow 3).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint (u : UnitSphere) : radialFunction (parallelBody K t) u ^ 3 ≤
      (ρ u + t * L u) ^ 3 :=
    pow_le_pow_left₀ (radialFunction_pos (zero_mem_interior_parallelBody h0 t)
      (UnitSphere.ne_zero u)).le
      (hK.radialFunction_parallelBody_le h0 hR hbound hm hmR ht (UnitSphere.norm_eq_one u)) _
  have hmono := integral_mono
    (integrable_radialFunction_pow (zero_mem_interior_parallelBody h0 t) 3) hi hpoint
  rw [integral_radialFunction_cube (zero_mem_interior_parallelBody h0 t),
    integral_cube_add_mul ρ L hρ hL t] at hmono
  have hlinear : (∫ u, ρ u ^ 2 * L u ∂sphereMeasure) = radialFluxIntegral K m := by
    apply integral_congr_ae
    exact Eventually.of_forall fun u ↦ by dsimp [ρ, L, radialExpansionSpeed]; ring
  rw [hlinear] at hmono
  have hvol : (∫ u, ρ u ^ 3 ∂sphereMeasure) = 3 * bodyVolume K :=
    integral_radialFunction_cube h0
  rw [hvol] at hmono
  change 3 * bodyVolume (parallelBody K t) ≤ 3 * bodyVolume K +
    3 * t * radialFluxIntegral K m + 3 * t ^ 2 * parallelQuadraticTerm K m +
      t ^ 3 * (∫ u : UnitSphere, radialExpansionSpeed m (radialFunction K u) ^ 3
        ∂sphereMeasure) at hmono
  unfold parallelCubicTerm
  nlinarith only [hmono]

theorem HasConstantWidth.parallelBody_volume_quotient_le {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m t : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) (ht : 0 < t) :
    (bodyVolume (parallelBody K t) - bodyVolume K) / t ≤
      radialFluxIntegral K m + t * parallelQuadraticTerm K m + t ^ 2 * parallelCubicTerm K m := by
  apply (div_le_iff₀ ht).2
  have h := hK.parallelBody_volume_le h0 hR hbound hm hmR ht.le
  nlinarith only [h]

theorem parallelVolume_bound_tendsto (K : ConvexBody Space) (m : ℝ) :
    Tendsto (fun t : ℝ ↦ radialFluxIntegral K m + t * parallelQuadraticTerm K m +
      t ^ 2 * parallelCubicTerm K m) (𝓝[>] 0) (𝓝 (radialFluxIntegral K m)) := by
  have hcont : Continuous (fun t : ℝ ↦ radialFluxIntegral K m +
      t * parallelQuadraticTerm K m + t ^ 2 * parallelCubicTerm K m) := by fun_prop
  simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The upper right volume-growth rate is bounded without assuming a derivative exists. -/
theorem HasConstantWidth.parallelBody_volume_quotient_eventually_lt {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (bodyVolume (parallelBody K t) - bodyVolume K) / t <
      radialFluxIntegral K m + ε := by
  have he := (parallelVolume_bound_tendsto K m).eventually_lt_const
    (lt_add_of_pos_right _ hε)
  filter_upwards [self_mem_nhdsWithin, he] with t ht he
  exact (hK.parallelBody_volume_quotient_le h0 hR hbound hm hmR ht).trans_lt he

/-- Any actual right derivative of parallel volume obeys the radial surface-area bound.
`BlaschkeIdentity.lean` supplies the derivative and its value for unit-width bodies. -/
theorem HasConstantWidth.parallelBody_deriv_le_of_hasDerivWithinAt {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (h0 : (0 : Space) ∈ interior (K : Set Space))
    {R m S : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (hm : 0 < m) (hmR : m ≤ 1 - R ^ 2)
    (hderiv : HasDerivWithinAt (fun t ↦ bodyVolume (parallelBody K t)) S (Ici 0) 0) :
    S ≤ radialFluxIntegral K m := by
  have hd := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).1
    (hderiv.mono (show Ioi (0 : ℝ) ⊆ Ici 0 from Ioi_subset_Ici_self))
  have hd' : Tendsto (fun t ↦ (bodyVolume (parallelBody K t) - bodyVolume K) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 S) := hd.congr' (Eventually.of_forall fun t ↦ by
        simp only [slope_def_field, sub_zero, parallelBody_zero])
  apply le_of_tendsto_of_tendsto hd' (parallelVolume_bound_tendsto K m)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hK.parallelBody_volume_quotient_le h0 hR hbound hm hmR ht

end BlaschkeLebesgue
