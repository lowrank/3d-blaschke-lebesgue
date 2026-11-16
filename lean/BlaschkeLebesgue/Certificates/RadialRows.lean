module

public import BlaschkeLebesgue.Certificates.Generated.Row7
public import BlaschkeLebesgue.Certificates.CapIntegrals
public import BlaschkeLebesgue.Certificates.PositiveCaps
public import BlaschkeLebesgue.Certificates.RadialGeometry
public import BlaschkeLebesgue.Certificates.RadialSoundness

/-!
# The eight checked radial rows and their complete radius cover

The generated row imports are chained to serialize the expensive kernel reductions
on machines with limited memory. The endpoint cover, real-valued margins, and cap
geometry are proved below, including the actual spherical deficit integrals.
The surface-area argument and the volume theorem remain open.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.RadialArithmetic

structure Row where
  parameters : Parameters
  positive : List ℕ
  negative : List ℕ

def rows : Fin 8 → Row := ![
  ⟨Row0.parameters, Row0.positive, Row0.negative⟩,
  ⟨Row1.parameters, Row1.positive, Row1.negative⟩,
  ⟨Row2.parameters, Row2.positive, Row2.negative⟩,
  ⟨Row3.parameters, Row3.positive, Row3.negative⟩,
  ⟨Row4.parameters, Row4.positive, Row4.negative⟩,
  ⟨Row5.parameters, Row5.positive, Row5.negative⟩,
  ⟨Row6.parameters, Row6.positive, Row6.negative⟩,
  ⟨Row7.parameters, Row7.positive, Row7.negative⟩]

theorem all_rows_verified (i : Fin 8) :
    checkRow (rows i).parameters (rows i).positive (rows i).negative = true := by
  fin_cases i
  · exact Row0.verified
  · exact Row1.verified
  · exact Row2.verified
  · exact Row3.verified
  · exact Row4.verified
  · exact Row5.verified
  · exact Row6.verified
  · exact Row7.verified

theorem all_rows_real_margin (i : Fin 8) :
    (4144109 / 10000000 : ℝ) < Real.pi *
      (coefficient (rows i).parameters (rows i).positive (rows i).negative : ℝ) :=
  checkRow_real_margin (all_rows_verified i)

/-- Every stored row bounds the actual deficit integral of a centered unit-width
body in its radius interval. The four contacts are constructed from the body. -/
theorem all_rows_gap_integral_lower {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (row : Fin 8)
    (hRlo : ((rows row).parameters.lo : ℝ) ≤ b.radius)
    (hRhi : b.radius ≤ ((rows row).parameters.hi : ℝ)) :
    8 * Real.pi *
      (((((roundedSum (rows row).parameters 1 (rows row).positive +
        roundedSum (rows row).parameters 1 (rows row).negative : ℤ) : ℚ) /
          roundingScale : ℚ) : ℝ)) ≤
      ∫ u : UnitSphere, Radial.gap (parameterM (rows row).parameters)
        (rows row).parameters.tangentPoint (radialFunction b.centeredBody u) ∂sphereMeasure := by
  have hrow := all_rows_verified row
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hlo : (3 / 5 : ℚ) ≤ (rows row).parameters.lo := by tauto
  have hlo' := (Rat.cast_le (K := ℝ)).2 hlo
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo'
  have hR : (1 / 3 : ℝ) < b.radius ^ 2 := by nlinarith only [hRlo, hlo']
  obtain ⟨c⟩ := b.exists_four_contacts hK hR
  exact checkRow_rounded_gap_integral_lower hK b c (all_rows_verified row) hRlo hRhi

/-- All 14,814 negative candidates bound actual body points in their respective
contact caps. Their validity is discharged by the kernel-checked row theorems. -/
theorem all_rows_negative_body_bound {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4) (row : Fin 8)
    (hR : ((rows row).parameters.lo : ℝ) ≤ b.radius)
    (j : Fin (rows row).negative.length) (i : Fin 4) {u : Space} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcap : u ∈ sphericalCap (-c.toBalancedContacts.direction i) (cosine (j + 1) : ℝ))
    (hx : ρ • u ∈ b.centeredBody) :
    ρ ≤ ((((rows row).negative[j] : ℚ) / candidateScale : ℚ) : ℝ) :=
  checkRow_enclosing_negative_body_bound hK b c (all_rows_verified row) hR j i hρ hcap hx

/-- The four negative caps in any layer of any stored row are disjoint for the
actual enclosing contacts. -/
theorem all_rows_negative_caps_disjoint {K : ConvexBody Space} {b : MinimumEnclosingBall K}
    (c : EnclosingContacts b 4) (row : Fin 8)
    (hR : ((rows row).parameters.lo : ℝ) ≤ b.radius)
    (j : Fin (rows row).negative.length) (a d : Fin 4) (had : a ≠ d) :
    Disjoint (sphericalCap (-c.toBalancedContacts.direction a) (cosine (j + 1) : ℝ))
      (sphericalCap (-c.toBalancedContacts.direction d) (cosine (j + 1) : ℝ)) :=
  checkRow_negative_caps_disjoint (all_rows_verified row) c.toBalancedContacts
    (c.radius_eq ▸ hR) j a d had

/-- All 5,836 positive candidates give lower bounds for the actual radial function. -/
theorem all_rows_positive_radial_bound {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4) (row : Fin 8)
    (hRlo : ((rows row).parameters.lo : ℝ) ≤ b.radius)
    (hRhi : b.radius ≤ ((rows row).parameters.hi : ℝ))
    (j : Fin (rows row).positive.length) (i : Fin 4) {u : Space}
    (hcap : u ∈ sphericalCap (c.toBalancedContacts.direction i) (cosine (j + 1) : ℝ)) :
    ((((rows row).positive[j] : ℚ) / candidateScale : ℚ) : ℝ) ≤
      radialFunction b.centeredBody u :=
  checkRow_enclosing_positive_radial_bound hK b c (all_rows_verified row) hRlo hRhi j i hcap

theorem all_rows_positive_gap_lower {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4) (row : Fin 8)
    (hRlo : ((rows row).parameters.lo : ℝ) ≤ b.radius)
    (hRhi : b.radius ≤ ((rows row).parameters.hi : ℝ))
    (j : Fin (rows row).positive.length) (i : Fin 4) {u : Space}
    (hcap : u ∈ sphericalCap (c.toBalancedContacts.direction i) (cosine (j + 1) : ℝ)) :
    (tangentGap (rows row).parameters ((rows row).positive[j] / candidateScale) : ℝ) ≤
      Radial.gap (parameterM (rows row).parameters) (rows row).parameters.tangentPoint
        (radialFunction b.centeredBody u) :=
  checkRow_positive_gap_lower hK b c (all_rows_verified row) hRlo hRhi j i hcap

theorem all_rows_negative_gap_lower {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4) (row : Fin 8)
    (hRlo : ((rows row).parameters.lo : ℝ) ≤ b.radius)
    (j : Fin (rows row).negative.length) (i : Fin 4) {u : Space}
    (hcap : u ∈ sphericalCap (-c.toBalancedContacts.direction i) (cosine (j + 1) : ℝ)) :
    (tangentGap (rows row).parameters ((rows row).negative[j] / candidateScale) : ℝ) ≤
      Radial.gap (parameterM (rows row).parameters) (rows row).parameters.tangentPoint
        (radialFunction b.centeredBody u) :=
  checkRow_negative_gap_lower hK b c (all_rows_verified row) hRlo j i hcap

theorem all_rows_positive_caps_disjoint {K : ConvexBody Space} {b : MinimumEnclosingBall K}
    (c : EnclosingContacts b 4) (row : Fin 8)
    (hRlo : ((rows row).parameters.lo : ℝ) ≤ b.radius)
    (j : Fin (rows row).positive.length) (a d : Fin 4) (had : a ≠ d) :
    Disjoint (sphericalCap (c.toBalancedContacts.direction a) (cosine (j + 1) : ℝ))
      (sphericalCap (c.toBalancedContacts.direction d) (cosine (j + 1) : ℝ)) :=
  checkRow_positive_caps_disjoint (all_rows_verified row) c.toBalancedContacts
    (c.radius_eq ▸ hRlo) j a d had

theorem all_rows_opposite_caps_disjoint {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4) (row : Fin 8)
    (hRlo : ((rows row).parameters.lo : ℝ) ≤ b.radius)
    (hRhi : b.radius ≤ ((rows row).parameters.hi : ℝ))
    (j : Fin (rows row).positive.length) (k : Fin (rows row).negative.length) (a d : Fin 4) :
    Disjoint (sphericalCap (c.toBalancedContacts.direction a) (cosine (j + 1) : ℝ))
      (sphericalCap (-c.toBalancedContacts.direction d) (cosine (k + 1) : ℝ)) :=
  checkRow_opposite_caps_disjoint hK b c (all_rows_verified row) hRlo hRhi j k a d

/-- The rational radius intervals cover the entire intermediate-radius branch. -/
theorem radius_cover {r : ℝ} (hr : r ∈ Set.Icc (3 / 5) (60849 / 100000)) :
    ∃ i : Fin 8, (rows i).parameters.lo ≤ r ∧ r ≤ (rows i).parameters.hi := by
  by_cases h₀ : r ≤ 121 / 200
  · refine ⟨0, ?_⟩
    norm_num [rows, Row0.parameters]
    exact ⟨hr.1, h₀⟩
  by_cases h₁ : r ≤ 607 / 1000
  · refine ⟨1, ?_⟩
    norm_num [rows, Row1.parameters]
    constructor <;> linarith
  by_cases h₂ : r ≤ 76 / 125
  · refine ⟨2, ?_⟩
    norm_num [rows, Row2.parameters]
    constructor <;> linarith
  by_cases h₃ : r ≤ 2433 / 4000
  · refine ⟨3, ?_⟩
    norm_num [rows, Row3.parameters]
    constructor <;> linarith
  by_cases h₄ : r ≤ 1521 / 2500
  · refine ⟨4, ?_⟩
    norm_num [rows, Row4.parameters]
    constructor <;> linarith
  by_cases h₅ : r ≤ 12169 / 20000
  · refine ⟨5, ?_⟩
    norm_num [rows, Row5.parameters]
    constructor <;> linarith
  by_cases h₆ : r ≤ 24339 / 40000
  · refine ⟨6, ?_⟩
    norm_num [rows, Row6.parameters]
    constructor <;> linarith
  · refine ⟨7, ?_⟩
    norm_num [rows, Row7.parameters]
    exact ⟨by linarith, hr.2⟩

/-- Every radius in the interval has a kernel-checked row with a strict uniform margin. -/
theorem certified_radius_cover {r : ℝ}
    (hr : r ∈ Set.Icc (3 / 5) (60849 / 100000)) :
    ∃ i : Fin 8, (rows i).parameters.lo ≤ r ∧ r ≤ (rows i).parameters.hi ∧
      (4144109 / 10000000 : ℝ) < Real.pi *
        (coefficient (rows i).parameters (rows i).positive (rows i).negative : ℝ) := by
  obtain ⟨i, hlo, hhi⟩ := radius_cover hr
  exact ⟨i, hlo, hhi, all_rows_real_margin i⟩

end BlaschkeLebesgue.Certificates.RadialArithmetic
