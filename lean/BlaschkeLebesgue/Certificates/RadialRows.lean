module

public import BlaschkeLebesgue.Certificates.Generated.Row7
public import BlaschkeLebesgue.Certificates.RadialGeometry
public import BlaschkeLebesgue.Certificates.RadialSoundness

/-!
# The eight checked radial rows and their complete radius cover

The generated row imports are chained to serialize the expensive kernel reductions
on machines with limited memory. The endpoint cover and real-valued margins below
are the arithmetic layer of the radial certificate, not a volume theorem about bodies.
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
