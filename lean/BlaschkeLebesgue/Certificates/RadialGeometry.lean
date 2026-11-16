module

public import BlaschkeLebesgue.Certificates.RadialSoundness
public import BlaschkeLebesgue.ContactDirections
public import BlaschkeLebesgue.RadialAnalysis
public import BlaschkeLebesgue.RadialGeometry
public import BlaschkeLebesgue.Translation

/-! # Geometric meaning of the negative-cap certificates -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.Certificates.RadialArithmetic

theorem cosine_nonneg {k : ℕ} (hk : k ≤ gridSize) : 0 ≤ cosine k := by
  have hk' : (k : ℚ) ≤ (gridSize : ℚ) := by exact_mod_cast hk
  apply div_nonneg
  · nlinarith [sq_nonneg ((gridSize : ℚ) - k)]
  · positivity

theorem grid_circle (k : ℕ) : (cosine k : ℝ) ^ 2 + (sine k : ℝ) ^ 2 = 1 := by
  simp only [cosine, sine, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_pow,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
  apply Radial.rational_circle
  have hN : 0 < (gridSize : ℝ) := by norm_num [gridSize]
  positivity

theorem tangentGap_cast (p : Parameters) (x : ℚ) :
    (tangentGap p x : ℝ) = Radial.gap (parameterM p) p.tangentPoint x := by
  simp [tangentGap, parameterA, parameterB, Radial.gap, Radial.slope, Radial.intercept]

/-- An accepted negative-cap candidate bounds every actual body point in that cap. -/
theorem negativeStep_body_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : ConvexBody E} (hK : HasConstantWidth K 1)
    {p : Parameters} {k : ℕ} {previous z : ℚ}
    (h : negativeStep p k previous z = true) (hk : k ≤ gridSize) (hlo : 0 ≤ p.lo)
    {u v : E} {ρ R : ℝ} (hv : ‖v‖ = 1) (hρ : 0 ≤ ρ) (hR : (p.lo : ℝ) ≤ R)
    (hcap : u ∈ sphericalCap (-v) (cosine k : ℝ))
    (hx : ρ • u ∈ K) (hy : R • v ∈ K) : ρ ≤ (z : ℝ) := by
  have hangle : ⟪u, v⟫_ℝ ≤ -(cosine k : ℝ) := by
    have hh := hcap.2
    rw [inner_neg_left, real_inner_comm u v] at hh
    linarith
  exact (hK.negative_cap_bound hcap.1 hv hρ (by exact_mod_cast hlo) hR
    (by exact_mod_cast cosine_nonneg hk) (grid_circle k) hangle hx hy).trans
      (negativeStep_sound h)

/-- The candidate's rational tangent deficit is a lower bound for the actual
deficit at a body point in the cap. -/
theorem negativeStep_gap_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : ConvexBody E} (hK : HasConstantWidth K 1)
    {p : Parameters} {k : ℕ} {previous z : ℚ}
    (h : negativeStep p k previous z = true) (hk : k ≤ gridSize) (hlo : 0 ≤ p.lo)
    (hm : 0 < parameterM p) {u v : E} {ρ R : ℝ}
    (hv : ‖v‖ = 1) (hρ : 0 ≤ ρ) (hR : (p.lo : ℝ) ≤ R)
    (hcap : u ∈ sphericalCap (-v) (cosine k : ℝ))
    (hx : ρ • u ∈ K) (hy : R • v ∈ K) :
    (tangentGap p z : ℝ) ≤ Radial.gap (parameterM p) p.tangentPoint ρ := by
  have hbound := negativeStep_body_bound hK h hk hlo hv hρ hR hcap hx hy
  have hz : z ≤ p.tangentPoint := by
    simp only [negativeStep, decide_eq_true_eq] at h
    tauto
  have hz' : (z : ℝ) ≤ (p.tangentPoint : ℝ) := by exact_mod_cast hz
  rw [tangentGap_cast]
  exact Radial.gap_antitoneOn (by exact_mod_cast hm)
    ⟨hρ, hbound.trans hz'⟩ ⟨hρ.trans hbound, hz'⟩ hbound

/-- The recursive checker really checks the candidate at every list position. -/
theorem negativeChecks_step {p : Parameters} {xs : List ℕ} {k : ℕ} {previous : ℚ}
    (h : negativeChecks p k previous xs = true) (j : Fin xs.length) :
    ∃ q : ℚ, negativeStep p (k + j) q ((xs[j] : ℚ) / candidateScale) = true := by
  induction xs generalizing k previous with
  | nil => exact Fin.elim0 j
  | cons x xs ih =>
    simp only [negativeChecks, Bool.and_eq_true] at h
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · exact ⟨previous, by simpa using h.1⟩
    · obtain ⟨q, hq⟩ := ih h.2 i
      refine ⟨q, ?_⟩
      simpa [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq

/-- The full row checker implies the geometric upper bound for each of its
negative caps, including every direction inside the cap. -/
theorem checkRow_negative_body_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : ConvexBody E} (hK : HasConstantWidth K 1)
    {p : Parameters} {positive negative : List ℕ} (h : checkRow p positive negative = true)
    (j : Fin negative.length) {u v : E} {ρ R : ℝ}
    (hv : ‖v‖ = 1) (hρ : 0 ≤ ρ) (hR : (p.lo : ℝ) ≤ R)
    (hcap : u ∈ sphericalCap (-v) (cosine (j + 1) : ℝ))
    (hx : ρ • u ∈ K) (hy : R • v ∈ K) :
    ρ ≤ (((negative[j] : ℚ) / candidateScale : ℚ) : ℝ) := by
  have hrow := h
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hlo : (3 / 5 : ℚ) ≤ p.lo := by tauto
  have hlen : negative.length < gridSize := by tauto
  have hnegative : negativeChecks p 1 0 negative = true := by tauto
  obtain ⟨q, hq⟩ := negativeChecks_step hnegative j
  have hk : (j : ℕ) + 1 ≤ gridSize := by omega
  apply negativeStep_body_bound hK (previous := q) (k := j + 1)
    (by simpa [Nat.add_comm] using hq) hk (by linarith) hv hρ hR hcap hx hy

/-- The separation threshold in the certificate is valid for genuine balanced
contacts throughout the row's entire radius interval. -/
theorem checkRow_contact_separation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) (c : BalancedContacts 4 E)
    (hR : (p.lo : ℝ) ≤ c.radius) (i j : Fin 4) (hij : i ≠ j) :
    ⟪c.direction i, c.direction j⟫_ℝ ≤ (separationThreshold p : ℝ) := by
  have hrow := h
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hlo : (3 / 5 : ℚ) ≤ p.lo := by tauto
  have hhi : p.lo < (60849 / 100000 : ℚ) := by
    have h₁ : p.lo < p.hi := by tauto
    have h₂ : p.hi ≤ 60849 / 100000 := by tauto
    exact h₁.trans_le h₂
  have hlo' := (Rat.cast_le (K := ℝ)).2 hlo
  have hhi' := (Rat.cast_lt (K := ℝ)).2 hhi
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo' hhi'
  have hp : 0 < (p.lo : ℝ) := by linarith
  have hR' : 0 < c.radius := hp.trans_le hR
  let η : ℝ := 1 / (2 * (p.lo : ℝ) ^ 2) - 1
  have hden : 0 < 2 * (p.lo : ℝ) ^ 2 := by positivity
  have hη : 0 ≤ η := by
    have hh : (1 : ℝ) ≤ 1 / (2 * (p.lo : ℝ) ^ 2) :=
      (le_div_iff₀ hden).2 (by nlinarith)
    dsimp [η]
    linarith
  have hη' : η < 1 := by
    have hh : 1 / (2 * (p.lo : ℝ) ^ 2) < (2 : ℝ) :=
      (div_lt_iff₀ hden).2 (by nlinarith)
    dsimp [η]
    linarith
  have hidentity : 2 * (p.lo : ℝ) ^ 2 * (1 + η) = 1 := by
    dsimp [η]
    field_simp
    ring
  have hbudget : 1 ≤ 2 * c.radius ^ 2 * (1 + η) := by
    calc
      1 = 2 * (p.lo : ℝ) ^ 2 * (1 + η) := hidentity.symm
      _ ≤ 2 * c.radius ^ 2 * (1 + η) := by gcongr
  have hthreshold : (separationThreshold p : ℝ) = 4 * η ^ 2 / (1 - η) - 1 := by
    simp [separationThreshold, η]
  rw [hthreshold]
  exact c.direction_inner_upper hR' hη hη' hbudget i j hij

/-- Every negative-cap layer has pairwise disjoint caps at the four contact
directions, as a consequence of the checked separation inequalities. -/
theorem checkRow_negative_caps_disjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) (c : BalancedContacts 4 E)
    (hR : (p.lo : ℝ) ≤ c.radius) (j : Fin negative.length) (a b : Fin 4) (hab : a ≠ b) :
    Disjoint (sphericalCap (-c.direction a) (cosine (j + 1) : ℝ))
      (sphericalCap (-c.direction b) (cosine (j + 1) : ℝ)) := by
  have hrow := h
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hlo : (3 / 5 : ℚ) ≤ p.lo := by tauto
  have hlo' := (Rat.cast_le (K := ℝ)).2 hlo
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo'
  have hR' : 0 < c.radius := by linarith
  have hlen : negative.length < gridSize := by tauto
  have hnegative : negativeChecks p 1 0 negative = true := by tauto
  obtain ⟨q, hq⟩ := negativeChecks_step hnegative j
  simp only [negativeStep, decide_eq_true_eq] at hq
  have hsep : separationThreshold p < cosine (j + 1) ^ 2 - sine (j + 1) ^ 2 := by
    simpa only [Nat.add_comm] using hq.2.2.2.2.1
  have hsep' : (separationThreshold p : ℝ) <
      (cosine (j + 1) : ℝ) ^ 2 - (sine (j + 1) : ℝ) ^ 2 := by exact_mod_cast hsep
  have hgeom := checkRow_contact_separation h c hR a b hab
  have hcircle := grid_circle (j + 1)
  apply sphericalCap_disjoint
    (by simpa using c.direction_norm hR' a) (by simpa using c.direction_norm hR' b)
    (by exact_mod_cast cosine_nonneg (show (j : ℕ) + 1 ≤ gridSize by omega))
  simp only [inner_neg_left, inner_neg_right, neg_neg]
  linarith

/-- Apply the checked negative caps to the actual contacts constructed from a
unit-width body, after translating its minimum enclosing center to zero. -/
theorem checkRow_enclosing_negative_body_bound {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4)
    {p : Parameters} {positive negative : List ℕ} (h : checkRow p positive negative = true)
    (hR : (p.lo : ℝ) ≤ b.radius) (j : Fin negative.length) (i : Fin 4)
    {u : Space} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcap : u ∈ sphericalCap (-c.toBalancedContacts.direction i) (cosine (j + 1) : ℝ))
    (hx : ρ • u ∈ b.centeredBody) :
    ρ ≤ (((negative[j] : ℚ) / candidateScale : ℚ) : ℝ) := by
  have hR' : 0 < c.radius := by rw [c.radius_eq]; linarith [b.radius_ge_half hK]
  apply checkRow_negative_body_bound (b.centeredBody_width hK) h j
    (c.toBalancedContacts.direction_norm hR' i) hρ hR hcap hx
  rw [← c.radius_eq, c.toBalancedContacts.radius_smul_direction hR' i]
  simpa [MinimumEnclosingBall.centeredBody] using c.point_mem i

end BlaschkeLebesgue.Certificates.RadialArithmetic
