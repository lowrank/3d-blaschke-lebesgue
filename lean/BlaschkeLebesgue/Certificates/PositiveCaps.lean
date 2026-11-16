module

public import BlaschkeLebesgue.Certificates.RadialGrid
public import BlaschkeLebesgue.Normalization

/-! # Positive-cap certificates applied to the radial function -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue.Certificates.RadialArithmetic

theorem checkRow_parameter_bounds {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) :
    3 / 5 ≤ p.lo ∧ p.lo < p.hi ∧ p.hi ≤ 60849 / 100000 ∧
      5 / 8 ≤ parameterM p ∧ 1 - p.lo < p.tangentPoint ∧ p.tangentPoint < p.lo := by
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

theorem positiveStep_ordering {p : Parameters} {k : ℕ} {previous x : ℚ}
    (h : positiveStep p k previous x = true) : p.tangentPoint < x ∧ x < previous := by
  simp only [positiveStep, decide_eq_true_eq] at h
  tauto

theorem positiveChecks_step {p : Parameters} {xs : List ℕ} {k : ℕ} {previous : ℚ}
    (h : positiveChecks p k previous xs = true) (j : Fin xs.length) :
    ∃ q : ℚ, positiveStep p (k + j) q ((xs[j] : ℚ) / candidateScale) = true := by
  induction xs generalizing k previous with
  | nil => exact Fin.elim0 j
  | cons x xs ih =>
    simp only [positiveChecks, Bool.and_eq_true] at h
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · exact ⟨previous, by simpa using h.1⟩
    · obtain ⟨q, hq⟩ := ih h.2 i
      refine ⟨q, ?_⟩
      simpa [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq

theorem checkRow_parameters_pos {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) : 0 < parameterM p ∧ 0 < p.tangentPoint := by
  obtain ⟨_, hlohi, hhi, hM, htlo, _⟩ := checkRow_parameter_bounds h
  constructor <;> linarith

theorem checkRow_positive_candidate_gt_tangent {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) (j : Fin positive.length) :
    p.tangentPoint < (positive[j] : ℚ) / candidateScale := by
  have hp : positiveChecks p 1 p.lo positive = true := by
    simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at h
    tauto
  obtain ⟨_, hj⟩ := positiveChecks_step hp j
  exact (positiveStep_ordering hj).1

theorem checkRow_negative_candidate_le_tangent {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) (j : Fin negative.length) :
    (negative[j] : ℚ) / candidateScale ≤ p.tangentPoint := by
  have hn : negativeChecks p 1 0 negative = true := by
    simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at h
    tauto
  obtain ⟨_, hj⟩ := negativeChecks_step hn j
  simp only [negativeStep, decide_eq_true_eq] at hj
  tauto

/-- Every accepted propagation step has the required signs and geometric meaning
throughout its row's radius interval. -/
theorem positiveStep_radial_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {K : ConvexBody E}
    (hK : HasConstantWidth K 1) (h0 : (0 : E) ∈ interior (K : Set E))
    {p : Parameters} {positive negative : List ℕ} (hrow : checkRow p positive negative = true)
    {k : ℕ} {previous x : ℚ} (h : positiveStep p k previous x = true)
    (hprevious : previous ≤ p.lo) (hk : 1 ≤ k) (hkN : k ≤ gridSize)
    {R : ℝ} (hR : 0 ≤ R) (hRhi : R ≤ (p.hi : ℝ)) (hbound : ∀ z ∈ K, ‖z‖ ≤ R)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hangle : (stepCosine k : ℝ) ≤ ⟪u, v⟫_ℝ)
    (hprev : (previous : ℝ) ≤ radialFunction K u) : (x : ℝ) ≤ radialFunction K v := by
  obtain ⟨hlo, hlohi, hhi, hM, htlo, _⟩ := checkRow_parameter_bounds hrow
  obtain ⟨htx, hxp⟩ := positiveStep_ordering h
  have htan : 0 < p.tangentPoint := by linarith
  have hx : 0 < x := htan.trans htx
  have hy : 0 < previous := hx.trans hxp
  have hm : 0 < parameterM p := by linarith
  have hxcut : x ≤ 60849 / 100000 := hxp.le.trans (hprevious.trans (hlohi.le.trans hhi))
  have hxm : x ^ 2 ≤ parameterM p := by
    have hh := (sq_le_sq₀ hx.le (show (0 : ℚ) ≤ 60849 / 100000 by norm_num)).2 hxcut
    nlinarith only [hh, hM]
  have hmR : (parameterM p : ℝ) ≤ 1 - R ^ 2 := by
    have hsq := (sq_le_sq₀ hR (hR.trans hRhi)).2 hRhi
    simp only [parameterM, Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
    linarith only [hsq]
  obtain ⟨hrad, hlinear, htest⟩ := positiveStep_squares h
  exact hK.positive_cap_step h0 hR hbound (by exact_mod_cast hm) hmR
    (by exact_mod_cast hx) (by exact_mod_cast hy) (by exact_mod_cast hxm)
    (by exact_mod_cast (step_nonneg hk hkN).1) (by exact_mod_cast (step_nonneg hk hkN).2)
    (step_circle hk) (by exact_mod_cast hrad) (by exact_mod_cast hlinear)
    (by exact_mod_cast htest) hu hv hangle hprev

/-- Induction through the actual candidate list propagates its bounds over every
direction of each cap, rather than only along a sampled ray. -/
theorem positiveChecks_radial_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {K : ConvexBody E}
    (hK : HasConstantWidth K 1) (h0 : (0 : E) ∈ interior (K : Set E))
    {p : Parameters} {positive negative : List ℕ} (hrow : checkRow p positive negative = true)
    {R : ℝ} (hR : 0 ≤ R) (hRhi : R ≤ (p.hi : ℝ)) (hbound : ∀ z ∈ K, ‖z‖ ≤ R)
    {w : E} (hw : ‖w‖ = 1) {xs : List ℕ} {k : ℕ} {previous : ℚ}
    (hcheck : positiveChecks p k previous xs = true) (hprevious : previous ≤ p.lo)
    (hk : 1 ≤ k) (hlen : k + xs.length ≤ gridSize + 1)
    (hinitial : ∀ v ∈ sphericalCap w (cosine (k - 1) : ℝ),
      (previous : ℝ) ≤ radialFunction K v)
    (j : Fin xs.length) {u : E} (hcap : u ∈ sphericalCap w (cosine (k + j) : ℝ)) :
    (((xs[j] : ℚ) / candidateScale : ℚ) : ℝ) ≤ radialFunction K u := by
  induction xs generalizing k previous with
  | nil => exact Fin.elim0 j
  | cons x xs ih =>
    simp only [positiveChecks, Bool.and_eq_true] at hcheck
    have hkN : k ≤ gridSize := by simp only [List.length_cons] at hlen; omega
    have hhead : ∀ v ∈ sphericalCap w (cosine k : ℝ),
        (((x : ℚ) / candidateScale : ℚ) : ℝ) ≤ radialFunction K v := by
      intro v hv
      obtain ⟨z, hz, hnear⟩ := exists_preceding_grid_cap_point hw hk hkN hv
      exact positiveStep_radial_bound hK h0 hrow hcheck.1 hprevious hk hkN hR hRhi hbound
        hz.1 hv.1 hnear (hinitial z hz)
    have hnext : (x : ℚ) / candidateScale ≤ p.lo :=
      (positiveStep_ordering hcheck.1).2.le.trans hprevious
    cases j using Fin.cases with
    | zero => simpa using hhead u (by simpa using hcap)
    | succ j =>
      have hlen' : k + 1 + xs.length ≤ gridSize + 1 := by
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
      have hh := ih hcheck.2 hnext (by omega : 1 ≤ k + 1) hlen'
        (by simpa using hhead) j
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap)
      simpa using hh

/-- Apply every positive candidate to the actual contact directions of the body,
with the initial bound provided by their circumradius. -/
theorem checkRow_enclosing_positive_radial_bound {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4)
    {p : Parameters} {positive negative : List ℕ} (h : checkRow p positive negative = true)
    (hRlo : (p.lo : ℝ) ≤ b.radius) (hRhi : b.radius ≤ (p.hi : ℝ))
    (j : Fin positive.length) (i : Fin 4) {u : Space}
    (hcap : u ∈ sphericalCap (c.toBalancedContacts.direction i) (cosine (j + 1) : ℝ)) :
    (((positive[j] : ℚ) / candidateScale : ℚ) : ℝ) ≤ radialFunction b.centeredBody u := by
  have hrow := h
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hpositive : positiveChecks p 1 p.lo positive = true := by tauto
  have hlen : positive.length < gridSize := by tauto
  have hR : 0 < c.radius := by rw [c.radius_eq]; linarith [b.radius_ge_half hK]
  have hnorm := c.toBalancedContacts.direction_norm hR i
  have hpoint : b.radius • c.toBalancedContacts.direction i ∈ b.centeredBody := by
    rw [← c.radius_eq, c.toBalancedContacts.radius_smul_direction hR i]
    simpa [MinimumEnclosingBall.centeredBody] using c.point_mem i
  have hcontact := radialFunction_eq_of_contact (b.centeredBody_zero_mem_interior hK)
    b.radius_nonneg (fun _ hz ↦ b.centeredBody_norm_le hz) hnorm hpoint
  have hinitial : ∀ v ∈ sphericalCap (c.toBalancedContacts.direction i) (cosine 0 : ℝ),
      (p.lo : ℝ) ≤ radialFunction b.centeredBody v := by
    intro v hv
    have heq := eq_of_mem_sphericalCap_one hnorm
      (show v ∈ sphericalCap (c.toBalancedContacts.direction i) 1 by
        simpa [cosine, gridSize] using hv)
    rw [heq, hcontact]
    exact hRlo
  exact positiveChecks_radial_bound (b.centeredBody_width hK)
    (b.centeredBody_zero_mem_interior hK) h b.radius_nonneg hRhi
    (fun _ hz ↦ b.centeredBody_norm_le hz) hnorm hpositive le_rfl (by norm_num)
    (by omega) (by simpa using hinitial) j (by simpa [Nat.add_comm] using hcap)

/-- The rational positive candidate bounds the actual tangent deficit throughout
its cap. -/
theorem checkRow_positive_gap_lower {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4)
    {p : Parameters} {positive negative : List ℕ} (h : checkRow p positive negative = true)
    (hRlo : (p.lo : ℝ) ≤ b.radius) (hRhi : b.radius ≤ (p.hi : ℝ))
    (j : Fin positive.length) (i : Fin 4) {u : Space}
    (hcap : u ∈ sphericalCap (c.toBalancedContacts.direction i) (cosine (j + 1) : ℝ)) :
    (tangentGap p ((positive[j] : ℚ) / candidateScale) : ℝ) ≤
      Radial.gap (parameterM p) p.tangentPoint (radialFunction b.centeredBody u) := by
  have hbound := checkRow_enclosing_positive_radial_bound hK b c h hRlo hRhi j i hcap
  have ht := (Rat.cast_lt (K := ℝ)).2 (checkRow_positive_candidate_gt_tangent h j)
  obtain ⟨hm, htpos⟩ := checkRow_parameters_pos h
  rw [tangentGap_cast]
  exact Radial.gap_monotoneOn (by exact_mod_cast hm) (by exact_mod_cast htpos.le)
    ht.le (ht.le.trans hbound) hbound

/-- The rational negative candidate bounds the actual tangent deficit throughout
its cap. -/
theorem checkRow_negative_gap_lower {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4)
    {p : Parameters} {positive negative : List ℕ} (h : checkRow p positive negative = true)
    (hRlo : (p.lo : ℝ) ≤ b.radius) (j : Fin negative.length) (i : Fin 4) {u : Space}
    (hcap : u ∈ sphericalCap (-c.toBalancedContacts.direction i) (cosine (j + 1) : ℝ)) :
    (tangentGap p ((negative[j] : ℚ) / candidateScale) : ℝ) ≤
      Radial.gap (parameterM p) p.tangentPoint (radialFunction b.centeredBody u) := by
  have hu : u ≠ 0 := by intro hh; simpa [hh] using hcap.1
  have h0 := b.centeredBody_zero_mem_interior hK
  have hρ := radialFunction_pos h0 hu
  have hbound := checkRow_enclosing_negative_body_bound hK b c h hRlo j i hρ.le hcap
    (radialFunction_smul_mem h0 hu)
  have ht := (Rat.cast_le (K := ℝ)).2 (checkRow_negative_candidate_le_tangent h j)
  have hm := (checkRow_parameters_pos h).1
  rw [tangentGap_cast]
  exact Radial.gap_antitoneOn (by exact_mod_cast hm)
    ⟨hρ.le, hbound.trans ht⟩ ⟨hρ.le.trans hbound, ht⟩ hbound

/-- The four positive caps in each layer are disjoint, by the checked separation
test and the proved bounds for actual contact scalar products. -/
theorem checkRow_positive_caps_disjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {p : Parameters} {positive negative : List ℕ}
    (h : checkRow p positive negative = true) (c : BalancedContacts 4 E)
    (hR : (p.lo : ℝ) ≤ c.radius) (j : Fin positive.length) (a d : Fin 4) (had : a ≠ d) :
    Disjoint (sphericalCap (c.direction a) (cosine (j + 1) : ℝ))
      (sphericalCap (c.direction d) (cosine (j + 1) : ℝ)) := by
  have hrow := h
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hlo : (3 / 5 : ℚ) ≤ p.lo := by tauto
  have hlo' := (Rat.cast_le (K := ℝ)).2 hlo
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo'
  have hR' : 0 < c.radius := by linarith
  have hlen : positive.length < gridSize := by tauto
  have hpositive : positiveChecks p 1 p.lo positive = true := by tauto
  obtain ⟨q, hq⟩ := positiveChecks_step hpositive j
  simp only [positiveStep, decide_eq_true_eq] at hq
  have hsep : separationThreshold p < cosine (j + 1) ^ 2 - sine (j + 1) ^ 2 := by
    have hh : separationThreshold p < cosine (1 + j) ^ 2 - sine (1 + j) ^ 2 := by tauto
    simpa only [Nat.add_comm] using hh
  have hsep' : (separationThreshold p : ℝ) <
      (cosine (j + 1) : ℝ) ^ 2 - (sine (j + 1) : ℝ) ^ 2 := by exact_mod_cast hsep
  have hgeom := checkRow_contact_separation h c hR a d had
  have hcircle := grid_circle (j + 1)
  apply sphericalCap_disjoint (c.direction_norm hR' a) (c.direction_norm hR' d)
    (by exact_mod_cast cosine_nonneg (show (j : ℕ) + 1 ≤ gridSize by omega))
  linarith only [hgeom, hsep', hcircle]

/-- A positive cap and a negative cap cannot overlap: the actual radial function
would have to lie strictly above and at most at the same tangent point. -/
theorem checkRow_opposite_caps_disjoint {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (b : MinimumEnclosingBall K) (c : EnclosingContacts b 4)
    {p : Parameters} {positive negative : List ℕ} (h : checkRow p positive negative = true)
    (hRlo : (p.lo : ℝ) ≤ b.radius) (hRhi : b.radius ≤ (p.hi : ℝ))
    (j : Fin positive.length) (k : Fin negative.length) (a d : Fin 4) :
    Disjoint (sphericalCap (c.toBalancedContacts.direction a) (cosine (j + 1) : ℝ))
      (sphericalCap (-c.toBalancedContacts.direction d) (cosine (k + 1) : ℝ)) := by
  rw [Set.disjoint_left]
  intro u hu₁ hu₂
  have h0 := b.centeredBody_zero_mem_interior hK
  have hu : u ≠ 0 := by intro hh; simpa [hh] using hu₁.1
  have hpos := checkRow_enclosing_positive_radial_bound hK b c h hRlo hRhi j a hu₁
  have hneg := checkRow_enclosing_negative_body_bound hK b c h hRlo k d
    (radialFunction_pos h0 hu).le hu₂ (radialFunction_smul_mem h0 hu)
  have hpt := (Rat.cast_lt (K := ℝ)).2 (checkRow_positive_candidate_gt_tangent h j)
  have hnt := (Rat.cast_le (K := ℝ)).2 (checkRow_negative_candidate_le_tangent h k)
  linarith only [hpos, hneg, hpt, hnt]

end BlaschkeLebesgue.Certificates.RadialArithmetic
