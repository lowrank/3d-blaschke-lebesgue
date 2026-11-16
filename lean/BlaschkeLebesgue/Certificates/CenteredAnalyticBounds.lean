module

public import BlaschkeLebesgue.Certificates.CenteredPointIntegral
public import BlaschkeLebesgue.Certificates.ProjectiveAnalyticBounds

/-!
# Candidate acceptance with centered point quadrature

Each entry carries its own precision, point grid, gradient grid, and proposed
outputs. The final theorem applies when the entries' boxes cover the known
triangle and every finite check succeeds. No universal success is asserted.
-/

@[expose] public section

open Set

namespace BlaschkeLebesgue.Certificates.CenteredAnalyticBounds

open FixedPoint ParameterCover ProjectiveAcceptance ProjectiveAnalyticBounds

def check (p np ng : ℕ) (c : Candidate) (w : Results) : Bool :=
  c.box.domainCheck && decide (0 < np ∧ 0 < ng) &&
    decide (c.valueLower ≤ ratValue p w.center ∧
      c.aLower ≤ ratValue p w.aSlope.lo ∧ ratValue p w.aSlope.hi ≤ c.aUpper ∧
      c.bLower ≤ ratValue p w.bSlope.lo ∧ ratValue p w.bSlope.hi ≤ c.bUpper) &&
    decide (CenteredProjective.check p np (rational p c.box.aMid) (rational p c.box.bMid) = some w.center ∧
      ProjectiveGradientIntegral.check p ng true (boxA p c.box) (boxB p c.box) = some w.aSlope ∧
      ProjectiveGradientIntegral.check p ng false (boxA p c.box) (boxB p c.box) = some w.bSlope)

theorem check_of_computations {p np ng : ℕ} {c : Candidate} {w : Results}
    (hbox : c.box.domainCheck = true) (hn : 0 < np ∧ 0 < ng)
    (hnum : c.valueLower ≤ ratValue p w.center ∧
      c.aLower ≤ ratValue p w.aSlope.lo ∧ ratValue p w.aSlope.hi ≤ c.aUpper ∧
      c.bLower ≤ ratValue p w.bSlope.lo ∧ ratValue p w.bSlope.hi ≤ c.bUpper)
    (hp : CenteredProjective.check p np (rational p c.box.aMid) (rational p c.box.bMid) = some w.center)
    (ha : ProjectiveGradientIntegral.check p ng true (boxA p c.box) (boxB p c.box) = some w.aSlope)
    (hb : ProjectiveGradientIntegral.check p ng false (boxA p c.box) (boxB p c.box) = some w.bSlope) :
    check p np ng c w = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hbox, hn⟩, hnum⟩, hp, ha, hb⟩

theorem check_sound {p np ng : ℕ} {c : Candidate} {w : Results} (hc : check p np ng c w = true) :
    c.AnalyticBounds Completion.fixedSquareIntegral := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hbox, hsize⟩, hnum⟩, hcalc⟩ := hc
  have hmid := domain_extended hbox (center_mem hbox)
  have hchi : |Completion.obliquity (c.box.aMid : ℝ) (c.box.bMid : ℝ)| < 1 :=
    Completion.obliquity_abs_lt_one_of_total_lt_one hmid.2.1 (by linarith [hmid.2.2])
  refine ⟨?_, ?_, ?_⟩
  · exact (le_value hnum.1).trans (CenteredProjective.check_sound hcalc.1 hsize.1
      (rational_contains p c.box.aMid) (rational_contains p c.box.bMid) hmid.1 hchi)
  · intro b hb
    have hs := ProjectiveGradientIntegral.check_secantBounds (fixed := b) hcalc.2.1 hsize.2
      (fun _ hz ↦ boxA_contains hz) (fun _ _ ↦ boxB_contains hb)
      (fun z hz ↦ domain_extended hbox (show c.box.Contains z b from ⟨hz.1, hz.2, hb⟩))
    exact secantBounds_weaken hs (le_value hnum.2.1) (value_le hnum.2.2.1)
  · intro a ha
    have hs := ProjectiveGradientIntegral.check_secantBounds (fixed := a) hcalc.2.2 hsize.2
      (fun _ _ ↦ boxA_contains ha) (fun _ hz ↦ boxB_contains hz)
      (fun z hz ↦ domain_extended hbox (show c.box.Contains a z from ⟨ha.1, ha.2, hz⟩))
    exact secantBounds_weaken hs (le_value hnum.2.2.2.1) (value_le hnum.2.2.2.2)

structure Entry where
  candidate : Candidate
  precision : ℕ
  pointGrid : ℕ
  gradientGrid : ℕ
  results : Results

def Entry.check (e : Entry) : Bool :=
  e.candidate.check && CenteredAnalyticBounds.check e.precision e.pointGrid e.gradientGrid e.candidate e.results

theorem Entry.check_of_checks {e : Entry} (ha : e.candidate.check = true)
    (hc : CenteredAnalyticBounds.check e.precision e.pointGrid e.gradientGrid e.candidate e.results = true) :
    e.check = true := by simpa only [Entry.check, Bool.and_eq_true] using And.intro ha hc

theorem completion_affine_lower_of_entries {entries : List Entry}
    (hboxes : entries.map (fun e ↦ e.candidate.box) = ParameterCover.Generated.boxes)
    (hchecks : entries.all Entry.check = true)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    (153 / 100000 : ℝ) - 601 / 100000 * a + 317 / 20000 * b < Completion.F a b := by
  obtain ⟨q, hq, hp⟩ := ParameterCover.Generated.covers ha hb hab
  rw [← hboxes] at hq
  obtain ⟨e, he, heq⟩ := List.mem_map.1 hq
  rw [← heq] at hp
  have hc := List.all_eq_true.1 hchecks e he
  simp only [Entry.check, Bool.and_eq_true] at hc
  have h := Candidate.check_sound hc.1 (check_sound hc.2) hp
  rw [← Completion.F_eq_fixedSquareIntegral ha hb hab] at h
  exact h

end BlaschkeLebesgue.Certificates.CenteredAnalyticBounds
