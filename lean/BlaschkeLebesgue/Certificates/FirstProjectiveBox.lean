module

public import BlaschkeLebesgue.Certificates.CenteredAnalyticBounds
public import BlaschkeLebesgue.Certificates.CenteredFirst
public import BlaschkeLebesgue.Certificates.FirstGradient
public import BlaschkeLebesgue.Certificates.Generated.ProjectiveAcceptance

/-!
# An unconditional affine bound on the first certificate box

The center value, both coordinate secant intervals, and the final acceptance
arithmetic have kernel proofs. No reported numerical bound is a hypothesis.
-/

@[expose] public section

open Set

namespace BlaschkeLebesgue.Certificates.ProjectiveAcceptance.First

open FixedPoint

def candidate : Candidate :=
  ⟨⟨0, 1 / 800, 0, 1 / 800⟩, 15647245535 / 2251799813685248,
    3499295368065 / 2251799813685248, -38305472032463 / 4503599627370496,
    -4481399316083 / 2251799813685248, 23361772611441 / 4503599627370496,
    131824902922151 / 4503599627370496⟩

theorem candidate_matches : Generated.candidates[0]? = some candidate := by decide +kernel

theorem candidate_mem : candidate ∈ Generated.candidates := List.mem_of_getElem? candidate_matches

theorem arithmetic_verified : candidate.check = true :=
  List.all_eq_true.1 Generated.arithmetic_verified candidate candidate_mem

def entry : CenteredAnalyticBounds.Entry :=
  ⟨candidate, 52, 48, 64,
    ⟨7008754898294, ⟨-38305472032463, -8962798632166⟩, ⟨23361772611441, 131824902922151⟩⟩⟩

theorem computations_verified : CenteredAnalyticBounds.check 52 48 64 candidate entry.results = true := by
  have hma : ProjectiveAnalyticBounds.rational 52 candidate.box.aMid = Interval.rational 52 1 1600 := by
    decide +kernel
  have hmb : ProjectiveAnalyticBounds.rational 52 candidate.box.bMid = Interval.rational 52 1 1600 := by
    decide +kernel
  have hba : ProjectiveAnalyticBounds.boxA 52 candidate.box = ProjectiveGradientIntegral.First.box := by
    decide +kernel
  have hbb : ProjectiveAnalyticBounds.boxB 52 candidate.box = ProjectiveGradientIntegral.First.box := by
    decide +kernel
  apply CenteredAnalyticBounds.check_of_computations
  · decide +kernel
  · decide
  · decide +kernel
  · exact (congrArg₂ (CenteredProjective.check 52 48) hma hmb).trans CenteredProjective.First.point_verified
  · exact (congrArg₂ (ProjectiveGradientIntegral.check 52 64 true) hba hbb).trans
      ProjectiveGradientIntegral.First.check_a_verified
  · exact (congrArg₂ (ProjectiveGradientIntegral.check 52 64 false) hba hbb).trans
      ProjectiveGradientIntegral.First.check_b_verified

theorem entry_verified : entry.check = true :=
  CenteredAnalyticBounds.Entry.check_of_checks arithmetic_verified computations_verified

theorem analytic_bounds : candidate.AnalyticBounds Completion.fixedSquareIntegral :=
  CenteredAnalyticBounds.check_sound computations_verified

theorem affine_lower {a b : ℝ} (ha : a ∈ Icc 0 (1 / 800)) (hb : b ∈ Icc 0 (1 / 800)) :
    (153 / 100000 : ℝ) - 601 / 100000 * a + 317 / 20000 * b < Completion.F a b := by
  have hp : candidate.box.Contains a b := by
    norm_num [candidate, ParameterCover.Box.Contains]
    exact ⟨ha.1, ha.2, hb⟩
  have h := Candidate.check_sound arithmetic_verified analytic_bounds hp
  rw [← Completion.F_eq_fixedSquareIntegral ha.1 hb.1 (by linarith [ha.2, hb.2])] at h
  exact h

end BlaschkeLebesgue.Certificates.ProjectiveAcceptance.First
