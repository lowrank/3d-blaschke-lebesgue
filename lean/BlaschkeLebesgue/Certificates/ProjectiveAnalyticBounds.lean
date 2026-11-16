module

public import BlaschkeLebesgue.Certificates.ProjectiveGradientIntegral
public import BlaschkeLebesgue.Certificates.Generated.ProjectiveAcceptance

/-!
# From executable certificate checks to the candidate analytic bounds

The only inputs beyond a candidate are integer computation results. The
checker verifies the point and gradient computations themselves, then proves
the center-integral and coordinate-secant facts used by final box acceptance.
The full 584-candidate computation check is defined but not asserted true.
-/

@[expose] public section

open Set

namespace BlaschkeLebesgue.Certificates.ProjectiveAnalyticBounds

open FixedPoint ParameterCover ProjectiveAcceptance

def rational (p : ℕ) (q : ℚ) : Interval := Interval.rational p q.num q.den
def boxA (p : ℕ) (q : Box) : Interval := Interval.span (rational p q.aLo) (rational p q.aHi)
def boxB (p : ℕ) (q : Box) : Interval := Interval.span (rational p q.bLo) (rational p q.bHi)
def ratValue (p : ℕ) (z : ℤ) : ℚ := z / (scale p)

theorem rational_contains (p : ℕ) (q : ℚ) : (rational p q).Contains p (q : ℝ) := by
  simpa only [rational, Rat.cast_def, Int.cast_natCast] using Interval.contains_rational p q.num q.den

theorem boxA_contains {p : ℕ} {q : Box} {a : ℝ} (h : a ∈ Icc (q.aLo : ℝ) (q.aHi : ℝ)) :
    (boxA p q).Contains p a := Interval.contains_span (rational_contains p q.aLo) (rational_contains p q.aHi) h.1 h.2

theorem boxB_contains {p : ℕ} {q : Box} {b : ℝ} (h : b ∈ Icc (q.bLo : ℝ) (q.bHi : ℝ)) :
    (boxB p q).Contains p b := Interval.contains_span (rational_contains p q.bLo) (rational_contains p q.bHi) h.1 h.2

theorem ratValue_cast (p : ℕ) (z : ℤ) : (ratValue p z : ℝ) = value p z := by
  simp only [ratValue, value, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]

theorem le_value {p : ℕ} {q : ℚ} {z : ℤ} (h : q ≤ ratValue p z) : (q : ℝ) ≤ value p z := by
  simpa only [ratValue_cast] using (Rat.cast_le (K := ℝ)).2 h

theorem value_le {p : ℕ} {q : ℚ} {z : ℤ} (h : ratValue p z ≤ q) : value p z ≤ (q : ℝ) := by
  simpa only [ratValue_cast] using (Rat.cast_le (K := ℝ)).2 h

theorem center_mem {q : Box} (hq : q.domainCheck = true) : q.Contains (q.aMid : ℝ) (q.bMid : ℝ) := by
  have hd : 0 ≤ q.aLo ∧ q.aLo ≤ q.aHi ∧ 0 ≤ q.bLo ∧ q.bLo ≤ q.bHi ∧ q.aHi + q.bHi ≤ 17 / 200 :=
    of_decide_eq_true hq
  have ha : q.aLo ≤ q.aMid ∧ q.aMid ≤ q.aHi := by
    unfold Box.aMid
    constructor <;> linarith [hd.2.1]
  have hb : q.bLo ≤ q.bMid ∧ q.bMid ≤ q.bHi := by
    unfold Box.bMid
    constructor <;> linarith [hd.2.2.2.1]
  exact ⟨(Rat.cast_le (K := ℝ)).2 ha.1, (Rat.cast_le (K := ℝ)).2 ha.2,
    (Rat.cast_le (K := ℝ)).2 hb.1, (Rat.cast_le (K := ℝ)).2 hb.2⟩

theorem domain_extended {q : Box} (hq : q.domainCheck = true) {a b : ℝ} (h : q.Contains a b) :
    0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 / 10 := by
  have hd := Box.domainCheck_sound hq h
  exact ⟨hd.1, hd.2.1, by linarith [hd.2.2]⟩

structure Results where
  center : ℤ
  aSlope : Interval
  bSlope : Interval
  deriving DecidableEq, Inhabited

def check (p np ng : ℕ) (c : Candidate) (w : Results) : Bool :=
  c.box.domainCheck && decide (0 < np ∧ 0 < ng) &&
    decide (c.valueLower ≤ ratValue p w.center ∧
      c.aLower ≤ ratValue p w.aSlope.lo ∧ ratValue p w.aSlope.hi ≤ c.aUpper ∧
      c.bLower ≤ ratValue p w.bSlope.lo ∧ ratValue p w.bSlope.hi ≤ c.bUpper) &&
    decide (ProjectivePointIntegral.check p np (rational p c.box.aMid) (rational p c.box.bMid) = some w.center ∧
      ProjectiveGradientIntegral.check p ng true (boxA p c.box) (boxB p c.box) = some w.aSlope ∧
      ProjectiveGradientIntegral.check p ng false (boxA p c.box) (boxB p c.box) = some w.bSlope)

theorem secantBounds_weaken {f : ℝ → ℝ} {l r m M m' M' : ℝ}
    (h : SecantBounds f l r m M) (hm : m' ≤ m) (hM : M ≤ M') : SecantBounds f l r m' M' := by
  intro x hx y hy hxy
  have hb := h x hx y hy hxy
  exact ⟨(mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hxy)).trans hb.1,
    hb.2.trans (mul_le_mul_of_nonneg_right hM (sub_nonneg.mpr hxy))⟩

theorem check_sound {p np ng : ℕ} {c : Candidate} {w : Results} (hc : check p np ng c w = true) :
    c.AnalyticBounds Completion.fixedSquareIntegral := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hbox, hsize⟩, hnum⟩, hcalc⟩ := hc
  have hmid := domain_extended hbox (center_mem hbox)
  have hchi : |Completion.obliquity (c.box.aMid : ℝ) (c.box.bMid : ℝ)| < 1 :=
    Completion.obliquity_abs_lt_one_of_total_lt_one hmid.2.1 (by linarith [hmid.2.2])
  refine ⟨?_, ?_, ?_⟩
  · exact (le_value hnum.1).trans (ProjectivePointIntegral.check_sound hcalc.1 hsize.1
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

/-- Convert candidate rational columns to proposed fixed-dyadic integers.
The checker verifies both these proposals and all corresponding computations. -/
def proposal (p : ℕ) (q : ℚ) : ℤ := floorDiv (q.num * scale p) q.den

def recordedResults (p : ℕ) (c : Candidate) : Results :=
  ⟨proposal p c.valueLower, ⟨proposal p c.aLower, proposal p c.aUpper⟩,
    ⟨proposal p c.bLower, proposal p c.bUpper⟩⟩

/-- This is the remaining finite projective check. Its truth is not assumed
or claimed by any declaration in this module. -/
def allComputations : Bool := Generated.candidates.all fun c ↦ check 52 192 64 c (recordedResults 52 c)

theorem completion_affine_lower_of_computations (h : allComputations = true)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 / 25) :
    (153 / 100000 : ℝ) - 601 / 100000 * a + 317 / 20000 * b < Completion.F a b := by
  apply Generated.completion_affine_lower_of_analytic_bounds _ ha hb hab
  intro c hc
  exact check_sound (List.all_eq_true.1 h c hc)

end BlaschkeLebesgue.Certificates.ProjectiveAnalyticBounds
