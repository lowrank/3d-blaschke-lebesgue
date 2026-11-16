module

public import BlaschkeLebesgue.ParameterBoxEstimate

/-!
# Exact final arithmetic for a projective parameter box

Acceptance is conditional on proved center-integral and coordinate-secant
enclosures. The checker verifies the final rational arithmetic; it does not
certify these analytic enclosures merely because they occur in a report.
-/

@[expose] public section

open Set

namespace BlaschkeLebesgue.Certificates

namespace ParameterCover.Box

def aHalf (q : Box) : ℚ := (q.aHi - q.aLo) / 2
def bHalf (q : Box) : ℚ := (q.bHi - q.bLo) / 2

theorem aMid_sub_aHalf (q : Box) : (q.aMid : ℝ) - (q.aHalf : ℝ) = (q.aLo : ℝ) := by
  simp only [aMid, aHalf, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  ring

theorem aMid_add_aHalf (q : Box) : (q.aMid : ℝ) + (q.aHalf : ℝ) = (q.aHi : ℝ) := by
  simp only [aMid, aHalf, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  ring

theorem bMid_sub_bHalf (q : Box) : (q.bMid : ℝ) - (q.bHalf : ℝ) = (q.bLo : ℝ) := by
  simp only [bMid, bHalf, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  ring

theorem bMid_add_bHalf (q : Box) : (q.bMid : ℝ) + (q.bHalf : ℝ) = (q.bHi : ℝ) := by
  simp only [bMid, bHalf, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  ring

end ParameterCover.Box

namespace ProjectiveAcceptance

def c0 : ℚ := 153 / 100000
def ca : ℚ := -601 / 100000
def cb : ℚ := 317 / 20000

structure Candidate where
  box : ParameterCover.Box
  reportedMargin : ℚ
  valueLower : ℚ
  aLower : ℚ
  aUpper : ℚ
  bLower : ℚ
  bUpper : ℚ
  deriving DecidableEq

def Candidate.margin (c : Candidate) : ℚ :=
  c.valueLower - (c0 + ca * c.box.aMid + cb * c.box.bMid) -
    (c.box.aHalf * max |c.aLower - ca| |c.aUpper - ca| +
      c.box.bHalf * max |c.bLower - cb| |c.bUpper - cb|)

def Candidate.check (c : Candidate) : Bool :=
  c.box.domainCheck && decide (c.aLower ≤ c.aUpper ∧ c.bLower ≤ c.bUpper ∧
    0 < c.reportedMargin ∧ c.reportedMargin ≤ c.margin)

/-- These are the outstanding analytic facts for a candidate. A successful
arithmetic check alone supplies none of them. -/
def Candidate.AnalyticBounds (c : Candidate) (H : ℝ → ℝ → ℝ) : Prop :=
  (c.valueLower : ℝ) ≤ H (c.box.aMid : ℝ) (c.box.bMid : ℝ) ∧
  (∀ y ∈ Icc (c.box.bLo : ℝ) (c.box.bHi : ℝ),
    SecantBounds (fun x ↦ H x y) (c.box.aLo : ℝ) (c.box.aHi : ℝ) (c.aLower : ℝ) (c.aUpper : ℝ)) ∧
  (∀ x ∈ Icc (c.box.aLo : ℝ) (c.box.aHi : ℝ),
    SecantBounds (H x) (c.box.bLo : ℝ) (c.box.bHi : ℝ) (c.bLower : ℝ) (c.bUpper : ℝ))

theorem Candidate.check_sound {c : Candidate} {H : ℝ → ℝ → ℝ} (hc : c.check = true)
    (hH : c.AnalyticBounds H) {a b : ℝ} (hp : c.box.Contains a b) :
    (153 / 100000 : ℝ) - 601 / 100000 * a + 317 / 20000 * b < H a b := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hdom := hc.1
  simp only [ParameterCover.Box.domainCheck, decide_eq_true_eq] at hdom
  have haHalf : (0 : ℝ) ≤ (c.box.aHalf : ℝ) := by
    apply (Rat.cast_nonneg (K := ℝ)).2
    exact div_nonneg (sub_nonneg.mpr hdom.2.1) (by norm_num)
  have hbHalf : (0 : ℝ) ≤ (c.box.bHalf : ℝ) := by
    apply (Rat.cast_nonneg (K := ℝ)).2
    exact div_nonneg (sub_nonneg.mpr hdom.2.2.2.1) (by norm_num)
  have hmargin : (0 : ℝ) < (c.margin : ℝ) :=
    (Rat.cast_pos (K := ℝ)).2 (hc.2.2.2.1.trans_le hc.2.2.2.2)
  simp only [margin, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_max, Rat.cast_abs] at hmargin
  have hA : ∀ y ∈ Icc ((c.box.bMid : ℝ) - (c.box.bHalf : ℝ)) ((c.box.bMid : ℝ) + (c.box.bHalf : ℝ)),
      SecantBounds (fun x ↦ H x y) ((c.box.aMid : ℝ) - (c.box.aHalf : ℝ))
        ((c.box.aMid : ℝ) + (c.box.aHalf : ℝ)) (c.aLower : ℝ) (c.aUpper : ℝ) := by
    simpa only [ParameterCover.Box.aMid_sub_aHalf, ParameterCover.Box.aMid_add_aHalf,
      ParameterCover.Box.bMid_sub_bHalf, ParameterCover.Box.bMid_add_bHalf] using hH.2.1
  have hB : ∀ x ∈ Icc ((c.box.aMid : ℝ) - (c.box.aHalf : ℝ)) ((c.box.aMid : ℝ) + (c.box.aHalf : ℝ)),
      SecantBounds (H x) ((c.box.bMid : ℝ) - (c.box.bHalf : ℝ))
        ((c.box.bMid : ℝ) + (c.box.bHalf : ℝ)) (c.bLower : ℝ) (c.bUpper : ℝ) := by
    simpa only [ParameterCover.Box.aMid_sub_aHalf, ParameterCover.Box.aMid_add_aHalf,
      ParameterCover.Box.bMid_sub_bHalf, ParameterCover.Box.bMid_add_bHalf] using hH.2.2
  have hx : a ∈ Icc ((c.box.aMid : ℝ) - (c.box.aHalf : ℝ)) ((c.box.aMid : ℝ) + (c.box.aHalf : ℝ)) := by
    simpa only [ParameterCover.Box.aMid_sub_aHalf, ParameterCover.Box.aMid_add_aHalf] using
      (show a ∈ Icc (c.box.aLo : ℝ) (c.box.aHi : ℝ) from ⟨hp.1, hp.2.1⟩)
  have hy : b ∈ Icc ((c.box.bMid : ℝ) - (c.box.bHalf : ℝ)) ((c.box.bMid : ℝ) + (c.box.bHalf : ℝ)) := by
    simpa only [ParameterCover.Box.bMid_sub_bHalf, ParameterCover.Box.bMid_add_bHalf] using
      (show b ∈ Icc (c.box.bLo : ℝ) (c.box.bHi : ℝ) from hp.2.2)
  have h := affine_lt_of_box_center_margin haHalf hbHalf hA hB hH.1 hmargin hx hy
  norm_num only [c0, ca, cb, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div, neg_mul] at h
  simpa only [sub_eq_add_neg] using h

end ProjectiveAcceptance
end BlaschkeLebesgue.Certificates
