module

public import BlaschkeLebesgue.Certificates.ClippedHullDerivatives
public import BlaschkeLebesgue.Certificates.ClippedHullCheckComputation

/-! # Analytic signs certified by successful clipped-hull box checks -/

public noncomputable section

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint ClippedDifferential Filter
open scoped Topology

attribute [local irreducible] dxProgram volumeProgram

theorem edgeSigns_sound {p n i j nr ne : ℕ} {R x : ℝ}
    (h : edgeSignCheck p n i j nr ne = true)
    (hR : (radiusInterval p i nr).Contains p R)
    (hx : (edgeSquaredInterval p j ne).Contains p x) :
    combinedDx R x < 0 ∧
      (∃ d, HasDerivAt (combinedDx R) d x ∧ d < 0) ∧
      (∃ d, HasDerivAt (fun t ↦ combinedDx t x) d R ∧ 0 < d) := by
  unfold edgeSignCheck at h
  cases hd : dxJet p n (Jet.const p (radiusInterval p i nr))
      (Jet.var p (edgeSquaredInterval p j ne)) with
  | none => simp [hd] at h
  | some dx =>
    cases hr : dxJet p n (Jet.var p (radiusInterval p i nr))
        (Jet.const p (edgeSquaredInterval p j ne)) with
    | none => simp [hd, hr] at h
    | some dr =>
      simp only [hd, hr, decide_eq_true_eq] at h
      have hc := dxJet_sound hd (Jet.contains_const hR) (Jet.contains_var hx)
      have hx' := dxJet_derivatives (a := fun _ ↦ SecondOrder.Jet.const R)
        (b := SecondOrder.Jet.var) hd (Jet.contains_const hR) (Jet.contains_var hx)
        (SecondOrder.Jet.validAt_const R x) (SecondOrder.Jet.validAt_var x)
      have hr' := dxJet_derivatives (a := SecondOrder.Jet.var)
        (b := fun _ ↦ SecondOrder.Jet.const x) hr (Jet.contains_var hR) (Jet.contains_const hx)
        (SecondOrder.Jet.validAt_var R) (SecondOrder.Jet.validAt_const x R)
      have hv : (dxRealJet (SecondOrder.Jet.const R) (SecondOrder.Jet.var x)).combined.v =
          combinedDx R x := by
        change (TrigProgram.realJet dxProgram _ 0).v = _
        rw [TrigProgram.realJet_v]
        have he : (fun k ↦ (inputEnv (SecondOrder.Jet.const R) (SecondOrder.Jet.var x) k).v) =
            inputEnv R x := by funext k; cases k <;> rfl
        rw [he]
        exact congrArg Derivatives.combined (dxProgram_real R x)
      refine ⟨?_, ⟨_, hx'.1, ?_⟩, ⟨_, hr'.1, ?_⟩⟩
      · rw [← hv]
        exact hc.2.2.1.2.trans_lt (value_neg_of_neg h.1)
      · exact hx'.2.2.trans_lt (value_neg_of_neg h.2.1)
      · exact (value_pos h.2.2).trans_le hr'.2.1

theorem baselineSign_sound {p n i nr : ℕ} {R : ℝ}
    (h : baselineSignCheck p n i nr = true)
    (hR : (radiusInterval p i nr).Contains p R) (hR0 : 1 / 2 < R) :
    ∃ d, HasDerivAt ClippedFormula.combinedBaseline d R ∧ 0 < d := by
  unfold baselineSignCheck at h
  cases hv : volumeJet p n (Jet.var p (radiusInterval p i nr))
      (Jet.const p (Interval.integer p 1)) with
  | none => simp [hv] at h
  | some v =>
    simp only [hv, decide_eq_true_eq] at h
    have h1 : (Interval.integer p 1).Contains p (1 : ℝ) := by
      exact_mod_cast Interval.contains_integer p 1
    have hd := volumeJet_derivatives (a := SecondOrder.Jet.var)
      (b := fun _ ↦ SecondOrder.Jet.const 1) hv (Jet.contains_var hR) (Jet.contains_const h1)
      (SecondOrder.Jet.validAt_var R) (SecondOrder.Jet.validAt_const 1 R)
    refine ⟨_, ?_, (value_pos h).trans_le hd.2.1⟩
    apply hd.1.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hR0] with t ht
    exact (realVolumes_baseline ht).symm

end BlaschkeLebesgue.Certificates.ClippedHull
