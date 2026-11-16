module

public import BlaschkeLebesgue.Certificates.InverseTrigIntervalJet

/-! # Kernel-checked 128-bit inverse-trigonometric enclosures

These concrete checks exercise the Machin formula, half-angle reduction,
negative arguments, and derivative enclosures. The proposed integers are
recomputed by the kernel; no native-evaluation axiom is used.
-/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BlaschkeLebesgue.Certificates.InverseTrigExamples

open FixedPoint

def piEnclosure : Interval :=
  ⟨1069028584064966747859680373161870783288, 1069028584064966747859680373161870783328⟩

def asinHalfEnclosure : Jet :=
  ⟨⟨178171430677494457976613395526978463880, 178171430677494457976613395526978463886⟩,
    ⟨392924232284573655178783274247689436421, 392924232284573655178783274247689436423⟩,
    ⟨261949488189715770119188849498459624278, 261949488189715770119188849498459624284⟩⟩

def acosNegHalfEnclosure : Interval :=
  ⟨712685722709977831906453582107913855524, 712685722709977831906453582107913855550⟩

theorem pi_verified : Interval.pi 128 32 = some piEnclosure := by decide +kernel

theorem asin_half_verified :
    Jet.asin 128 32 (Jet.var 128 (Interval.rational 128 1 2)) = some asinHalfEnclosure := by
  decide +kernel

theorem acos_neg_half_verified :
    Interval.acos 128 32 (Interval.rational 128 (-1) 2) = some acosNegHalfEnclosure := by
  decide +kernel

theorem pi_enclosed : piEnclosure.Contains 128 Real.pi := Interval.pi_sound pi_verified

theorem asin_half_jet_enclosed :
    asinHalfEnclosure.Contains 128 ((SecondOrder.Jet.var (1 / 2)).asin) := by
  apply Jet.asin_sound asin_half_verified
  apply Jet.contains_var
  simpa only [Int.cast_one, Int.cast_ofNat] using Interval.contains_rational 128 1 2

theorem acos_neg_half_enclosed : acosNegHalfEnclosure.Contains 128 (Real.arccos (-1 / 2)) := by
  apply Interval.acos_sound acos_neg_half_verified
  simpa only [Int.cast_neg, Int.cast_one, Int.cast_ofNat] using Interval.contains_rational 128 (-1) 2

end BlaschkeLebesgue.Certificates.InverseTrigExamples
