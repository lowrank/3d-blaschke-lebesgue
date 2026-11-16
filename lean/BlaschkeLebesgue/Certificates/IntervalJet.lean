module

public import BlaschkeLebesgue.Certificates.FixedInterval
public import BlaschkeLebesgue.SecondOrderJet

/-!
# Interval enclosures for a value and two derivatives

Each jet tracks one derivative direction. Independent directions can use the
same value enclosure with separate jets; no mixed derivative is needed by the
quadrature theorem. The interval and real jet formulas agree operation by
operation, and the domain checks justify every reciprocal and square root.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

namespace Jet

def Contains (a : Jet) (p : ℕ) (x : SecondOrder.Jet) : Prop :=
  a.v.Contains p x.v ∧ a.d.Contains p x.d ∧ a.dd.Contains p x.dd

theorem contains_const {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) :
    (const p I).Contains p (SecondOrder.Jet.const x) := by
  have h0 : (Interval.integer p 0).Contains p (0 : ℝ) := by simpa only [Int.cast_zero] using Interval.contains_integer p 0
  exact ⟨hx, h0, h0⟩

theorem contains_var {I : Interval} {p : ℕ} {x : ℝ} (hx : I.Contains p x) :
    (var p I).Contains p (SecondOrder.Jet.var x) := by
  have h0 : (Interval.integer p 0).Contains p (0 : ℝ) := by simpa only [Int.cast_zero] using Interval.contains_integer p 0
  have h1 : (Interval.integer p 1).Contains p (1 : ℝ) := by simpa only [Int.cast_one] using Interval.contains_integer p 1
  exact ⟨hx, h1, h0⟩

theorem contains_neg {a : Jet} {p : ℕ} {x : SecondOrder.Jet} (hx : a.Contains p x) :
    a.neg.Contains p x.neg := ⟨Interval.contains_neg hx.1, Interval.contains_neg hx.2.1, Interval.contains_neg hx.2.2⟩

theorem contains_add {a b : Jet} {p : ℕ} {x y : SecondOrder.Jet} (hx : a.Contains p x) (hy : b.Contains p y) :
    (a.add b).Contains p (x.add y) :=
  ⟨Interval.contains_add hx.1 hy.1, Interval.contains_add hx.2.1 hy.2.1, Interval.contains_add hx.2.2 hy.2.2⟩

theorem contains_sub {a b : Jet} {p : ℕ} {x y : SecondOrder.Jet} (hx : a.Contains p x) (hy : b.Contains p y) :
    (a.sub b).Contains p (x.sub y) := contains_add hx (contains_neg hy)

theorem contains_mul {a b : Jet} {p : ℕ} {x y : SecondOrder.Jet} (hx : a.Contains p x) (hy : b.Contains p y) :
    (mul p a b).Contains p (x.mul y) := by
  have h2 : (Interval.integer p 2).Contains p (2 : ℝ) := by simpa only [Int.cast_ofNat] using Interval.contains_integer p 2
  exact ⟨Interval.contains_mul hx.1 hy.1,
    Interval.contains_add (Interval.contains_mul hx.2.1 hy.1) (Interval.contains_mul hx.1 hy.2.1),
    Interval.contains_add (Interval.contains_add (Interval.contains_mul hx.2.2 hy.1)
      (Interval.contains_mul (Interval.contains_mul h2 hx.2.1) hy.2.1)) (Interval.contains_mul hx.1 hy.2.2)⟩

theorem contains_sq {a : Jet} {p : ℕ} {x : SecondOrder.Jet} (hx : a.Contains p x) :
    (sq p a).Contains p x.sq := by
  have h2 : (Interval.integer p 2).Contains p (2 : ℝ) := by simpa only [Int.cast_ofNat] using Interval.contains_integer p 2
  exact ⟨Interval.contains_sq hx.1, Interval.contains_mul (Interval.contains_mul h2 hx.1) hx.2.1,
    Interval.contains_mul h2 (Interval.contains_add (Interval.contains_sq hx.2.1) (Interval.contains_mul hx.1 hx.2.2))⟩

theorem contains_comp {a : Jet} {v d dd : Interval} {p : ℕ} {x : SecondOrder.Jet} {fv fd fdd : ℝ}
    (hx : a.Contains p x) (hv : v.Contains p fv) (hd : d.Contains p fd) (hdd : dd.Contains p fdd) :
    (comp p a v d dd).Contains p (x.comp fv fd fdd) :=
  ⟨hv, Interval.contains_mul hd hx.2.1,
    Interval.contains_add (Interval.contains_mul hdd (Interval.contains_sq hx.2.1)) (Interval.contains_mul hd hx.2.2)⟩

theorem contains_inv {a : Jet} {p : ℕ} {x : SecondOrder.Jet} (hx : a.Contains p x) (ha : a.v.invCheck = true) :
    (inv p a).Contains p x.inv := by
  have hv := Interval.contains_inv hx.1 ha
  have h2 : (Interval.integer p 2).Contains p (2 : ℝ) := by simpa only [Int.cast_ofNat] using Interval.contains_integer p 2
  exact contains_comp hx hv (Interval.contains_neg (Interval.contains_sq hv))
    (Interval.contains_mul (Interval.contains_mul h2 hv) (Interval.contains_sq hv))

theorem contains_div {a b : Jet} {p : ℕ} {x y : SecondOrder.Jet} (hx : a.Contains p x) (hy : b.Contains p y)
    (hb : b.v.invCheck = true) : (div p a b).Contains p (x.div y) := contains_mul hx (contains_inv hy hb)

theorem contains_sqrt {a : Jet} {p : ℕ} {x : SecondOrder.Jet} (hx : a.Contains p x) (ha : sqrtCheck p a = true) :
    (sqrt p a).Contains p x.sqrt := by
  simp only [sqrtCheck, Bool.and_eq_true] at ha
  have hpos : 0 < a.v.lo := of_decide_eq_true ha.1.1
  have hs : a.v.sqrtCheck = true := by simp only [Interval.sqrtCheck, decide_eq_true_eq]; exact hpos.le
  have hv := Interval.contains_sqrt hx.1 hs
  have h1 : (Interval.integer p 1).Contains p (1 : ℝ) := by simpa only [Int.cast_one] using Interval.contains_integer p 1
  have hn : (Interval.integer p (-1)).Contains p (-1 : ℝ) := by simpa only [Int.cast_neg, Int.cast_one] using Interval.contains_integer p (-1)
  have h2 : (Interval.integer p 2).Contains p (2 : ℝ) := by simpa only [Int.cast_ofNat] using Interval.contains_integer p 2
  have h4 : (Interval.integer p 4).Contains p (4 : ℝ) := by simpa only [Int.cast_ofNat] using Interval.contains_integer p 4
  exact contains_comp hx hv (Interval.contains_div h1 (Interval.contains_mul h2 hv) ha.1.2)
    (Interval.contains_div hn (Interval.contains_mul (Interval.contains_mul h4 (Interval.contains_sq hv)) hv) ha.2)

end Jet
end BlaschkeLebesgue.Certificates.FixedPoint
