module

public import BlaschkeLebesgue.Certificates.InverseTrigInterval
public import BlaschkeLebesgue.Certificates.IntervalJet
public import BlaschkeLebesgue.InverseTrigJet

/-! # Sound enclosures for inverse-trigonometric values and two derivatives -/

public section

namespace BlaschkeLebesgue.Certificates.FixedPoint.Jet

theorem atan_sound {p n : ℕ} {a b : Jet} {x : SecondOrder.Jet}
    (h : atan p n a = some b) (hx : a.Contains p x) : b.Contains p x.atan := by
  simp only [atan, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  split_ifs at h with hw
  cases h
  have h1 : (Interval.integer p 1).Contains p (1 : ℝ) := by
    exact_mod_cast Interval.contains_integer p 1
  have hn : (Interval.integer p (-2)).Contains p (-2 : ℝ) := by
    exact_mod_cast Interval.contains_integer p (-2)
  have hW := Interval.contains_add h1 (Interval.contains_sq hx.1)
  have hD := Interval.contains_inv hW hw
  have hDD := Interval.contains_mul (Interval.contains_mul hn hx.1) (Interval.contains_sq hD)
  have hder : (Interval.inv p ((Interval.integer p 1).add (Interval.sq p a.v))).Contains p
      (1 / (1 + x.v ^ 2)) := by simpa only [one_div] using hD
  apply contains_comp hx (Interval.checkedAtan_sound hv hx.1) hder
  simpa only [div_eq_mul_inv, inv_pow] using hDD

theorem asin_domain {p n : ℕ} {a b : Jet} {x : SecondOrder.Jet}
    (h : asin p n a = some b) (hx : a.Contains p x) : 0 < 1 - x.v ^ 2 := by
  simp only [asin, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  split_ifs at h with hq
  simp only [Bool.and_eq_true] at hq
  have h1 : (Interval.integer p 1).Contains p (1 : ℝ) := by
    exact_mod_cast Interval.contains_integer p 1
  exact Interval.pos_of_positiveCheck (Interval.contains_sub h1 (Interval.contains_sq hx.1)) hq.1

theorem asin_sound {p n : ℕ} {a b : Jet} {x : SecondOrder.Jet}
    (h : asin p n a = some b) (hx : a.Contains p x) : b.Contains p x.asin := by
  simp only [asin, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  split_ifs at h with hq
  cases h
  simp only [Bool.and_eq_true] at hq
  have h1 : (Interval.integer p 1).Contains p (1 : ℝ) := by
    exact_mod_cast Interval.contains_integer p 1
  have hQ := Interval.contains_sub h1 (Interval.contains_sq hx.1)
  have hs : (Interval.sub (Interval.integer p 1) (Interval.sq p a.v)).sqrtCheck = true := by
    simpa only [Interval.sqrtCheck, decide_eq_true_eq] using
      (show 0 ≤ (Interval.sub (Interval.integer p 1) (Interval.sq p a.v)).lo from
        (of_decide_eq_true hq.1).le)
  have hR := Interval.contains_sqrt hQ hs
  have hD := Interval.contains_inv hR hq.2
  have hDD := Interval.contains_mul hx.1 (Interval.contains_mul hD (Interval.contains_sq hD))
  apply contains_comp hx (Interval.asin_sound hv hx.1) (by simpa only [one_div] using hD)
  convert hDD using 1
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem acos_domain {p n : ℕ} {a b : Jet} {x : SecondOrder.Jet}
    (h : acos p n a = some b) (hx : a.Contains p x) : 0 < 1 - x.v ^ 2 := by
  simp only [acos, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨P, hP, v, hv, rfl⟩ := h
  exact asin_domain hv hx

theorem acos_sound {p n : ℕ} {a b : Jet} {x : SecondOrder.Jet}
    (h : acos p n a = some b) (hx : a.Contains p x) : b.Contains p x.acos := by
  simp only [acos, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨P, hP, v, hv, rfl⟩ := h
  have hhalf : (Interval.rational p 1 2).Contains p (1 / 2 : ℝ) := by
    simpa only [Int.cast_one, Int.cast_ofNat] using Interval.contains_rational p 1 2
  have hpi := Interval.contains_mul hhalf (Interval.pi_sound hP)
  rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring] at hpi
  exact contains_sub (contains_const hpi) (asin_sound hv hx)

end BlaschkeLebesgue.Certificates.FixedPoint.Jet
