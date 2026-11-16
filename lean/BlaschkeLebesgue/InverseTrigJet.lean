module

public import BlaschkeLebesgue.SecondOrderJet
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Exact first and second derivatives of inverse-trigonometric jets -/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.SecondOrder

def Jet.atan (a : Jet) : Jet :=
  a.comp (Real.arctan a.v) (1 / (1 + a.v ^ 2)) (-2 * a.v / (1 + a.v ^ 2) ^ 2)

def Jet.asin (a : Jet) : Jet :=
  a.comp (Real.arcsin a.v) (1 / Real.sqrt (1 - a.v ^ 2))
    (a.v / Real.sqrt (1 - a.v ^ 2) ^ 3)

def Jet.acos (a : Jet) : Jet := (const (Real.pi / 2)).sub a.asin

theorem hasDerivAt_atan_coefficient (x : ℝ) :
    HasDerivAt (fun z : ℝ ↦ 1 / (1 + z ^ 2)) (-2 * x / (1 + x ^ 2) ^ 2) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).fun_div
    (((hasDerivAt_id x).pow 2).const_add 1) (by change 1 + x ^ 2 ≠ 0; positivity)
  convert h using 1 <;> norm_num [Pi.pow_apply, id_eq]

theorem Jet.ValidAt.atan {f : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) :
    ValidAt (fun z ↦ (f z).atan) x :=
  hf.comp (g := Real.arctan) (g' := fun z : ℝ ↦ 1 / (1 + z ^ 2))
    (g'' := fun z : ℝ ↦ -2 * z / (1 + z ^ 2) ^ 2)
    (Real.hasDerivAt_arctan _) (hasDerivAt_atan_coefficient _)

theorem hasDerivAt_asin_coefficient {x : ℝ} (hx : 0 < 1 - x ^ 2) :
    HasDerivAt (fun z : ℝ ↦ 1 / Real.sqrt (1 - z ^ 2))
      (x / Real.sqrt (1 - x ^ 2) ^ 3) x := by
  have hr : Real.sqrt (1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have h := (hasDerivAt_const x (1 : ℝ)).fun_div
    ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt hx.ne') hr
  convert h using 1 <;> norm_num [Pi.pow_apply, id_eq]
  field_simp

theorem Jet.ValidAt.asin {f : ℝ → Jet} {x : ℝ} (hf : ValidAt f x)
    (hx : 0 < 1 - (f x).v ^ 2) : ValidAt (fun z ↦ (f z).asin) x := by
  have hneg : (f x).v ≠ -1 := by intro h; rw [h] at hx; norm_num at hx
  have hpos : (f x).v ≠ 1 := by intro h; rw [h] at hx; norm_num at hx
  exact hf.comp (g := Real.arcsin) (g' := fun z : ℝ ↦ 1 / Real.sqrt (1 - z ^ 2))
    (g'' := fun z : ℝ ↦ z / Real.sqrt (1 - z ^ 2) ^ 3)
    (Real.hasDerivAt_arcsin hneg hpos) (hasDerivAt_asin_coefficient hx)

theorem Jet.ValidAt.acos {f : ℝ → Jet} {x : ℝ} (hf : ValidAt f x)
    (hx : 0 < 1 - (f x).v ^ 2) : ValidAt (fun z ↦ (f z).acos) x :=
  (Jet.validAt_const (Real.pi / 2) x).sub (hf.asin hx)

theorem Jet.acos_v (a : Jet) : a.acos.v = Real.arccos a.v :=
  (Real.arccos_eq_pi_div_two_sub_arcsin _).symm

end BlaschkeLebesgue.SecondOrder
