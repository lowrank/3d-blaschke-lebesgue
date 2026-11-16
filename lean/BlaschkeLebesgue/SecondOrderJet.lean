module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic

/-! # The exact first and second derivative rules used by the certificate jets -/

@[expose] public noncomputable section

namespace BlaschkeLebesgue.SecondOrder

structure Jet where
  v : ℝ
  d : ℝ
  dd : ℝ

def Jet.ValidAt (f : ℝ → Jet) (x : ℝ) : Prop :=
  HasDerivAt (fun z ↦ (f z).v) (f x).d x ∧ HasDerivAt (fun z ↦ (f z).d) (f x).dd x

def Jet.const (c : ℝ) : Jet := ⟨c, 0, 0⟩
def Jet.var (x : ℝ) : Jet := ⟨x, 1, 0⟩
def Jet.neg (a : Jet) : Jet := ⟨-a.v, -a.d, -a.dd⟩
def Jet.add (a b : Jet) : Jet := ⟨a.v + b.v, a.d + b.d, a.dd + b.dd⟩
def Jet.sub (a b : Jet) : Jet := a.add b.neg
def Jet.mul (a b : Jet) : Jet :=
  ⟨a.v * b.v, a.d * b.v + a.v * b.d, a.dd * b.v + 2 * a.d * b.d + a.v * b.dd⟩
def Jet.sq (a : Jet) : Jet := ⟨a.v ^ 2, 2 * a.v * a.d, 2 * (a.d ^ 2 + a.v * a.dd)⟩
def Jet.comp (a : Jet) (v d dd : ℝ) : Jet := ⟨v, d * a.d, dd * a.d ^ 2 + d * a.dd⟩
def Jet.inv (a : Jet) : Jet := a.comp a.v⁻¹ (-(a.v⁻¹) ^ 2) (2 * a.v⁻¹ * (a.v⁻¹) ^ 2)
def Jet.div (a b : Jet) : Jet := a.mul b.inv
def Jet.sqrt (a : Jet) : Jet :=
  a.comp (Real.sqrt a.v) (1 / (2 * Real.sqrt a.v)) (-1 / (4 * (Real.sqrt a.v) ^ 2 * Real.sqrt a.v))

theorem Jet.validAt_const (c x : ℝ) : ValidAt (fun _ ↦ const c) x :=
  ⟨hasDerivAt_const x c, hasDerivAt_const x 0⟩

theorem Jet.validAt_var (x : ℝ) : ValidAt var x := ⟨hasDerivAt_id x, hasDerivAt_const x 1⟩

theorem Jet.ValidAt.neg {f : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) : ValidAt (fun z ↦ (f z).neg) x := by
  constructor
  · convert hf.1.neg using 1 <;> rfl
  · convert hf.2.neg using 1 <;> rfl

theorem Jet.ValidAt.add {f g : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) (hg : ValidAt g x) :
    ValidAt (fun z ↦ (f z).add (g z)) x := by
  constructor
  · convert hf.1.add hg.1 using 1 <;> rfl
  · convert hf.2.add hg.2 using 1 <;> rfl

theorem Jet.ValidAt.sub {f g : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) (hg : ValidAt g x) :
    ValidAt (fun z ↦ (f z).sub (g z)) x := hf.add hg.neg

theorem Jet.ValidAt.mul {f g : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) (hg : ValidAt g x) :
    ValidAt (fun z ↦ (f z).mul (g z)) x := by
  constructor
  · convert hf.1.mul hg.1 using 1 <;> rfl
  · have h := (hf.2.fun_mul hg.1).fun_add (hf.1.fun_mul hg.2)
    convert h using 1
    · rfl
    · dsimp only [Jet.mul]
      ring

theorem Jet.ValidAt.sq {f : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) : ValidAt (fun z ↦ (f z).sq) x := by
  constructor
  · convert hf.1.pow 2 using 1
    · rfl
    · dsimp only [Jet.sq]
      norm_num
  · have h := (hf.1.const_mul 2).fun_mul hf.2
    convert h using 1
    · rfl
    · dsimp only [Jet.sq]
      ring

theorem Jet.ValidAt.comp {f : ℝ → Jet} {g g' g'' : ℝ → ℝ} {x : ℝ}
    (hf : ValidAt f x) (hg : HasDerivAt g (g' (f x).v) (f x).v)
    (hg' : HasDerivAt g' (g'' (f x).v) (f x).v) :
    ValidAt (fun z ↦ (f z).comp (g (f z).v) (g' (f z).v) (g'' (f z).v)) x := by
  constructor
  · convert hg.comp x hf.1 using 1 <;> rfl
  · have h := (hg'.comp x hf.1).fun_mul hf.2
    convert h using 1
    · rfl
    · dsimp only [Jet.comp, Function.comp_apply]
      ring

theorem hasDerivAt_inv_coefficient {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun z : ℝ ↦ -(z⁻¹) ^ 2) (2 * x⁻¹ * (x⁻¹) ^ 2) x := by
  have h := ((hasDerivAt_inv hx).pow 2).neg
  convert h using 1
  norm_num [inv_pow]

theorem Jet.ValidAt.inv {f : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) (hx : (f x).v ≠ 0) :
    ValidAt (fun z ↦ (f z).inv) x := by
  have h1 : HasDerivAt (fun z : ℝ ↦ z⁻¹) (-((f x).v⁻¹) ^ 2) (f x).v := by
    simpa only [inv_pow] using hasDerivAt_inv hx
  exact hf.comp (g := fun z : ℝ ↦ z⁻¹) (g' := fun z : ℝ ↦ -(z⁻¹) ^ 2)
    (g'' := fun z : ℝ ↦ 2 * z⁻¹ * (z⁻¹) ^ 2) h1 (hasDerivAt_inv_coefficient hx)

theorem Jet.ValidAt.div {f g : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) (hg : ValidAt g x)
    (hx : (g x).v ≠ 0) : ValidAt (fun z ↦ (f z).div (g z)) x := hf.mul (hg.inv hx)

theorem hasDerivAt_sqrt_coefficient {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℝ ↦ 1 / (2 * Real.sqrt z))
      (-1 / (4 * (Real.sqrt x) ^ 2 * Real.sqrt x)) x := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have h := (hasDerivAt_const x (1 : ℝ)).fun_div ((Real.hasDerivAt_sqrt hx.ne').const_mul 2)
    (mul_ne_zero (by norm_num) hs)
  convert h using 1
  field_simp
  norm_num

theorem Jet.ValidAt.sqrt {f : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) (hx : 0 < (f x).v) :
    ValidAt (fun z ↦ (f z).sqrt) x :=
  hf.comp (g := Real.sqrt) (g' := fun z : ℝ ↦ 1 / (2 * Real.sqrt z))
    (g'' := fun z : ℝ ↦ -1 / (4 * Real.sqrt z ^ 2 * Real.sqrt z))
    (Real.hasDerivAt_sqrt hx.ne') (hasDerivAt_sqrt_coefficient hx)

end BlaschkeLebesgue.SecondOrder
