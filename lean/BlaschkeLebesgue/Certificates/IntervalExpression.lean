module

public import BlaschkeLebesgue.Certificates.IntervalJet

/-!
# Checked expression evaluation with shared intermediate values

The same expression has a real interpretation, a real jet interpretation,
and executable interval/interval-jet evaluators. `bind` stores an intermediate
value at environment index zero, allowing the certificate formulas to share
subexpressions. Failed domain checks return `none`.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

def pushEnv {α : Type*} (x : α) (env : ℕ → α) : ℕ → α
  | 0 => x
  | n + 1 => env n

inductive Expr where
  | rational (q : ℚ)
  | var (index : ℕ)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | sq (a : Expr)
  | inv (a : Expr)
  | sqrt (a : Expr)
  | bind (value body : Expr)
  deriving DecidableEq, Inhabited

namespace Expr

noncomputable def real (e : Expr) (env : ℕ → ℝ) : ℝ := match e with
  | .rational q => q
  | .var i => env i
  | .neg a => -(real a env)
  | .add a b => real a env + real b env
  | .sub a b => real a env - real b env
  | .mul a b => real a env * real b env
  | .sq a => real a env ^ 2
  | .inv a => (real a env)⁻¹
  | .sqrt a => Real.sqrt (real a env)
  | .bind a b => real b (pushEnv (real a env) env)

noncomputable def realJet (e : Expr) (env : ℕ → SecondOrder.Jet) : SecondOrder.Jet := match e with
  | .rational q => SecondOrder.Jet.const q
  | .var i => env i
  | .neg a => (realJet a env).neg
  | .add a b => (realJet a env).add (realJet b env)
  | .sub a b => (realJet a env).sub (realJet b env)
  | .mul a b => (realJet a env).mul (realJet b env)
  | .sq a => (realJet a env).sq
  | .inv a => (realJet a env).inv
  | .sqrt a => (realJet a env).sqrt
  | .bind a b => realJet b (pushEnv (realJet a env) env)

def interval (p : ℕ) (e : Expr) (env : ℕ → Interval) : Option Interval := match e with
  | .rational q => some (Interval.rational p q.num q.den)
  | .var i => some (env i)
  | .neg a => (interval p a env).map Interval.neg
  | .add a b => (interval p a env).bind fun x ↦ (interval p b env).map (Interval.add x)
  | .sub a b => (interval p a env).bind fun x ↦ (interval p b env).map (Interval.sub x)
  | .mul a b => (interval p a env).bind fun x ↦ (interval p b env).map (Interval.mul p x)
  | .sq a => (interval p a env).map (Interval.sq p)
  | .inv a => (interval p a env).bind fun x ↦ if x.invCheck then some (Interval.inv p x) else none
  | .sqrt a => (interval p a env).bind fun x ↦ if x.sqrtCheck then some (Interval.sqrt p x) else none
  | .bind a b => (interval p a env).bind fun x ↦ interval p b (pushEnv x env)

def jet (p : ℕ) (e : Expr) (env : ℕ → Jet) : Option Jet := match e with
  | .rational q => some (Jet.const p (Interval.rational p q.num q.den))
  | .var i => some (env i)
  | .neg a => (jet p a env).map Jet.neg
  | .add a b => (jet p a env).bind fun x ↦ (jet p b env).map (Jet.add x)
  | .sub a b => (jet p a env).bind fun x ↦ (jet p b env).map (Jet.sub x)
  | .mul a b => (jet p a env).bind fun x ↦ (jet p b env).map (Jet.mul p x)
  | .sq a => (jet p a env).map (Jet.sq p)
  | .inv a => (jet p a env).bind fun x ↦ if x.v.invCheck then some (Jet.inv p x) else none
  | .sqrt a => (jet p a env).bind fun x ↦ if Jet.sqrtCheck p x then some (Jet.sqrt p x) else none
  | .bind a b => (jet p a env).bind fun x ↦ jet p b (pushEnv x env)

theorem realJet_v (e : Expr) (env : ℕ → SecondOrder.Jet) :
    (realJet e env).v = real e (fun i ↦ (env i).v) := by
  induction e generalizing env with
  | rational q => rfl
  | var i => rfl
  | neg a ih => exact congrArg Neg.neg (ih env)
  | add a b iha ihb => exact congrArg₂ HAdd.hAdd (iha env) (ihb env)
  | sub a b iha ihb =>
    change (realJet a env).v + -(realJet b env).v = _
    rw [iha, ihb]
    rfl
  | mul a b iha ihb => exact congrArg₂ HMul.hMul (iha env) (ihb env)
  | sq a ih => exact congrArg (fun x : ℝ ↦ x ^ 2) (ih env)
  | inv a ih => exact congrArg Inv.inv (ih env)
  | sqrt a ih => exact congrArg Real.sqrt (ih env)
  | bind a b iha ihb =>
    dsimp only [realJet, real]
    rw [ihb]
    congr 1
    funext i
    cases i with
    | zero => exact iha env
    | succ i => rfl

theorem interval_sound {p : ℕ} {e : Expr} {env : ℕ → Interval} {xs : ℕ → ℝ} {I : Interval}
    (h : interval p e env = some I) (hx : ∀ i, (env i).Contains p (xs i)) : I.Contains p (real e xs) := by
  induction e generalizing env xs I with
  | rational q =>
    simp only [interval, Option.some.injEq] at h
    subst I
    simpa only [real, Rat.cast_def, Int.cast_natCast] using Interval.contains_rational p q.num q.den
  | var i =>
    simp only [interval, Option.some.injEq] at h
    subst I
    exact hx i
  | neg a ih =>
    simp only [interval, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, rfl⟩ := h
    exact Interval.contains_neg (ih hA hx)
  | add a b iha ihb =>
    simp only [interval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact Interval.contains_add (iha hA hx) (ihb hB hx)
  | sub a b iha ihb =>
    simp only [interval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact Interval.contains_sub (iha hA hx) (ihb hB hx)
  | mul a b iha ihb =>
    simp only [interval, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact Interval.contains_mul (iha hA hx) (ihb hB hx)
  | sq a ih =>
    simp only [interval, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, rfl⟩ := h
    exact Interval.contains_sq (ih hA hx)
  | inv a ih =>
    simp only [interval, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, h⟩ := h
    split_ifs at h with hA0
    · cases h
      exact Interval.contains_inv (ih hA hx) hA0
  | sqrt a ih =>
    simp only [interval, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, h⟩ := h
    split_ifs at h with hA0
    · cases h
      exact Interval.contains_sqrt (ih hA hx) hA0
  | bind a b iha ihb =>
    simp only [interval, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, hB⟩ := h
    apply ihb hB
    intro i
    cases i with
    | zero => exact iha hA hx
    | succ i => exact hx i

theorem jet_sound {p : ℕ} {e : Expr} {env : ℕ → Jet} {xs : ℕ → SecondOrder.Jet} {J : Jet}
    (h : jet p e env = some J) (hx : ∀ i, (env i).Contains p (xs i)) : J.Contains p (realJet e xs) := by
  induction e generalizing env xs J with
  | rational q =>
    simp only [jet, Option.some.injEq] at h
    subst J
    apply Jet.contains_const
    simpa only [Rat.cast_def, Int.cast_natCast] using Interval.contains_rational p q.num q.den
  | var i =>
    simp only [jet, Option.some.injEq] at h
    subst J
    exact hx i
  | neg a ih =>
    simp only [jet, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, rfl⟩ := h
    exact Jet.contains_neg (ih hA hx)
  | add a b iha ihb =>
    simp only [jet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact Jet.contains_add (iha hA hx) (ihb hB hx)
  | sub a b iha ihb =>
    simp only [jet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact Jet.contains_sub (iha hA hx) (ihb hB hx)
  | mul a b iha ihb =>
    simp only [jet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact Jet.contains_mul (iha hA hx) (ihb hB hx)
  | sq a ih =>
    simp only [jet, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, rfl⟩ := h
    exact Jet.contains_sq (ih hA hx)
  | inv a ih =>
    simp only [jet, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, h⟩ := h
    split_ifs at h with hA0
    · cases h
      exact Jet.contains_inv (ih hA hx) hA0
  | sqrt a ih =>
    simp only [jet, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, h⟩ := h
    split_ifs at h with hA0
    · cases h
      exact Jet.contains_sqrt (ih hA hx) hA0
  | bind a b iha ihb =>
    simp only [jet, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, hB⟩ := h
    apply ihb hB
    intro i
    cases i with
    | zero => exact iha hA hx
    | succ i => exact hx i

/-! A successful jet evaluation also supplies the domains needed by the
analytic chain rule. The input jets may themselves depend on the parameter,
so this theorem remains valid when `bind` introduces an intermediate value. -/

theorem jet_validAt {p : ℕ} {e : Expr} {env : ℕ → Jet} {fs : ℕ → ℝ → SecondOrder.Jet}
    {x : ℝ} {J : Jet} (h : jet p e env = some J)
    (hx : ∀ i, (env i).Contains p (fs i x)) (hf : ∀ i, SecondOrder.Jet.ValidAt (fs i) x) :
    SecondOrder.Jet.ValidAt (fun z ↦ realJet e (fun i ↦ fs i z)) x := by
  induction e generalizing env fs J with
  | rational q => exact SecondOrder.Jet.validAt_const q x
  | var i => exact hf i
  | neg a ih =>
    simp only [jet, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, rfl⟩ := h
    exact (ih hA hx hf).neg
  | add a b iha ihb =>
    simp only [jet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact (iha hA hx hf).add (ihb hB hx hf)
  | sub a b iha ihb =>
    simp only [jet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact (iha hA hx hf).sub (ihb hB hx hf)
  | mul a b iha ihb =>
    simp only [jet, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    exact (iha hA hx hf).mul (ihb hB hx hf)
  | sq a ih =>
    simp only [jet, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, rfl⟩ := h
    exact (ih hA hx hf).sq
  | inv a ih =>
    simp only [jet, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, h⟩ := h
    split_ifs at h with hA0
    cases h
    exact (ih hA hx hf).inv (Interval.ne_zero_of_invCheck (jet_sound hA hx).1 hA0)
  | sqrt a ih =>
    simp only [jet, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, h⟩ := h
    split_ifs at h with hA0
    cases h
    simp only [Jet.sqrtCheck, Bool.and_eq_true] at hA0
    exact (ih hA hx hf).sqrt (Interval.pos_of_positiveCheck (jet_sound hA hx).1 hA0.1.1)
  | bind a b iha ihb =>
    simp only [jet, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, hB⟩ := h
    let gs := pushEnv (fun z ↦ realJet a (fun i ↦ fs i z)) fs
    have hgs : ∀ i, (pushEnv A env i).Contains p (gs i x) := by
      intro i
      cases i with
      | zero => exact jet_sound hA hx
      | succ i => exact hx i
    have hvalid : ∀ i, SecondOrder.Jet.ValidAt (gs i) x := by
      intro i
      cases i with
      | zero => exact iha hA hx hf
      | succ i => exact hf i
    have hb := ihb hB hgs hvalid
    convert hb using 1
    funext z
    dsimp only [realJet]
    congr 1
    funext i
    cases i <;> rfl

/-- The derivative bounds returned by the executable evaluator concern the
ordinary real interpretation of the expression. -/
theorem jet_derivatives {p : ℕ} {e : Expr} {env : ℕ → Jet} {fs : ℕ → ℝ → SecondOrder.Jet}
    {x : ℝ} {J : Jet} (h : jet p e env = some J)
    (hx : ∀ i, (env i).Contains p (fs i x)) (hf : ∀ i, SecondOrder.Jet.ValidAt (fs i) x) :
    HasDerivAt (fun z ↦ real e (fun i ↦ (fs i z).v)) (realJet e (fun i ↦ fs i x)).d x ∧
    HasDerivAt (fun z ↦ (realJet e (fun i ↦ fs i z)).d) (realJet e (fun i ↦ fs i x)).dd x ∧
    J.d.Contains p (realJet e (fun i ↦ fs i x)).d ∧
    J.dd.Contains p (realJet e (fun i ↦ fs i x)).dd := by
  have hv := jet_validAt h hx hf
  have hc := jet_sound h hx
  refine ⟨?_, hv.2, hc.2⟩
  simpa only [realJet_v] using hv.1

end Expr
end BlaschkeLebesgue.Certificates.FixedPoint
