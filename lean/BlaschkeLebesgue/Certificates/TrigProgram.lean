module

public import BlaschkeLebesgue.Certificates.TrigProgramComputation
public import BlaschkeLebesgue.Certificates.IntervalProgram
public import BlaschkeLebesgue.Certificates.InverseTrigIntervalJet

/-! # Sound values and derivatives of inverse-trigonometric programs -/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

namespace TrigOp

noncomputable def real (e : TrigOp) (env : ℕ → ℝ) : ℝ := match e with
  | .algebra a => a.real env
  | .pi => Real.pi
  | .atan i => Real.arctan (env i)
  | .asin i => Real.arcsin (env i)
  | .acos i => Real.arccos (env i)

noncomputable def realJet (e : TrigOp) (env : ℕ → SecondOrder.Jet) : SecondOrder.Jet := match e with
  | .algebra a => a.realJet env
  | .pi => SecondOrder.Jet.const Real.pi
  | .atan i => (env i).atan
  | .asin i => (env i).asin
  | .acos i => (env i).acos

theorem realJet_v (e : TrigOp) (env : ℕ → SecondOrder.Jet) :
    (realJet e env).v = real e (fun i ↦ (env i).v) := by
  cases e with
  | algebra a => exact Expr.realJet_v a env
  | pi => rfl
  | atan i => rfl
  | asin i => rfl
  | acos i => exact SecondOrder.Jet.acos_v _

theorem interval_sound {p n : ℕ} {e : TrigOp} {env : ℕ → Interval} {xs : ℕ → ℝ} {I : Interval}
    (h : interval p n e env = some I) (hx : ∀ i, (env i).Contains p (xs i)) :
    I.Contains p (real e xs) := by
  cases e with
  | algebra a => exact Expr.interval_sound h hx
  | pi => exact Interval.pi_sound h
  | atan i => exact Interval.checkedAtan_sound h (hx i)
  | asin i => exact Interval.asin_sound h (hx i)
  | acos i => exact Interval.acos_sound h (hx i)

theorem jet_sound {p n : ℕ} {e : TrigOp} {env : ℕ → Jet} {xs : ℕ → SecondOrder.Jet} {J : Jet}
    (h : jet p n e env = some J) (hx : ∀ i, (env i).Contains p (xs i)) :
    J.Contains p (realJet e xs) := by
  cases e with
  | algebra a => exact Expr.jet_sound h hx
  | pi =>
    simp only [jet, Option.map_eq_some_iff] at h
    obtain ⟨P, hP, rfl⟩ := h
    exact Jet.contains_const (Interval.pi_sound hP)
  | atan i => exact Jet.atan_sound h (hx i)
  | asin i => exact Jet.asin_sound h (hx i)
  | acos i => exact Jet.acos_sound h (hx i)

theorem jet_validAt {p n : ℕ} {e : TrigOp} {env : ℕ → Jet}
    {fs : ℕ → ℝ → SecondOrder.Jet} {x : ℝ} {J : Jet} (h : jet p n e env = some J)
    (hx : ∀ i, (env i).Contains p (fs i x)) (hf : ∀ i, SecondOrder.Jet.ValidAt (fs i) x) :
    SecondOrder.Jet.ValidAt (fun z ↦ realJet e (fun i ↦ fs i z)) x := by
  cases e with
  | algebra a => exact Expr.jet_validAt h hx hf
  | pi => exact SecondOrder.Jet.validAt_const _ _
  | atan i => exact (hf i).atan
  | asin i => exact (hf i).asin (Jet.asin_domain h (hx i))
  | acos i => exact (hf i).acos (Jet.acos_domain h (hx i))

end TrigOp

namespace TrigProgram

noncomputable def real : TrigProgram → (ℕ → ℝ) → ℕ → ℝ
  | [], env => env
  | e :: es, env => real es (pushEnv (e.real env) env)

noncomputable def realJet : TrigProgram → (ℕ → SecondOrder.Jet) → ℕ → SecondOrder.Jet
  | [], env => env
  | e :: es, env => realJet es (pushEnv (e.realJet env) env)

theorem realJet_v (es : TrigProgram) (env : ℕ → SecondOrder.Jet) (i : ℕ) :
    (realJet es env i).v = real es (fun j ↦ (env j).v) i := by
  induction es generalizing env with
  | nil => rfl
  | cons e es ih =>
    dsimp only [realJet, real]
    rw [ih]
    congr 1
    funext j
    cases j with
    | zero => exact TrigOp.realJet_v e env
    | succ j => rfl

theorem interval_sound {p n : ℕ} {es : TrigProgram} {env out : ℕ → Interval} {xs : ℕ → ℝ}
    (h : interval p n es env = some out) (hx : ∀ i, (env i).Contains p (xs i)) :
    ∀ i, (out i).Contains p (real es xs i) := by
  induction es generalizing env xs with
  | nil =>
    simp only [interval, Option.some.injEq] at h
    subst out
    exact hx
  | cons e es ih =>
    simp only [interval, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, hB⟩ := h
    apply ih hB
    intro i
    cases i with
    | zero => exact TrigOp.interval_sound hA hx
    | succ i => exact hx i

theorem jet_sound {p n : ℕ} {es : TrigProgram} {env out : ℕ → Jet} {xs : ℕ → SecondOrder.Jet}
    (h : jet p n es env = some out) (hx : ∀ i, (env i).Contains p (xs i)) :
    ∀ i, (out i).Contains p (realJet es xs i) := by
  induction es generalizing env xs with
  | nil =>
    simp only [jet, Option.some.injEq] at h
    subst out
    exact hx
  | cons e es ih =>
    simp only [jet, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, hB⟩ := h
    apply ih hB
    intro i
    cases i with
    | zero => exact TrigOp.jet_sound hA hx
    | succ i => exact hx i

theorem jet_validAt {p n : ℕ} {es : TrigProgram} {env out : ℕ → Jet}
    {fs : ℕ → ℝ → SecondOrder.Jet} {x : ℝ} (h : jet p n es env = some out)
    (hx : ∀ i, (env i).Contains p (fs i x)) (hf : ∀ i, SecondOrder.Jet.ValidAt (fs i) x) :
    ∀ i, SecondOrder.Jet.ValidAt (fun z ↦ realJet es (fun j ↦ fs j z) i) x := by
  induction es generalizing env fs with
  | nil => exact hf
  | cons e es ih =>
    simp only [jet, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA, hB⟩ := h
    let gs := pushEnv (fun z ↦ e.realJet (fun i ↦ fs i z)) fs
    have hgs : ∀ i, (pushEnv A env i).Contains p (gs i x) := by
      intro i
      cases i with
      | zero => exact TrigOp.jet_sound hA hx
      | succ i => exact hx i
    have hvalid : ∀ i, SecondOrder.Jet.ValidAt (gs i) x := by
      intro i
      cases i with
      | zero => exact TrigOp.jet_validAt hA hx hf
      | succ i => exact hf i
    intro i
    have hb := ih hB hgs hvalid i
    convert hb using 1
    funext z
    dsimp only [realJet]
    congr 1
    funext j
    cases j <;> rfl

theorem jet_derivatives {p n : ℕ} {es : TrigProgram} {env out : ℕ → Jet}
    {fs : ℕ → ℝ → SecondOrder.Jet} {x : ℝ} (h : jet p n es env = some out)
    (hx : ∀ i, (env i).Contains p (fs i x)) (hf : ∀ i, SecondOrder.Jet.ValidAt (fs i) x) (i : ℕ) :
    HasDerivAt (fun z ↦ real es (fun j ↦ (fs j z).v) i) (realJet es (fun j ↦ fs j x) i).d x ∧
    HasDerivAt (fun z ↦ (realJet es (fun j ↦ fs j z) i).d) (realJet es (fun j ↦ fs j x) i).dd x ∧
    (out i).d.Contains p (realJet es (fun j ↦ fs j x) i).d ∧
    (out i).dd.Contains p (realJet es (fun j ↦ fs j x) i).dd := by
  have hv := jet_validAt h hx hf i
  have hc := jet_sound h hx i
  refine ⟨?_, hv.2, hc.2⟩
  simpa only [realJet_v] using hv.1

end TrigProgram

end BlaschkeLebesgue.Certificates.FixedPoint
