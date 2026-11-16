module

public import BlaschkeLebesgue.Certificates.IntervalExpression

/-!
# Shared expression programs

A program evaluates each expression once and stores its result at index zero.
Returning the environment permits several outputs to share intermediates.
The containment and derivative theorems apply to every output index.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

namespace Program

noncomputable def real : Program → (ℕ → ℝ) → ℕ → ℝ
  | [], env => env
  | e :: es, env => real es (pushEnv (e.real env) env)

noncomputable def realJet : Program → (ℕ → SecondOrder.Jet) → ℕ → SecondOrder.Jet
  | [], env => env
  | e :: es, env => realJet es (pushEnv (e.realJet env) env)

theorem realJet_v (es : Program) (env : ℕ → SecondOrder.Jet) (i : ℕ) :
    (realJet es env i).v = real es (fun j ↦ (env j).v) i := by
  induction es generalizing env with
  | nil => rfl
  | cons e es ih =>
    dsimp only [realJet, real]
    rw [ih]
    congr 1
    funext j
    cases j with
    | zero => exact Expr.realJet_v e env
    | succ j => rfl

theorem interval_sound {p : ℕ} {es : Program} {env out : ℕ → Interval} {xs : ℕ → ℝ}
    (h : interval p es env = some out) (hx : ∀ i, (env i).Contains p (xs i)) :
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
    | zero => exact Expr.interval_sound hA hx
    | succ i => exact hx i

theorem jet_sound {p : ℕ} {es : Program} {env out : ℕ → Jet} {xs : ℕ → SecondOrder.Jet}
    (h : jet p es env = some out) (hx : ∀ i, (env i).Contains p (xs i)) :
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
    | zero => exact Expr.jet_sound hA hx
    | succ i => exact hx i

theorem jet_validAt {p : ℕ} {es : Program} {env out : ℕ → Jet}
    {fs : ℕ → ℝ → SecondOrder.Jet} {x : ℝ} (h : jet p es env = some out)
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
      | zero => exact Expr.jet_sound hA hx
      | succ i => exact hx i
    have hvalid : ∀ i, SecondOrder.Jet.ValidAt (gs i) x := by
      intro i
      cases i with
      | zero => exact Expr.jet_validAt hA hx hf
      | succ i => exact hf i
    intro i
    have hb := ih hB hgs hvalid i
    convert hb using 1
    funext z
    dsimp only [realJet]
    congr 1
    funext j
    cases j <;> rfl

theorem jet_derivatives {p : ℕ} {es : Program} {env out : ℕ → Jet}
    {fs : ℕ → ℝ → SecondOrder.Jet} {x : ℝ} (h : jet p es env = some out)
    (hx : ∀ i, (env i).Contains p (fs i x)) (hf : ∀ i, SecondOrder.Jet.ValidAt (fs i) x) (i : ℕ) :
    HasDerivAt (fun z ↦ real es (fun j ↦ (fs j z).v) i) (realJet es (fun j ↦ fs j x) i).d x ∧
    HasDerivAt (fun z ↦ (realJet es (fun j ↦ fs j z) i).d) (realJet es (fun j ↦ fs j x) i).dd x ∧
    (out i).d.Contains p (realJet es (fun j ↦ fs j x) i).d ∧
    (out i).dd.Contains p (realJet es (fun j ↦ fs j x) i).dd := by
  have hv := jet_validAt h hx hf i
  have hc := jet_sound h hx i
  refine ⟨?_, hv.2, hc.2⟩
  simpa only [realJet_v] using hv.1

end Program
end BlaschkeLebesgue.Certificates.FixedPoint
