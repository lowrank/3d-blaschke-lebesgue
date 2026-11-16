module

public import BlaschkeLebesgue.Certificates.IntervalProgram
public import BlaschkeLebesgue.CompletionFixedSquare

/-!
# The completion certificate as checked expression programs

The parameter program is evaluated once per parameter box. The integrand
program reuses its parameters on each quadrature cell and shares the
intermediates needed by the gap, determinant lower bound, and smooth density.
The real interpretations below are identified with the analytic definitions.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.ProjectiveExpressions

open FixedPoint

attribute [local instance] exprAdd exprSub exprMul exprDiv exprNat

@[simp] theorem real_add (a b : Expr) (env : ℕ → ℝ) :
    (a + b).real env = a.real env + b.real env := rfl
@[simp] theorem real_sub (a b : Expr) (env : ℕ → ℝ) :
    (a - b).real env = a.real env - b.real env := rfl
@[simp] theorem real_mul (a b : Expr) (env : ℕ → ℝ) :
    (a * b).real env = a.real env * b.real env := rfl
@[simp] theorem real_div (a b : Expr) (env : ℕ → ℝ) :
    (a / b).real env = a.real env / b.real env := by
  simp only [div_eq_mul_inv]
  rfl
@[simp] theorem real_numeral (n : ℕ) (env : ℕ → ℝ) :
    Expr.real (OfNat.ofNat n) env = (n : ℝ) := by
  change ((n : ℚ) : ℝ) = (n : ℝ)
  exact Rat.cast_natCast n

noncomputable def realParams (a b : ℝ) : Params ℝ :=
  ⟨Completion.edgeRadius a, Completion.separationUpper a b,
    Completion.obliquity a b, Completion.rectangleRadius a b⟩

noncomputable def realValues (a b s t : ℝ) : Values ℝ :=
  ⟨Completion.squareGap a b s t, Completion.squareDetLower a b s t,
    Completion.unitSquareSmoothDensity a b s t⟩

theorem parameterProgram_real (a b : ℝ) :
    paramsOut (Program.real parameterProgram (parameterEnv a b)) = realParams a b := by
  apply Params.ext <;>
    norm_num [paramsOut, Program.real, parameterProgram, Expr.real, X, C, sq, rt,
      parameterEnv, pushEnv, realParams, Completion.edgeRadius, Completion.separationUpper,
      Completion.obliquity, Completion.rectangleRadius, Completion.arcSin, Completion.arcCos,
      Completion.midpointError, sub_add_eq_sub_sub, div_eq_mul_inv]

theorem integrandProgram_real (a b s t : ℝ) :
    valuesOut (Program.real integrandProgram (integrandEnv (realParams a b) s t)) =
      realValues a b s t := by
  apply Values.ext <;>
    norm_num [valuesOut, Program.real, integrandProgram, Expr.real, X, C, sq, rt,
      integrandEnv, pushEnv, realParams, realValues, Completion.squareGap,
      Completion.squareDetLower, Completion.unitSquareSmoothDensity, Completion.squareW,
      Completion.uniformW, Completion.averagedW, Completion.q, Completion.edgeRadius, div_eq_mul_inv]

def Params.Rel {α β : Type*} (R : α → β → Prop) (a : Params α) (b : Params β) : Prop :=
  R a.ra b.ra ∧ R a.w b.w ∧ R a.c b.c ∧ R a.T b.T

def Values.Rel {α β : Type*} (R : α → β → Prop) (a : Values α) (b : Values β) : Prop :=
  R a.G b.G ∧ R a.D b.D ∧ R a.V b.V

theorem parameterEnv_rel {α β : Type*} {R : α → β → Prop} {a b : α} {x y : β}
    (ha : R a x) (hb : R b y) : ∀ i, R (parameterEnv a b i) (parameterEnv x y i) := by
  intro i
  cases i with
  | zero => exact ha
  | succ i => exact hb

theorem integrandEnv_rel {α β : Type*} {R : α → β → Prop} {a : Params α} {b : Params β}
    {s t : α} {x y : β} (hab : a.Rel R b) (hs : R s x) (ht : R t y) :
    ∀ i, R (integrandEnv a s t i) (integrandEnv b x y i) := by
  intro i
  rcases i with _ | _ | _ | _ | _ | i
  · exact hab.1
  · exact hab.2.1
  · exact hab.2.2.1
  · exact hab.2.2.2
  · exact hs
  · exact ht

theorem paramsOut_rel {α β : Type*} {R : α → β → Prop} {a : ℕ → α} {b : ℕ → β}
    (h : ∀ i, R (a i) (b i)) : (paramsOut a).Rel R (paramsOut b) := ⟨h 1, h 0, h 7, h 2⟩

theorem valuesOut_rel {α β : Type*} {R : α → β → Prop} {a : ℕ → α} {b : ℕ → β}
    (h : ∀ i, R (a i) (b i)) : (valuesOut a).Rel R (valuesOut b) := ⟨h 3, h 2, h 0⟩

theorem paramsInterval_sound {p : ℕ} {a b : Interval} {out : Params Interval} {x y : ℝ}
    (h : paramsInterval p a b = some out) (ha : a.Contains p x) (hb : b.Contains p y) :
    out.Rel (fun I z ↦ I.Contains p z) (realParams x y) := by
  simp only [paramsInterval, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  have hr := paramsOut_rel (R := fun (I : Interval) z ↦ I.Contains p z)
    (Program.interval_sound he (parameterEnv_rel (R := fun (I : Interval) z ↦ I.Contains p z) ha hb))
  rwa [parameterProgram_real] at hr

theorem valuesInterval_sound {p : ℕ} {par : Params Interval} {s t : Interval} {out : Values Interval}
    {a b x y : ℝ} (h : valuesInterval p par s t = some out)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (hs : s.Contains p x) (ht : t.Contains p y) :
    out.Rel (fun I z ↦ I.Contains p z) (realValues a b x y) := by
  simp only [valuesInterval, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  have hr := valuesOut_rel (R := fun (I : Interval) z ↦ I.Contains p z)
    (Program.interval_sound he (integrandEnv_rel hp hs ht))
  rwa [integrandProgram_real] at hr

noncomputable def paramsRealJet (a b : SecondOrder.Jet) : Params SecondOrder.Jet :=
  paramsOut (Program.realJet parameterProgram (parameterEnv a b))

noncomputable def valuesRealJet (par : Params SecondOrder.Jet) (s t : SecondOrder.Jet) : Values SecondOrder.Jet :=
  valuesOut (Program.realJet integrandProgram (integrandEnv par s t))

theorem paramsJet_sound {p : ℕ} {a b : Jet} {out : Params Jet} {x y : SecondOrder.Jet}
    (h : paramsJet p a b = some out) (ha : a.Contains p x) (hb : b.Contains p y) :
    out.Rel (fun I z ↦ I.Contains p z) (paramsRealJet x y) := by
  simp only [paramsJet, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  exact paramsOut_rel (Program.jet_sound he (parameterEnv_rel (R := fun (I : Jet) z ↦ I.Contains p z) ha hb))

theorem valuesJet_sound {p : ℕ} {par : Params Jet} {s t : Jet} {out : Values Jet}
    {P : Params SecondOrder.Jet} {x y : SecondOrder.Jet}
    (h : valuesJet p par s t = some out) (hp : par.Rel (fun I z ↦ I.Contains p z) P)
    (hs : s.Contains p x) (ht : t.Contains p y) :
    out.Rel (fun I z ↦ I.Contains p z) (valuesRealJet P x y) := by
  simp only [valuesJet, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  exact valuesOut_rel (Program.jet_sound he (integrandEnv_rel hp hs ht))

theorem paramsRealJet_v (a b : SecondOrder.Jet) :
    (paramsRealJet a b).map SecondOrder.Jet.v = realParams a.v b.v := by
  rw [← parameterProgram_real]
  have he : (fun i ↦ (parameterEnv a b i).v) = parameterEnv a.v b.v := by
    funext i
    cases i <;> rfl
  apply Params.ext <;>
    dsimp only [paramsRealJet, Params.map, paramsOut] <;>
    rw [Program.realJet_v, he]

theorem valuesRealJet_v {par : Params SecondOrder.Jet} {a b : ℝ}
    (hp : par.map SecondOrder.Jet.v = realParams a b) (s t : SecondOrder.Jet) :
    (valuesRealJet par s t).map SecondOrder.Jet.v = realValues a b s.v t.v := by
  rw [← integrandProgram_real, ← hp]
  have he : (fun i ↦ (integrandEnv par s t i).v) = integrandEnv (par.map SecondOrder.Jet.v) s.v t.v := by
    funext i
    rcases i with _ | _ | _ | _ | _ | i <;> rfl
  apply Values.ext <;>
    dsimp only [valuesRealJet, Values.map, valuesOut] <;>
    rw [Program.realJet_v, he]

end BlaschkeLebesgue.Certificates.ProjectiveExpressions
