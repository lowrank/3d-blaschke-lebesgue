module

public import BlaschkeLebesgue.Certificates.ClippedHullComputation
public import BlaschkeLebesgue.Certificates.TrigProgram
public import BlaschkeLebesgue.ClippedVolumeDerivatives

/-! # The clipped-hull programs compute the proved scalar formulas -/

@[expose] public section

set_option maxHeartbeats 2000000

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint
open ClippedDifferential

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

noncomputable def realDerivatives (R x : ℝ) : Derivatives ℝ :=
  ⟨outerDx R x, innerDx R x, combinedDx R x⟩

noncomputable def realVolumes (R x : ℝ) : Volumes ℝ :=
  ⟨outer R x, inner R x, (47 * inner R x - outer R x) / 46,
    (47 * ClippedFormula.innerBase R - ClippedFormula.outerBase R) / 46 +
      6 * ((47 * inner R x - outer R x) / 46)⟩

theorem dxProgram_real (R x : ℝ) :
    dxOut (TrigProgram.real dxProgram (inputEnv R x)) = realDerivatives R x := by
  apply Derivatives.ext <;>
    norm_num [dxOut, dxProgram, baseProgram, dxTail, TrigProgram.real, TrigOp.real, Expr.real,
      inputEnv, pushEnv, realDerivatives, outerDx, innerDx, combinedDx, s, r, m, q, k,
      phi, theta, ClippingCircle.radius, ClippedEdge.normalAngle, div_eq_mul_inv] <;>
    (apply Or.inl; ring)

theorem volumeProgram_real (R x : ℝ) :
    volumeOut (TrigProgram.real volumeProgram (inputEnv R x)) = realVolumes R x := by
  apply Volumes.ext <;>
    norm_num [volumeOut, volumeProgram, baseProgram, volumeTail, TrigProgram.real, TrigOp.real,
      Expr.real, inputEnv, pushEnv, realVolumes, outer, ClippedDifferential.inner, U, V, Psi, phi, T, F, theta,
      s, r, m, q, k, ClippingCircle.radius, ClippedEdge.normalAngle,
      ClippedFormula.z, ClippedFormula.b, ClippedFormula.outerBase, ClippedFormula.innerBase,
      div_eq_mul_inv, pow_succ, mul_assoc]

theorem realVolumes_manuscript {R x : ℝ} (hR : 1 / 2 < R) (hx : 0 ≤ x) :
    realVolumes R x =
      ⟨ClippedFormula.outerEdge R (1 - x), ClippedFormula.innerEdge R (1 - x),
        ClippedFormula.combinedEdge R (1 - x),
        (47 * ClippedFormula.innerBase R - ClippedFormula.outerBase R) / 46 +
          6 * ClippedFormula.combinedEdge R (1 - x)⟩ := by
  unfold realVolumes ClippedFormula.combinedEdge
  rw [outer_eq_manuscript hR hx, inner_eq_manuscript hR hx]

theorem realVolumes_baseline {R : ℝ} (hR : 1 / 2 < R) :
    (realVolumes R 1).baseline = ClippedFormula.combinedBaseline R := by
  rw [realVolumes_manuscript hR (by norm_num)]
  simp only [sub_self, ClippedFormula.combinedBaseline]

def Derivatives.Rel {α β : Type*} (rel : α → β → Prop) (a : Derivatives α)
    (b : Derivatives β) : Prop := rel a.outer b.outer ∧ rel a.inner b.inner ∧ rel a.combined b.combined

def Volumes.Rel {α β : Type*} (rel : α → β → Prop) (a : Volumes α) (b : Volumes β) : Prop :=
  rel a.outer b.outer ∧ rel a.inner b.inner ∧ rel a.combined b.combined ∧ rel a.baseline b.baseline

theorem inputEnv_rel {α β : Type*} {rel : α → β → Prop} {a b : α} {x y : β}
    (ha : rel a x) (hb : rel b y) : ∀ i, rel (inputEnv a b i) (inputEnv x y i) := by
  intro i
  cases i with
  | zero => exact ha
  | succ i => exact hb

theorem dxOut_rel {α β : Type*} {rel : α → β → Prop} {a : ℕ → α} {b : ℕ → β}
    (h : ∀ i, rel (a i) (b i)) : (dxOut a).Rel rel (dxOut b) := ⟨h 2, h 1, h 0⟩

theorem volumeOut_rel {α β : Type*} {rel : α → β → Prop} {a : ℕ → α} {b : ℕ → β}
    (h : ∀ i, rel (a i) (b i)) : (volumeOut a).Rel rel (volumeOut b) := ⟨h 6, h 5, h 4, h 0⟩

theorem dxInterval_sound {p n : ℕ} {R x : Interval} {out : Derivatives Interval} {a b : ℝ}
    (h : dxInterval p n R x = some out) (hR : R.Contains p a) (hx : x.Contains p b) :
    out.Rel (fun I z ↦ I.Contains p z) (realDerivatives a b) := by
  simp only [dxInterval, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  have hr := dxOut_rel (rel := fun (I : Interval) z ↦ I.Contains p z) (TrigProgram.interval_sound he
    (inputEnv_rel (rel := fun (I : Interval) z ↦ I.Contains p z) hR hx))
  rwa [dxProgram_real] at hr

theorem volumeInterval_sound {p n : ℕ} {R x : Interval} {out : Volumes Interval} {a b : ℝ}
    (h : volumeInterval p n R x = some out) (hR : R.Contains p a) (hx : x.Contains p b) :
    out.Rel (fun I z ↦ I.Contains p z) (realVolumes a b) := by
  simp only [volumeInterval, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  have hr := volumeOut_rel (rel := fun (I : Interval) z ↦ I.Contains p z) (TrigProgram.interval_sound he
    (inputEnv_rel (rel := fun (I : Interval) z ↦ I.Contains p z) hR hx))
  rwa [volumeProgram_real] at hr

noncomputable def dxRealJet (R x : SecondOrder.Jet) : Derivatives SecondOrder.Jet :=
  dxOut (TrigProgram.realJet dxProgram (inputEnv R x))

noncomputable def volumeRealJet (R x : SecondOrder.Jet) : Volumes SecondOrder.Jet :=
  volumeOut (TrigProgram.realJet volumeProgram (inputEnv R x))

theorem dxJet_sound {p n : ℕ} {R x : Jet} {out : Derivatives Jet} {a b : SecondOrder.Jet}
    (h : dxJet p n R x = some out) (hR : R.Contains p a) (hx : x.Contains p b) :
    out.Rel (fun I z ↦ I.Contains p z) (dxRealJet a b) := by
  simp only [dxJet, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  exact dxOut_rel (TrigProgram.jet_sound he
    (inputEnv_rel (rel := fun (I : Jet) z ↦ I.Contains p z) hR hx))

theorem volumeJet_sound {p n : ℕ} {R x : Jet} {out : Volumes Jet} {a b : SecondOrder.Jet}
    (h : volumeJet p n R x = some out) (hR : R.Contains p a) (hx : x.Contains p b) :
    out.Rel (fun I z ↦ I.Contains p z) (volumeRealJet a b) := by
  simp only [volumeJet, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  exact volumeOut_rel (TrigProgram.jet_sound he
    (inputEnv_rel (rel := fun (I : Jet) z ↦ I.Contains p z) hR hx))

end BlaschkeLebesgue.Certificates.ClippedHull
