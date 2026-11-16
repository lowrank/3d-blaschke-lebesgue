module

public import BlaschkeLebesgue.Certificates.ClippedHullExpressions

/-! # Analytic meaning of clipped-hull derivative outputs -/

public noncomputable section

namespace BlaschkeLebesgue.Certificates.ClippedHull

open FixedPoint ClippedDifferential

attribute [local irreducible] dxProgram volumeProgram

 theorem dxJet_derivatives {p n : ℕ} {R x : Jet} {out : Derivatives Jet}
    {a b : ℝ → SecondOrder.Jet} {z : ℝ} (h : dxJet p n R x = some out)
    (hR : R.Contains p (a z)) (hx : x.Contains p (b z))
    (ha : SecondOrder.Jet.ValidAt a z) (hb : SecondOrder.Jet.ValidAt b z) :
    HasDerivAt (fun t ↦ combinedDx (a t).v (b t).v) (dxRealJet (a z) (b z)).combined.d z ∧
      out.combined.d.Contains p (dxRealJet (a z) (b z)).combined.d := by
  simp only [dxJet, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  have hf : ∀ i, SecondOrder.Jet.ValidAt (inputEnv a b i) z := by
    intro i
    cases i with
    | zero => exact ha
    | succ i => exact hb
  have hi : ∀ i, (inputEnv R x i).Contains p (inputEnv a b i z) := by
    intro i
    cases i with
    | zero => exact hR
    | succ i => exact hx
  have hd := TrigProgram.jet_derivatives (p := p) (n := n) (es := dxProgram)
    (env := inputEnv R x) (out := env) (fs := inputEnv a b) (x := z) he hi hf 0
  have heq : (fun t ↦ combinedDx (a t).v (b t).v) =
      (fun t ↦ TrigProgram.real dxProgram (fun j ↦ (inputEnv a b j t).v) 0) := by
    funext t
    have hen : (fun j ↦ (inputEnv a b j t).v) = inputEnv (a t).v (b t).v := by
      funext j
      cases j <;> rfl
    rw [hen]
    exact (congrArg Derivatives.combined (dxProgram_real (a t).v (b t).v)).symm
  have hj : (fun j ↦ inputEnv a b j z) = inputEnv (a z) (b z) := by
    funext j
    cases j <;> rfl
  rw [hj] at hd
  constructor
  · rw [heq]
    exact hd.1
  · exact hd.2.2.1

theorem volumeJet_derivatives {p n : ℕ} {R x : Jet} {out : Volumes Jet}
    {a b : ℝ → SecondOrder.Jet} {z : ℝ} (h : volumeJet p n R x = some out)
    (hR : R.Contains p (a z)) (hx : x.Contains p (b z))
    (ha : SecondOrder.Jet.ValidAt a z) (hb : SecondOrder.Jet.ValidAt b z) :
    HasDerivAt (fun t ↦ (realVolumes (a t).v (b t).v).baseline) (volumeRealJet (a z) (b z)).baseline.d z ∧
      out.baseline.d.Contains p (volumeRealJet (a z) (b z)).baseline.d := by
  simp only [volumeJet, Option.map_eq_some_iff] at h
  obtain ⟨env, he, rfl⟩ := h
  have hf : ∀ i, SecondOrder.Jet.ValidAt (inputEnv a b i) z := by
    intro i
    cases i with
    | zero => exact ha
    | succ i => exact hb
  have hi : ∀ i, (inputEnv R x i).Contains p (inputEnv a b i z) := by
    intro i
    cases i with
    | zero => exact hR
    | succ i => exact hx
  have hd := TrigProgram.jet_derivatives (p := p) (n := n) (es := volumeProgram)
    (env := inputEnv R x) (out := env) (fs := inputEnv a b) (x := z) he hi hf 0
  have heq : (fun t ↦ (realVolumes (a t).v (b t).v).baseline) =
      (fun t ↦ TrigProgram.real volumeProgram (fun j ↦ (inputEnv a b j t).v) 0) := by
    funext t
    have hen : (fun j ↦ (inputEnv a b j t).v) = inputEnv (a t).v (b t).v := by
      funext j
      cases j <;> rfl
    rw [hen]
    exact (congrArg Volumes.baseline (volumeProgram_real (a t).v (b t).v)).symm
  have hj : (fun j ↦ inputEnv a b j z) = inputEnv (a z) (b z) := by
    funext j
    cases j <;> rfl
  rw [hj] at hd
  constructor
  · rw [heq]
    exact hd.1
  · exact hd.2.2.1

end BlaschkeLebesgue.Certificates.ClippedHull
