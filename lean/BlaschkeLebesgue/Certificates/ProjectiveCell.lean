module

public import BlaschkeLebesgue.Certificates.ProjectiveSpatialJets
public import BlaschkeLebesgue.CompletionCellQuadrature

/-!
# Executable lower bounds for completion quadrature cells

A retained cell uses checked pure second derivatives and a checked midpoint
value. The correction, positive-part truncation, and area multiplication all
round outward. Unretained cells contribute zero by nonnegativity of the true
density. Failed arithmetic domain checks return `none`.
-/

@[expose] public section

open Set MeasureTheory

namespace BlaschkeLebesgue.Certificates.ProjectiveCell

open FixedPoint ProjectiveExpressions

def correction (p : ℕ) (half : Interval) : Interval :=
  Interval.div p (Interval.sq p half) (Interval.integer p 6)

def correctedValue (p : ℕ) (half mid ds dt : Interval) : Interval :=
  let M : Interval := ⟨ds.absMax + dt.absMax, ds.absMax + dt.absMax⟩
  mid.sub (Interval.mul p (correction p half) M)

def contribution (p : ℕ) (half area mid ds dt : Interval) : ℤ :=
  let v := correctedValue p half mid ds dt
  (Interval.mul p (Interval.pos ⟨v.lo, v.lo⟩) area).lo

def retained (v : Values Jet) : Bool := v.G.v.positiveCheck && v.D.v.positiveCheck

def lower (p : ℕ) (par : Params Interval) (U V Um Vm half area : Interval) : Option ℤ :=
  (valuesJet p (par.map (Jet.const p)) (Jet.var p U) (Jet.const p V)).bind fun js ↦
  if retained js then
    (valuesJet p (par.map (Jet.const p)) (Jet.const p U) (Jet.var p V)).bind fun jt ↦
      (valuesInterval p par Um Vm).map fun mid ↦ contribution p half area mid.V js.V.dd jt.V.dd
  else some 0

theorem correction_contains {p : ℕ} {half : Interval} {h : ℝ} (hh : half.Contains p h) :
    (correction p half).Contains p (h ^ 2 / 6) := by
  have h6 : (Interval.integer p 6).Contains p (6 : ℝ) := by
    simpa only [Int.cast_ofNat] using Interval.contains_integer p 6
  have hc : (Interval.integer p 6).invCheck = true := by
    unfold Interval.invCheck Interval.integer
    apply decide_eq_true
    left
    exact mul_pos (by norm_num) (by exact_mod_cast scale_pos p)
  exact Interval.contains_div (Interval.contains_sq hh) h6 hc

theorem contribution_le {p : ℕ} {half area mid ds dt : Interval} {h v : ℝ}
    (hh : half.Contains p h) (ha : area.Contains p (4 * h * h)) (hv : mid.Contains p v) :
    value p (contribution p half area mid ds dt) ≤
      4 * h * h * max (v - value p ds.absMax * h ^ 2 / 6 - value p dt.absMax * h ^ 2 / 6) 0 := by
  have hM : (⟨ds.absMax + dt.absMax, ds.absMax + dt.absMax⟩ : Interval).Contains p
      (value p ds.absMax + value p dt.absMax) := by
    simp only [Interval.Contains, value_add, le_refl, and_self]
  have hc := Interval.contains_sub hv (Interval.contains_mul (correction_contains hh) hM)
  have hl : value p (correctedValue p half mid ds dt).lo ≤
      v - value p ds.absMax * h ^ 2 / 6 - value p dt.absMax * h ^ 2 / 6 := by
    exact hc.1.trans_eq (by ring)
  have hs : (⟨(correctedValue p half mid ds dt).lo, (correctedValue p half mid ds dt).lo⟩ : Interval).Contains p
      (value p (correctedValue p half mid ds dt).lo) := ⟨le_rfl, le_rfl⟩
  have hm := Interval.contains_mul (Interval.contains_pos hs) ha
  refine hm.1.trans ?_
  have harea : 0 ≤ 4 * h * h := by nlinarith [sq_nonneg h]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (max_le_max hl (le_refl 0)) harea

theorem lower_sound {p : ℕ} {par : Params Interval} {U V Um Vm half area : Interval} {l : ℤ}
    {a b ms mt h : ℝ} (hc : lower p par U V Um Vm half area = some l)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (hU : ∀ s ∈ Icc (ms - h) (ms + h), U.Contains p s)
    (hV : ∀ t ∈ Icc (mt - h) (mt + h), V.Contains p t)
    (hUm : Um.Contains p ms) (hVm : Vm.Contains p mt)
    (hhalf : half.Contains p h) (harea : area.Contains p (4 * h * h))
    (ha : 0 ≤ a) (hchi : |Completion.obliquity a b| < 1) (hh : 0 ≤ h)
    (hcell : Icc (ms - h) (ms + h) ×ˢ Icc (mt - h) (mt + h) ⊆ Icc 0 1 ×ˢ Icc 0 1) :
    value p l ≤ ∫ s in (ms - h)..(ms + h), ∫ t in (mt - h)..(mt + h), Completion.unitSquareDensity a b s t := by
  simp only [lower, Option.bind_eq_some_iff] at hc
  obtain ⟨js, hjs, hc⟩ := hc
  split_ifs at hc with hret
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨jt, hjt, mid, hmid, rfl⟩ := hc
    simp only [retained, Bool.and_eq_true] at hret
    have hmt : mt ∈ Icc (mt - h) (mt + h) := ⟨by linarith, by linarith⟩
    have hG (s : ℝ) (hs : s ∈ Icc (ms - h) (ms + h)) (t : ℝ) (ht : t ∈ Icc (mt - h) (mt + h)) :
        0 ≤ Completion.squareGap a b s t :=
      (Interval.pos_of_positiveCheck (spatialJetS_values hjs hp (hU s hs) (hV t ht)).1 hret.1).le
    have hD (s : ℝ) (hs : s ∈ Icc (ms - h) (ms + h)) (t : ℝ) (ht : t ∈ Icc (mt - h) (mt + h)) :
        0 ≤ Completion.squareDetLower a b s t :=
      (Interval.pos_of_positiveCheck (spatialJetS_values hjs hp (hU s hs) (hV t ht)).2.1 hret.2).le
    have hds (s : ℝ) (hs : s ∈ Icc (ms - h) (ms + h)) :=
      spatialJetS_derivatives hjs hp (hU s hs) (hV mt hmt)
    have hdt (s : ℝ) (hs : s ∈ Icc (ms - h) (ms + h)) (t : ℝ) (ht : t ∈ Icc (mt - h) (mt + h)) :=
      spatialJetT_derivatives hjt hp (hU s hs) (hV t ht)
    have hquad := Completion.unitSquare_cell_quadrature_lower
      (Hx := fun q ↦ (spatialJetS a b q.1 q.2).V.d) (Hxx := fun q ↦ (spatialJetS a b q.1 q.2).V.dd)
      (Hy := fun q ↦ (spatialJetT a b q.1 q.2).V.d) (Hyy := fun q ↦ (spatialJetT a b q.1 q.2).V.dd)
      (Ms := value p js.V.dd.absMax) (Mt := value p jt.V.dd.absMax)
      ha hchi hh hh hcell hG hD
      (fun s hs ↦ (hds s hs).1) (fun s hs ↦ (hds s hs).2.1)
      (fun s hs t ht ↦ (hdt s hs t ht).1) (fun s hs t ht ↦ (hdt s hs t ht).2.1)
      (fun s hs ↦ (abs_le.mp (Interval.abs_le_absMax (hds s hs).2.2.2)).1)
      (fun s hs t ht ↦ (abs_le.mp (Interval.abs_le_absMax (hdt s hs t ht).2.2.2)).1)
    exact (contribution_le hhalf harea (valuesInterval_sound hmid hp hUm hVm).2.2).trans hquad
  · simp only [Option.some.injEq] at hc
    subst l
    rw [value_zero]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro s hs
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have hst : (s, t) ∈ Icc 0 1 ×ˢ Icc 0 1 := hcell ⟨hs, ht⟩
    exact Completion.unitSquareDensity_nonneg_of_obliquity ha hchi hst.1.1 t

end BlaschkeLebesgue.Certificates.ProjectiveCell
