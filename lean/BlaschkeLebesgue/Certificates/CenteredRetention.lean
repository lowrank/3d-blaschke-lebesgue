module

public import BlaschkeLebesgue.Certificates.CenteredComputation
public import BlaschkeLebesgue.Certificates.ProjectiveSpatialVariation
public import BlaschkeLebesgue.RectangleVariation

/-! # Soundness of centered activation checks on quadrature cells -/

@[expose] public noncomputable section

open Set

namespace BlaschkeLebesgue.Certificates.CenteredProjective

open FixedPoint ProjectiveExpressions

theorem variationLower_le {p : ℕ} {half mid ds dt : Interval} {h m : ℝ}
    (hh : half.Contains p h) (hm : mid.Contains p m) :
    value p (variationLower p half mid ds dt) ≤ m - (value p ds.absMax + value p dt.absMax) * h := by
  have hM : (⟨ds.absMax + dt.absMax, ds.absMax + dt.absMax⟩ : Interval).Contains p
      (value p ds.absMax + value p dt.absMax) := by
    simp only [Interval.Contains, value_add, le_refl, and_self]
  exact (Interval.contains_sub hm (Interval.contains_mul hh hM)).1.trans_eq (by ring)

theorem retained_sound {p : ℕ} {par : Params Interval} {U V Um Vm half : Interval}
    {js jt : Values Jet} {mid : Values Interval} {a b ms mt h : ℝ}
    (hjs : valuesJet p (par.map (Jet.const p)) (Jet.var p U) (Jet.const p V) = some js)
    (hjt : valuesJet p (par.map (Jet.const p)) (Jet.const p U) (Jet.var p V) = some jt)
    (hmid : valuesInterval p par Um Vm = some mid)
    (hret : retained p half mid js jt = true)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (hU : ∀ s ∈ Icc (ms - h) (ms + h), U.Contains p s)
    (hV : ∀ t ∈ Icc (mt - h) (mt + h), V.Contains p t)
    (hUm : Um.Contains p ms) (hVm : Vm.Contains p mt)
    (hhalf : half.Contains p h) (hh : 0 ≤ h) :
    ∀ s ∈ Icc (ms - h) (ms + h), ∀ t ∈ Icc (mt - h) (mt + h),
      0 ≤ Completion.squareGap a b s t ∧ 0 ≤ Completion.squareDetLower a b s t := by
  intro s hs t ht
  simp only [retained, Bool.or_eq_true, Bool.and_eq_true] at hret
  rcases hret with hret | hret
  · simp only [ProjectiveCell.retained, Bool.and_eq_true] at hret
    have hv := spatialJetS_values hjs hp (hU s hs) (hV t ht)
    exact ⟨(Interval.pos_of_positiveCheck hv.1 hret.1).le,
      (Interval.pos_of_positiveCheck hv.2.1 hret.2).le⟩
  · have hm := valuesInterval_sound hmid hp hUm hVm
    have hdS (x : ℝ) (hx : x ∈ Icc (ms - h) (ms + h))
        (y : ℝ) (hy : y ∈ Icc (mt - h) (mt + h)) :=
      spatialJetS_activation_derivatives hjs hp (hU x hx) (hV y hy)
    have hdT (x : ℝ) (hx : x ∈ Icc (ms - h) (ms + h))
        (y : ℝ) (hy : y ∈ Icc (mt - h) (mt + h)) :=
      spatialJetT_activation_derivatives hjt hp (hU x hx) (hV y hy)
    have hG := rectangle_center_lower hh
      (fun x hx y hy ↦ (hdS x hx y hy).1.1) (fun x hx y hy ↦ (hdT x hx y hy).1.1)
      (fun x hx y hy ↦ Interval.abs_le_absMax (hdS x hx y hy).1.2)
      (fun x hx y hy ↦ Interval.abs_le_absMax (hdT x hx y hy).1.2) hs ht
    have hD := rectangle_center_lower hh
      (fun x hx y hy ↦ (hdS x hx y hy).2.1) (fun x hx y hy ↦ (hdT x hx y hy).2.1)
      (fun x hx y hy ↦ Interval.abs_le_absMax (hdS x hx y hy).2.2)
      (fun x hx y hy ↦ Interval.abs_le_absMax (hdT x hx y hy).2.2) hs ht
    exact ⟨((value_pos (of_decide_eq_true hret.1)).trans_le ((variationLower_le hhalf hm.1).trans hG)).le,
      ((value_pos (of_decide_eq_true hret.2)).trans_le ((variationLower_le hhalf hm.2.1).trans hD)).le⟩

end BlaschkeLebesgue.Certificates.CenteredProjective
