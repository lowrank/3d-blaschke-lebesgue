module

public import BlaschkeLebesgue.Certificates.CenteredRetention
public import BlaschkeLebesgue.Certificates.ProjectivePointIntegral

/-!
# Sound point quadrature with centered activation checks

The midpoint and checked first derivatives certify the sign of the actual
activation functions throughout a cell. The existing second-derivative
quadrature estimate then supplies its nonnegative lower contribution.
-/

@[expose] public section

open Set MeasureTheory

namespace BlaschkeLebesgue.Certificates.CenteredProjective

open FixedPoint ProjectiveExpressions ProjectivePointIntegral

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
  simp only [lower, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
  obtain ⟨js, hjs, jt, hjt, mid, hmid, hc⟩ := hc
  split_ifs at hc with hret
  · subst l
    have hmt : mt ∈ Icc (mt - h) (mt + h) := ⟨by linarith, by linarith⟩
    have hpos := retained_sound hjs hjt hmid hret hp hU hV hUm hVm hhalf hh
    have hG := fun s hs t ht ↦ (hpos s hs t ht).1
    have hD := fun s hs t ht ↦ (hpos s hs t ht).2
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
    exact (ProjectiveCell.contribution_le hhalf harea (valuesInterval_sound hmid hp hUm hVm).2.2).trans hquad
  · subst l
    rw [value_zero]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro s hs
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have hst : (s, t) ∈ Icc 0 1 ×ˢ Icc 0 1 := hcell ⟨hs, ht⟩
    exact Completion.unitSquareDensity_nonneg_of_obliquity ha hchi hst.1.1 t

theorem cell_sound {p n i j : ℕ} {par : Params Interval} {l : ℤ} {a b : ℝ}
    (h : cell p n par i j = some l) (hi : i < n) (hj : j < n)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (ha : 0 ≤ a) (hchi : |Completion.obliquity a b| < 1) :
    value p l ≤ ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
      ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), Completion.unitSquareDensity a b s t := by
  have hn := Nat.zero_lt_of_lt hi
  rw [UniformGrid.point_eq_midpoint_sub hn i, UniformGrid.point_succ_eq_midpoint_add hn i,
    UniformGrid.point_eq_midpoint_sub hn j, UniformGrid.point_succ_eq_midpoint_add hn j]
  apply lower_sound h hp
  · intro s hs
    apply span_contains
    rwa [UniformGrid.point_eq_midpoint_sub hn i, UniformGrid.point_succ_eq_midpoint_add hn i]
  · intro t ht
    apply span_contains
    rwa [UniformGrid.point_eq_midpoint_sub hn j, UniformGrid.point_succ_eq_midpoint_add hn j]
  · exact midpoint_contains p n i
  · exact midpoint_contains p n j
  · exact halfWidth_contains p n
  · exact area_contains p n
  · exact ha
  · exact hchi
  · exact UniformGrid.halfWidth_nonneg n
  · have hc := UniformGrid.cell_subset_unitSquare hi hj
    dsimp only [UniformGrid.cell] at hc
    rwa [UniformGrid.point_eq_midpoint_sub hn i, UniformGrid.point_succ_eq_midpoint_add hn i,
      UniformGrid.point_eq_midpoint_sub hn j, UniformGrid.point_succ_eq_midpoint_add hn j] at hc

theorem grid_sound {p n : ℕ} {par : Params Interval} {l : ℤ} {a b : ℝ}
    (h : grid p n par = some l) (hn : 0 < n)
    (hp : par.Rel (fun I z ↦ I.Contains p z) (realParams a b))
    (ha : 0 ≤ a) (hchi : |Completion.obliquity a b| < 1) :
    value p l ≤ Completion.fixedSquareIntegral a b := by
  have hb := sumRange_lower h (g := fun i ↦ ∑ j ∈ Finset.range n,
      ∫ s in UniformGrid.point n i..UniformGrid.point n (i + 1),
        ∫ t in UniformGrid.point n j..UniformGrid.point n (j + 1), Completion.unitSquareDensity a b s t)
    (fun i hi v hv ↦ sumRange_lower hv (fun j hj w hw ↦ cell_sound hw hi hj hp ha hchi))
  have he := UniformGrid.integral_unitSquare_eq_sum (Completion.continuous_unitSquareDensity_of_obliquity hchi) hn
  exact hb.trans_eq he.symm

theorem check_sound {p n : ℕ} {A B : Interval} {l : ℤ} {a b : ℝ}
    (h : check p n A B = some l) (hn : 0 < n) (hA : A.Contains p a) (hB : B.Contains p b)
    (ha : 0 ≤ a) (hchi : |Completion.obliquity a b| < 1) :
    value p l ≤ Completion.fixedSquareIntegral a b := by
  simp only [check, Option.bind_eq_some_iff] at h
  obtain ⟨par, hp, hg⟩ := h
  exact grid_sound hg hn (paramsInterval_sound hp hA hB) ha hchi


end BlaschkeLebesgue.Certificates.CenteredProjective
