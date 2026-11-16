module

public import BlaschkeLebesgue.Certificates.ClippedHullSigns
public import BlaschkeLebesgue.ScalarSecant

/-! # Applying the derivative certificate to the six-edge secant argument -/

public noncomputable section

open Set

namespace BlaschkeLebesgue.Certificates.ClippedHull

open ClippedDifferential

variable (checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true)

theorem radius_sq_le_of_between {R S T : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) (hST : S ≤ T)
    (hT : T ^ 2 ≤ 3 / 8) : S ^ 2 ≤ 3 / 8 := by
  have hS : 0 ≤ S := hR.trans hRS
  nlinarith [mul_nonneg (sub_nonneg.mpr hST) (by linarith : 0 ≤ T + S)]

theorem combinedEdge_x_derivative {R x : ℝ} (hR : 60849 / 100000 ≤ R)
    (hx : 23 / 25 ≤ x) (hx1 : x ≤ 1) :
    HasDerivAt (fun z ↦ ClippedFormula.combinedEdge R (1 - z)) (combinedDx R x) x :=
  (domain_of_hull_rectangle hR hx hx1).hasDerivAt_combinedEdge

include checks

theorem combinedEdge_x_concave {R : ℝ} (hR : 60849 / 100000 ≤ R) (hRhi : R ^ 2 ≤ 3 / 8) :
    ConcaveOn ℝ (Icc (23 / 25) 1) (fun x ↦ ClippedFormula.combinedEdge R (1 - x)) := by
  apply concaveOn_of_slope_derivatives_nonpos (convex_Icc _ _)
    (fun x hx ↦ combinedEdge_x_derivative hR hx.1 hx.2)
  intro x hx
  obtain ⟨d, hd, hneg⟩ := (edgeSigns_of_checks checks hR hRhi hx.1 hx.2).2.1
  exact ⟨d, hd, hneg.le⟩

theorem combinedDx_radius_mono {R S x : ℝ} (hR : 60849 / 100000 ≤ R) (hRS : R ≤ S)
    (hS : S ^ 2 ≤ 3 / 8) (hx : 23 / 25 ≤ x) (hx1 : x ≤ 1) : combinedDx R x ≤ combinedDx S x := by
  have hm : MonotoneOn (fun t ↦ combinedDx t x) (Icc R S) :=
    monotoneOn_of_derivatives_nonneg (convex_Icc _ _) (by
      intro t ht
      have ht0 : 60849 / 100000 ≤ t := hR.trans ht.1
      have hthi : t ^ 2 ≤ 3 / 8 := radius_sq_le_of_between (by linarith) ht.1 ht.2 hS
      obtain ⟨d, hd, hpos⟩ := (edgeSigns_of_checks checks ht0 hthi hx hx1).2.2
      exact ⟨d, hd, hpos.le⟩)
  exact hm ⟨le_rfl, hRS⟩ ⟨hRS, le_rfl⟩ hRS

theorem combinedEdge_increment_radius {R S e : ℝ} (hR : 60849 / 100000 ≤ R) (hRS : R ≤ S)
    (hS : S ^ 2 ≤ 3 / 8) (he : 0 ≤ e) (hehi : e ≤ 2 / 25) :
    ClippedFormula.combinedEdge S e - ClippedFormula.combinedEdge S 0 ≤
      ClippedFormula.combinedEdge R e - ClippedFormula.combinedEdge R 0 := by
  have hd := derivative_order_increment (f := fun x ↦ ClippedFormula.combinedEdge R (1 - x))
    (g := fun x ↦ ClippedFormula.combinedEdge S (1 - x))
    (f' := combinedDx R) (g' := combinedDx S) (a := 1 - e) (b := 1) (by linarith)
    (fun x hx ↦ combinedEdge_x_derivative hR (by linarith [hx.1]) hx.2)
    (fun x hx ↦ combinedEdge_x_derivative (hR.trans hRS) (by linarith [hx.1]) hx.2)
    (fun x hx ↦ combinedDx_radius_mono checks hR hRS hS (by linarith [hx.1]) hx.2)
  simpa only [sub_sub_cancel, sub_self] using hd

theorem combinedEdge_increment_secant {R S E e : ℝ} (hR : 60849 / 100000 ≤ R)
    (hRS : R ≤ S) (hS : S ^ 2 ≤ 3 / 8) (hE : 0 < E) (hEhi : E ≤ 2 / 25)
    (he : 0 ≤ e) (heE : e ≤ E) :
    (ClippedFormula.combinedEdge S E - ClippedFormula.combinedEdge S 0) / E * e ≤
      ClippedFormula.combinedEdge R e - ClippedFormula.combinedEdge R 0 := by
  have hc := combinedEdge_x_concave checks (hR.trans hRS) hS
  have hsub : Icc (1 - E) 1 ⊆ Icc (23 / 25) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hs := concave_secant_increment hE he heE (hc.subset hsub (convex_Icc _ _))
  simp only [sub_sub_cancel, sub_self] at hs
  exact hs.trans (combinedEdge_increment_radius checks hR hRS hS he (heE.trans hEhi))

omit checks in
theorem combinedBaseline_mono
    (baselineChecks : ∀ i : Fin 32, baselineSignCheck 128 64 i 32 = true)
    {R S : ℝ} (hR : 60849 / 100000 ≤ R) (hRS : R ≤ S) (hS : S ^ 2 ≤ 3 / 8) :
    ClippedFormula.combinedBaseline R ≤ ClippedFormula.combinedBaseline S := by
  have hm : MonotoneOn ClippedFormula.combinedBaseline (Icc R S) :=
    monotoneOn_of_derivatives_nonneg (convex_Icc _ _) (by
      intro t ht
      have hthi : t ^ 2 ≤ 3 / 8 := radius_sq_le_of_between (by linarith) ht.1 ht.2 hS
      obtain ⟨d, hd, hpos⟩ := baselineSign_of_checks baselineChecks (hR.trans ht.1) hthi
      exact ⟨d, hd, hpos.le⟩)
  exact hm ⟨le_rfl, hRS⟩ ⟨hRS, le_rfl⟩ hRS

end BlaschkeLebesgue.Certificates.ClippedHull
