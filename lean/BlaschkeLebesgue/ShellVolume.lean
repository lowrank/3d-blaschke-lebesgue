module

public import BlaschkeLebesgue.ShellJacobian
public import BlaschkeLebesgue.PolarAnnulus

/-!
# Volume swept out by the interpolating support maps

The support-height gap times the tangent determinant integrates to the actual
volume between the rounded endpoint bodies. The proof applies directly to
summands of the unit ball, including nonsmooth bodies.
-/

public noncomputable section

open MeasureTheory Set Filter

namespace BlaschkeLebesgue

theorem shellVolume_integral {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (fun u : UnitSphere => ∫ t in (0 : ℝ)..1, shellDensity D K ε δ t u)
        sphereMeasure ∧
      bodyVolume (parallelBody K (ε + δ)) - bodyVolume (parallelBody D ε) =
        ∫ u : UnitSphere, (∫ t in (0 : ℝ)..1, shellDensity D K ε δ t u) ∂sphereMeasure := by
  obtain ⟨hJ, hvol⟩ := shellJacobian_integral hD hK hDK hε hδ
  obtain ⟨hpolar, hpolarEq⟩ := integral_annulus_polar
    (fun x => |(fderiv ℝ (shellMap D K ε δ) x).det|) hJ
  have he : (fun u : UnitSphere => ∫ r in (1 : ℝ)..2,
      r ^ 2 * |(fderiv ℝ (shellMap D K ε δ) (r • (u : Space))).det|) =ᵐ[sphereMeasure]
      fun u => ∫ t in (0 : ℝ)..1, shellDensity D K ε δ t u := by
    filter_upwards [abs_det_fderiv_shellMap_polar_ae hD hK hDK hε.le hδ.le] with u hu
    calc
      _ = ∫ r in (1 : ℝ)..2, shellDensity D K ε δ (r - 1) u := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hr
        dsimp only
        rw [hu r hr]
        have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1)
        field_simp
      _ = _ := by
        simpa only [sub_self, show (2 : ℝ) - 1 = 1 by norm_num] using
          intervalIntegral.integral_comp_sub_right (a := (1 : ℝ)) (b := 2)
            (fun t => shellDensity D K ε δ t u) 1
  exact ⟨hpolar.congr he, hvol.symm.trans (hpolarEq.trans (integral_congr_ae he))⟩

end BlaschkeLebesgue
