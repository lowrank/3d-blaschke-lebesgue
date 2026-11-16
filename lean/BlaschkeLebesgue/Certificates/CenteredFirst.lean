module

public import BlaschkeLebesgue.Certificates.CenteredPointIntegral
public import BlaschkeLebesgue.Certificates.Generated.CenteredFirstKernel

/-!
# A kernel-certified bound at the first report center

All 48 rows have separate kernel proofs. Their exact sum and the analytic
soundness theorem give a bound stronger than the first reported center value.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.CenteredProjective.First

open FixedPoint ProjectiveExpressions

theorem point_verified :
    check 52 48 (Interval.rational 52 1 1600) (Interval.rational 52 1 1600) = some 7008754898294 := by
  have hrows : ∀ i < 48, ProjectivePointIntegral.sumRange 48 (fun j ↦ cell 52 48 parameters i j) = rowValues[i]? := by
    intro i hi
    interval_cases i
    · exact row_00
    · exact row_01
    · exact row_02
    · exact row_03
    · exact row_04
    · exact row_05
    · exact row_06
    · exact row_07
    · exact row_08
    · exact row_09
    · exact row_10
    · exact row_11
    · exact row_12
    · exact row_13
    · exact row_14
    · exact row_15
    · exact row_16
    · exact row_17
    · exact row_18
    · exact row_19
    · exact row_20
    · exact row_21
    · exact row_22
    · exact row_23
    · exact row_24
    · exact row_25
    · exact row_26
    · exact row_27
    · exact row_28
    · exact row_29
    · exact row_30
    · exact row_31
    · exact row_32
    · exact row_33
    · exact row_34
    · exact row_35
    · exact row_36
    · exact row_37
    · exact row_38
    · exact row_39
    · exact row_40
    · exact row_41
    · exact row_42
    · exact row_43
    · exact row_44
    · exact row_45
    · exact row_46
    · exact row_47
  have hsum : ProjectivePointIntegral.sumRange 48 (fun i ↦ rowValues[i]?) = some 7008754898294 := by
    decide +kernel
  have hgrid : grid 52 48 parameters = some 7008754898294 :=
    (ProjectivePointIntegral.sumRange_congr hrows).trans hsum
  exact Option.bind_eq_some_iff.2 ⟨parameters, parameters_verified, hgrid⟩

theorem integral_lower : (7008754898294 / 4503599627370496 : ℝ) ≤ Completion.F (1 / 1600) (1 / 1600) := by
  have hA : (Interval.rational 52 1 1600).Contains 52 (1 / 1600 : ℝ) := by
    simpa only [Int.cast_one, Int.cast_ofNat] using Interval.contains_rational 52 1 1600
  have hchi : |Completion.obliquity (1 / 1600) (1 / 1600)| < 1 :=
    Completion.obliquity_abs_lt_one_of_total_lt_one (by norm_num) (by norm_num)
  have hv := check_sound point_verified (by decide) hA hA (by norm_num) hchi
  rw [← Completion.F_eq_fixedSquareIntegral (by norm_num : (0 : ℝ) ≤ 1 / 1600)
    (by norm_num : (0 : ℝ) ≤ 1 / 1600) (by norm_num)] at hv
  convert hv using 1
  norm_num [value, scale]

theorem reported_center_bound :
    (3499295368065 / 2251799813685248 : ℝ) ≤ Completion.F (1 / 1600) (1 / 1600) := by
  exact (by norm_num : (3499295368065 / 2251799813685248 : ℝ) ≤ 7008754898294 / 4503599627370496).trans integral_lower

end BlaschkeLebesgue.Certificates.CenteredProjective.First
