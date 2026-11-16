module

public import BlaschkeLebesgue.Certificates.ProjectiveGradientIntegral
public import BlaschkeLebesgue.Certificates.Generated.FirstGradientKernel

/-! # Kernel-certified parameter variation on the first report box -/

@[expose] public section

open Set

namespace BlaschkeLebesgue.Certificates.ProjectiveGradientIntegral.First

open FixedPoint ProjectiveExpressions

theorem check_a_verified :
    check 52 64 true box box = some (⟨-38305472032463, -8962798632166⟩ : Interval) := by
  have hrows : ∀ i < 64, sumRange 64 (fun j ↦ cell 52 64 parameters_a i j) = rows_a[i]? := by
    intro i hi
    interval_cases i
    · exact row_a_00
    · exact row_a_01
    · exact row_a_02
    · exact row_a_03
    · exact row_a_04
    · exact row_a_05
    · exact row_a_06
    · exact row_a_07
    · exact row_a_08
    · exact row_a_09
    · exact row_a_10
    · exact row_a_11
    · exact row_a_12
    · exact row_a_13
    · exact row_a_14
    · exact row_a_15
    · exact row_a_16
    · exact row_a_17
    · exact row_a_18
    · exact row_a_19
    · exact row_a_20
    · exact row_a_21
    · exact row_a_22
    · exact row_a_23
    · exact row_a_24
    · exact row_a_25
    · exact row_a_26
    · exact row_a_27
    · exact row_a_28
    · exact row_a_29
    · exact row_a_30
    · exact row_a_31
    · exact row_a_32
    · exact row_a_33
    · exact row_a_34
    · exact row_a_35
    · exact row_a_36
    · exact row_a_37
    · exact row_a_38
    · exact row_a_39
    · exact row_a_40
    · exact row_a_41
    · exact row_a_42
    · exact row_a_43
    · exact row_a_44
    · exact row_a_45
    · exact row_a_46
    · exact row_a_47
    · exact row_a_48
    · exact row_a_49
    · exact row_a_50
    · exact row_a_51
    · exact row_a_52
    · exact row_a_53
    · exact row_a_54
    · exact row_a_55
    · exact row_a_56
    · exact row_a_57
    · exact row_a_58
    · exact row_a_59
    · exact row_a_60
    · exact row_a_61
    · exact row_a_62
    · exact row_a_63
  have hsum : sumRange 64 (fun i ↦ rows_a[i]?) = some (⟨-38305472032463, -8962798632166⟩ : Interval) := by
    decide +kernel
  have hgrid : grid 52 64 parameters_a = some (⟨-38305472032463, -8962798632166⟩ : Interval) :=
    (sumRange_congr hrows).trans hsum
  exact Option.bind_eq_some_iff.2 ⟨parameters_a, parameters_a_verified, hgrid⟩

theorem check_b_verified :
    check 52 64 false box box = some (⟨23361772611441, 131824902922151⟩ : Interval) := by
  have hrows : ∀ i < 64, sumRange 64 (fun j ↦ cell 52 64 parameters_b i j) = rows_b[i]? := by
    intro i hi
    interval_cases i
    · exact row_b_00
    · exact row_b_01
    · exact row_b_02
    · exact row_b_03
    · exact row_b_04
    · exact row_b_05
    · exact row_b_06
    · exact row_b_07
    · exact row_b_08
    · exact row_b_09
    · exact row_b_10
    · exact row_b_11
    · exact row_b_12
    · exact row_b_13
    · exact row_b_14
    · exact row_b_15
    · exact row_b_16
    · exact row_b_17
    · exact row_b_18
    · exact row_b_19
    · exact row_b_20
    · exact row_b_21
    · exact row_b_22
    · exact row_b_23
    · exact row_b_24
    · exact row_b_25
    · exact row_b_26
    · exact row_b_27
    · exact row_b_28
    · exact row_b_29
    · exact row_b_30
    · exact row_b_31
    · exact row_b_32
    · exact row_b_33
    · exact row_b_34
    · exact row_b_35
    · exact row_b_36
    · exact row_b_37
    · exact row_b_38
    · exact row_b_39
    · exact row_b_40
    · exact row_b_41
    · exact row_b_42
    · exact row_b_43
    · exact row_b_44
    · exact row_b_45
    · exact row_b_46
    · exact row_b_47
    · exact row_b_48
    · exact row_b_49
    · exact row_b_50
    · exact row_b_51
    · exact row_b_52
    · exact row_b_53
    · exact row_b_54
    · exact row_b_55
    · exact row_b_56
    · exact row_b_57
    · exact row_b_58
    · exact row_b_59
    · exact row_b_60
    · exact row_b_61
    · exact row_b_62
    · exact row_b_63
  have hsum : sumRange 64 (fun i ↦ rows_b[i]?) = some (⟨23361772611441, 131824902922151⟩ : Interval) := by
    decide +kernel
  have hgrid : grid 52 64 parameters_b = some (⟨23361772611441, 131824902922151⟩ : Interval) :=
    (sumRange_congr hrows).trans hsum
  exact Option.bind_eq_some_iff.2 ⟨parameters_b, parameters_b_verified, hgrid⟩

theorem box_contains {x : ℝ} (hx : x ∈ Icc 0 (1 / 800)) : box.Contains 52 x := by
  have h0 : (Interval.rational 52 0 1).Contains 52 (0 : ℝ) := by
    simpa only [Int.cast_zero, Int.cast_one, zero_div] using Interval.contains_rational 52 0 1
  have h1 : (Interval.rational 52 1 800).Contains 52 (1 / 800 : ℝ) := by
    simpa only [Int.cast_one, Int.cast_ofNat] using Interval.contains_rational 52 1 800
  exact Interval.contains_span h0 h1 hx.1 hx.2

theorem a_secantBounds {b : ℝ} (hb : b ∈ Icc 0 (1 / 800)) :
    SecantBounds (fun a ↦ Completion.fixedSquareIntegral a b) 0 (1 / 800)
      (value 52 (-38305472032463)) (value 52 (-8962798632166)) := by
  apply check_secantBounds (fixed := b) check_a_verified (by decide)
  · intro z hz
    exact box_contains hz
  · intro z hz
    exact box_contains hb
  · intro z hz
    exact ⟨hz.1, hb.1, by change z + b ≤ 1 / 10; linarith [hz.2, hb.2]⟩

theorem b_secantBounds {a : ℝ} (ha : a ∈ Icc 0 (1 / 800)) :
    SecantBounds (Completion.fixedSquareIntegral a) 0 (1 / 800)
      (value 52 23361772611441) (value 52 131824902922151) := by
  apply check_secantBounds (fixed := a) check_b_verified (by decide)
  · intro z hz
    exact box_contains ha
  · intro z hz
    exact box_contains hz
  · intro z hz
    exact ⟨ha.1, hz.1, by change a + z ≤ 1 / 10; linarith [ha.2, hz.2]⟩

end BlaschkeLebesgue.Certificates.ProjectiveGradientIntegral.First
