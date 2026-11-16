module

public import BlaschkeLebesgue.SphereIsometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Rotations and longitude about the first coordinate axis -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

local instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

@[expose] def rotateCoordinates (t : ℝ) (x : Space) : Space :=
  !₂[x 0, Real.cos t * x 1 - Real.sin t * x 2, Real.sin t * x 1 + Real.cos t * x 2]

theorem rotateCoordinates_zero (t : ℝ) (x : Space) : rotateCoordinates t x 0 = x 0 := rfl

theorem rotateCoordinates_one (t : ℝ) (x : Space) :
    rotateCoordinates t x 1 = Real.cos t * x 1 - Real.sin t * x 2 := rfl

theorem rotateCoordinates_two (t : ℝ) (x : Space) :
    rotateCoordinates t x 2 = Real.sin t * x 1 + Real.cos t * x 2 := rfl

theorem rotateCoordinates_neg (t : ℝ) (x : Space) :
    rotateCoordinates (-t) (rotateCoordinates t x) = x := by
  ext i
  fin_cases i
  · rfl
  · change rotateCoordinates (-t) (rotateCoordinates t x) 1 = x 1
    simp only [rotateCoordinates_one, rotateCoordinates_two, Real.cos_neg, Real.sin_neg]
    linear_combination (x 1) * (Real.cos_sq_add_sin_sq t)
  · change rotateCoordinates (-t) (rotateCoordinates t x) 2 = x 2
    simp only [rotateCoordinates_one, rotateCoordinates_two, Real.cos_neg, Real.sin_neg]
    linear_combination (x 2) * (Real.cos_sq_add_sin_sq t)

theorem rotateCoordinates_norm (t : ℝ) (x : Space) : ‖rotateCoordinates t x‖ = ‖x‖ := by
  have hs : ‖rotateCoordinates t x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
      rotateCoordinates_zero, rotateCoordinates_one, rotateCoordinates_two]
    linear_combination ((x 1) ^ 2 + (x 2) ^ 2) * (Real.cos_sq_add_sin_sq t)
  nlinarith [norm_nonneg (rotateCoordinates t x), norm_nonneg x]

@[expose] def longitudeRotation (t : ℝ) : Space ≃ₗᵢ[ℝ] Space where
  toFun := rotateCoordinates t
  invFun := rotateCoordinates (-t)
  left_inv := rotateCoordinates_neg t
  right_inv x := by simpa only [neg_neg] using rotateCoordinates_neg (-t) x
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rotateCoordinates] <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [rotateCoordinates, smul_eq_mul] <;> ring
  norm_map' := rotateCoordinates_norm t

@[expose] def transverseComplex (x : Space) : ℂ := (x 1 : ℂ) + (x 2 : ℂ) * Complex.I

@[expose] def longitude (u : UnitSphere) : AddCircle (2 * Real.pi) := (transverseComplex u).arg

theorem transverseComplex_longitudeRotation (t : ℝ) (x : Space) :
    transverseComplex (longitudeRotation t x) =
      ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) * transverseComplex x := by
  apply Complex.ext <;> simp [transverseComplex, longitudeRotation, rotateCoordinates]
  ring

theorem longitudeRotation_pole (t : ℝ) : longitudeRotation t coordinatePole = coordinatePole := by
  ext i
  fin_cases i <;> simp [longitudeRotation, rotateCoordinates, coordinatePole,
    EuclideanSpace.single, PiLp.toLp_apply]

theorem longitude_rotate (t : ℝ) (u : UnitSphere) (hu : transverseComplex u ≠ 0) :
    longitude (sphereIsometry (longitudeRotation t) u) =
      (t : AddCircle (2 * Real.pi)) + longitude u := by
  have ht : ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) ≠ 0 := by
    have h : ‖((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)‖ = 1 := by
      simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.norm_cos_add_sin_mul_I t
    intro he
    rw [he, norm_zero] at h
    norm_num at h
  change ((transverseComplex (sphereIsometry (longitudeRotation t) u)).arg : Real.Angle) =
    (t : Real.Angle) + ((transverseComplex u).arg : Real.Angle)
  rw [sphereIsometry_val, transverseComplex_longitudeRotation,
    Complex.arg_mul_coe_angle ht hu]
  congr 1
  simpa only [Real.Angle.cos_coe, Real.Angle.sin_coe] using
    Complex.arg_cos_add_sin_mul_I_coe_angle (t : Real.Angle)

theorem measurable_longitude : Measurable longitude := by
  unfold longitude transverseComplex
  fun_prop

end BlaschkeLebesgue
