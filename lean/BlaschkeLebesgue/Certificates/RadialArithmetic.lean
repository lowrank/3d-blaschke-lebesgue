module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum

/-!
# Exact rational checker for the eight radial certificate rows

This checker uses the original candidate integers, exact rational arithmetic, and
integer floor. It recomputes the comparisons and lower sums rather than reading a
PASS flag or an endpoint from the reports. Its successful execution is proved by
kernel reduction in the generated row modules.

The result is a finite arithmetic certificate. The geometric cap-integration
theorem needed to apply it to an arbitrary convex body is a separate obligation.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.RadialArithmetic

structure Parameters where
  lo : ℚ
  hi : ℚ
  tangentPoint : ℚ
  expectedCoefficient : ℚ

def gridSize : ℕ := 4096
def candidateScale : ℚ := 1000000000000
def roundingScale : ℚ := 1000000000000000000

def parameterM (p : Parameters) : ℚ := 1 - p.hi ^ 2

def parameterA (p : Parameters) : ℚ :=
  2 * (p.tangentPoint ^ 2 + 3 * parameterM p) /
    (3 * (p.tangentPoint ^ 2 + parameterM p) ^ 2)

def parameterB (p : Parameters) : ℚ :=
  2 * p.tangentPoint ^ 3 / (p.tangentPoint ^ 2 + parameterM p) -
    parameterA p * p.tangentPoint ^ 3

def tangentGap (p : Parameters) (x : ℚ) : ℚ :=
  parameterA p * x ^ 3 + parameterB p - 2 * x ^ 3 / (x ^ 2 + parameterM p)

def cosine (k : ℕ) : ℚ :=
  ((gridSize : ℚ) ^ 2 - (k : ℚ) ^ 2) / ((gridSize : ℚ) ^ 2 + (k : ℚ) ^ 2)

def sine (k : ℕ) : ℚ :=
  2 * gridSize * k / ((gridSize : ℚ) ^ 2 + (k : ℚ) ^ 2)

def stepCosine (k : ℕ) : ℚ :=
  let a : ℚ := (gridSize : ℚ) ^ 2 + (k : ℚ) * ((k : ℚ) - 1)
  (a ^ 2 - (gridSize : ℚ) ^ 2) / (a ^ 2 + (gridSize : ℚ) ^ 2)

def stepSine (k : ℕ) : ℚ :=
  let a : ℚ := (gridSize : ℚ) ^ 2 + (k : ℚ) * ((k : ℚ) - 1)
  2 * gridSize * a / (a ^ 2 + (gridSize : ℚ) ^ 2)

def separationThreshold (p : Parameters) : ℚ :=
  let eta := 1 / (2 * p.lo ^ 2) - 1
  4 * eta ^ 2 / (1 - eta) - 1

def positiveStep (p : Parameters) (k : ℕ) (previous x : ℚ) : Bool :=
  let t := x ^ 2 + parameterM p
  let d := 4 * x ^ 2 - t ^ 2
  let b := previous * stepCosine k - x
  decide (p.tangentPoint < x ∧ x < previous ∧ 0 ≤ d ∧ 0 < b ∧
    previous ^ 2 * d * stepSine k ^ 2 ≤ t ^ 2 * b ^ 2 ∧
    separationThreshold p < cosine k ^ 2 - sine k ^ 2 ∧ 0 ≤ tangentGap p x)

def negativeStep (p : Parameters) (k : ℕ) (previous z : ℚ) : Bool :=
  decide (previous ≤ z ∧ z ≤ p.tangentPoint ∧ 0 ≤ z + p.lo * cosine k ∧
    1 - p.lo ^ 2 * sine k ^ 2 ≤ (z + p.lo * cosine k) ^ 2 ∧
    separationThreshold p < cosine k ^ 2 - sine k ^ 2 ∧ 0 ≤ tangentGap p z)

def positiveChecks (p : Parameters) (k : ℕ) (previous : ℚ) : List ℕ → Bool
  | [] => true
  | x :: xs => positiveStep p k previous (x / candidateScale) &&
      positiveChecks p (k + 1) (x / candidateScale) xs

def negativeChecks (p : Parameters) (k : ℕ) (previous : ℚ) : List ℕ → Bool
  | [] => true
  | z :: zs => negativeStep p k previous (z / candidateScale) &&
      negativeChecks p (k + 1) (z / candidateScale) zs

def ringTerm (p : Parameters) (k x : ℕ) : ℚ :=
  (cosine (k - 1) - cosine k) * tangentGap p (x / candidateScale)

def roundedTerm (p : Parameters) (k x : ℕ) : ℤ :=
  (roundingScale * ringTerm p k x).floor

def roundedSum (p : Parameters) (k : ℕ) : List ℕ → ℤ
  | [] => 0
  | x :: xs => roundedTerm p k x + roundedSum p (k + 1) xs

def coefficient (p : Parameters) (positive negative : List ℕ) : ℚ :=
  (2 / 3 - 4 * parameterB p +
    8 * ((roundedSum p 1 positive + roundedSum p 1 negative : ℤ) : ℚ) / roundingScale) /
      (3 * parameterA p - 2)

/-- Mathlib proves this terminating decimal is smaller than real pi. -/
def piLower : ℚ := 314159265358979323846 / 100000000000000000000

def checkRow (p : Parameters) (positive negative : List ℕ) : Bool :=
  decide (3 / 5 ≤ p.lo ∧ p.lo < p.hi ∧ p.hi ≤ 60849 / 100000 ∧
      5 / 8 ≤ parameterM p ∧ 1 - p.lo < p.tangentPoint ∧ p.tangentPoint < p.lo ∧
      1 / 3 < p.lo ^ 2 ∧ 0 < 3 * parameterA p - 2 ∧
      0 < positive.length ∧ positive.length < gridSize ∧
      0 < negative.length ∧ negative.length < gridSize) &&
    positiveChecks p 1 p.lo positive && negativeChecks p 1 0 negative &&
    decide (coefficient p positive negative = p.expectedCoefficient ∧
      0 < coefficient p positive negative ∧
      4144109 / 10000000 < piLower * coefficient p positive negative)

/-- Every rounded ring contribution is a conservative lower bound. -/
theorem roundedTerm_le (p : Parameters) (k x : ℕ) :
    (roundedTerm p k x : ℚ) / roundingScale ≤ ringTerm p k x := by
  apply (div_le_iff₀ (by norm_num [roundingScale])).2
  simpa only [roundedTerm, mul_comm] using Rat.floor_le (roundingScale * ringTerm p k x)

end BlaschkeLebesgue.Certificates.RadialArithmetic
