module

public import BlaschkeLebesgue.Certificates.FixedPointRounding

/-!
# A checked square-root proposal

Bounded Newton iteration is a proposal only. Two exact integer comparisons
certify its answer; otherwise the operation falls back to `Nat.sqrt`.
The result is proved equal to `Nat.sqrt` for every input and every precision.
-/

@[expose] public section

namespace BlaschkeLebesgue.Certificates.FixedPoint

theorem checkedNatSqrt_eq (p n : ℕ) : checkedNatSqrt p n = Nat.sqrt n := by
  unfold checkedNatSqrt
  dsimp only
  split_ifs with h
  · exact Nat.eq_sqrt.2 h
  · rfl

theorem checkedSqrtFloor_eq (p : ℕ) (a : ℤ) : checkedSqrtFloor p a = sqrtFloor a := by
  simp only [checkedSqrtFloor, checkedNatSqrt_eq, sqrtFloor]

theorem checkedSqrtCeil_eq (p : ℕ) (a : ℤ) : checkedSqrtCeil p a = sqrtCeil a := by
  simp only [checkedSqrtCeil, checkedSqrtFloor_eq, sqrtCeil]

end BlaschkeLebesgue.Certificates.FixedPoint
