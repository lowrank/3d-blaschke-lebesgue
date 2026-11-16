module

public import BlaschkeLebesgue.SmallBallIntersections
public import BlaschkeLebesgue.BlaschkeIdentity

/-!
# Actual ball-transform complements and their volume coefficients

The ball transform is bundled as a compact convex body when nonempty. For an
intersection of balls of radius at most one, its reflected transform is an
actual Minkowski complement. The proved determinant polynomial then supplies
the complementary volume and coefficient identities.
-/

public noncomputable section

open Set Metric MeasureTheory
open scoped InnerProductSpace

namespace BlaschkeLebesgue

theorem ballTransform_eq_iInter (s : Set Space) :
    ballTransform s = ⋂ y ∈ s, closedBall y 1 := by
  ext x
  simp only [ballTransform, mem_ofPred_eq, mem_iInter, mem_closedBall, dist_eq_norm]

theorem convex_ballTransform (s : Set Space) : Convex ℝ (ballTransform s) := by
  rw [ballTransform_eq_iInter]
  exact convex_iInter₂ fun y _ => convex_closedBall y 1

theorem isClosed_ballTransform (s : Set Space) : IsClosed (ballTransform s) := by
  rw [ballTransform_eq_iInter]
  exact isClosed_biInter fun y _ => isClosed_closedBall

theorem isCompact_ballTransform {s : Set Space} (hs : s.Nonempty) :
    IsCompact (ballTransform s) := by
  obtain ⟨y, hy⟩ := hs
  apply isCompact_of_isClosed_isBounded (isClosed_ballTransform s)
  apply (isBounded_closedBall (x := y) (r := 1)).subset
  intro x hx
  exact (mem_closedBall.2 (by simpa only [dist_eq_norm] using hx y hy))

@[expose] def ballTransformBody (C : ConvexBody Space)
    (hD : (ballTransform (C : Set Space)).Nonempty) : ConvexBody Space where
  carrier := ballTransform (C : Set Space)
  convex' := convex_ballTransform _
  isCompact' := isCompact_ballTransform C.nonempty
  nonempty' := hD

theorem smallBallIntersection_add_complement {ι : Type*} {C D : ConvexBody Space}
    (c : ι → Space) (r : ι → ℝ) (hr : ∀ i, r i ≤ 1)
    (hC : (C : Set Space) = ⋂ i, closedBall (c i) (r i))
    (hD : (D : Set Space) = ballTransform (C : Set Space)) :
    C + reflectBody D = unitBallBody := by
  apply eq_of_unit_support_eq
  intro n hn
  rw [support_add, support_reflectBody, support_unitBallBody hn]
  obtain ⟨x, hx, hsx, _⟩ := exists_support_point C n
  obtain ⟨y, hy, hsy, _⟩ := exists_support_point D (-n)
  have hy' : y ∈ ballTransform (C : Set Space) := by
    rw [← hD]
    exact hy
  have hnorm := hy' x hx
  have hi := real_inner_le_norm n (x - y)
  rw [hn, one_mul, inner_sub_right] at hi
  rw [norm_sub_rev] at hnorm
  have hop := smallBallIntersection_opposite_mem c r hr hC hx hn hsx.symm
  have hop' : x - n ∈ D := by
    change x - n ∈ (D : Set Space)
    rw [hD]
    exact hop
  have hsupport := inner_le_support D (-n) hop'
  rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq, hn, one_pow] at hsupport
  rw [inner_neg_left] at hsy
  apply le_antisymm <;> linarith only [hi, hnorm, hsx, hsy, hsupport]

theorem reflectBody_reflectBody (K : ConvexBody Space) : reflectBody (reflectBody K) = K := by
  simp [reflectBody, smul_smul]

theorem parallelPolynomial_reflectBody {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    parallelConstant (reflectBody K) = parallelConstant K ∧
      parallelLinear (reflectBody K) = parallelLinear K ∧
      parallelQuadratic (reflectBody K) = parallelQuadratic K := by
  have href : reflectBody K + reflectBody L = unitBallBody := by
    rw [← reflectBody_add, hKL, reflectBody_unitBallBody]
  have href0 := zero_mem_interior_reflectBody h0
  have hc : parallelConstant (reflectBody K) = parallelConstant K := by
    rw [parallelConstant_eq_volume href href0, parallelConstant_eq_volume hKL h0,
      bodyVolume_reflectBody]
  have heq (t : ℝ) (ht : 0 < t) : parallelPolynomial (reflectBody K) t =
      parallelPolynomial K t := by
    rw [parallelPolynomial_eq_volume_pos href href0 ht,
      parallelPolynomial_eq_volume_pos hKL h0 ht, ← reflectBody_parallelBody,
      bodyVolume_reflectBody]
  have h1 := heq 1 (by norm_num)
  have h2 := heq 2 (by norm_num)
  simp only [parallelPolynomial, hc] at h1 h2
  norm_num at h1 h2
  exact ⟨hc, by linarith only [h1, h2], by linarith only [h1, h2]⟩

/-- Complementarity determines actual volumes and both nonconstant Steiner coefficients. -/
theorem complementary_volume_coefficients {C D : ConvexBody Space}
    (hCD : C + reflectBody D = unitBallBody)
    (hC0 : (0 : Space) ∈ interior (C : Set Space))
    (hD0 : (0 : Space) ∈ interior (D : Set Space)) :
    bodyVolume D = 4 * Real.pi / 3 - parallelQuadratic C + parallelLinear C - bodyVolume C ∧
      parallelLinear D = 4 * Real.pi - 2 * parallelQuadratic C + parallelLinear C ∧
      parallelQuadratic C + parallelQuadratic D = 4 * Real.pi := by
  have hDsum : D + reflectBody C = unitBallBody := by
    have h := congrArg reflectBody hCD
    change reflectBody (C + reflectBody D) = reflectBody unitBallBody at h
    rw [reflectBody_add, reflectBody_reflectBody, reflectBody_unitBallBody] at h
    rwa [add_comm]
  have href := parallelPolynomial_reflectBody hDsum hD0
  have hpoly (t : ℝ) : parallelPolynomial (reflectBody D) t = -parallelPolynomial C (-1 - t) :=
    parallelPolynomial_complement hCD hC0 (zero_mem_interior_reflectBody hD0) t
  have h0 := hpoly 0
  have h1 := hpoly 1
  have h2 := hpoly 2
  simp only [parallelPolynomial, href.1, href.2.1, href.2.2,
    parallelConstant_eq_volume hCD hC0, parallelConstant_eq_volume hDsum hD0,
    bodyVolume_unitBallBody] at h0 h1 h2
  norm_num at h0 h1 h2
  exact ⟨by linarith only [h0], by linarith only [h0, h1, h2],
    by linarith only [h0, h1, h2]⟩

end BlaschkeLebesgue
