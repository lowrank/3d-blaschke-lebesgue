module

public import BlaschkeLebesgue.RadialVolume

/-!
# Minkowski sums and parallel bodies

The unit ball, reflected bodies, and outer parallel bodies are actual compact
convex sets. Support functions identify the difference body of a unit-width body
with the unit ball.
-/

public noncomputable section

open Metric Set MeasureTheory
open scoped InnerProductSpace Pointwise

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem support_add (K L : ConvexBody E) (n : E) :
    support (K + L) n = support K n + support L n := by
  apply le_antisymm
  · apply (support_le_iff _ _ _).2
    rintro x ⟨y, hy, z, hz, rfl⟩
    rw [inner_add_right]
    exact add_le_add (inner_le_support K n hy) (inner_le_support L n hz)
  · obtain ⟨x, hx, hxs, _⟩ := exists_support_point K n
    obtain ⟨y, hy, hys, _⟩ := exists_support_point L n
    have hxy : x + y ∈ K + L := Set.add_mem_add hx hy
    simpa only [inner_add_right, hxs, hys] using inner_le_support (K + L) n hxy

/-- Reflection in the origin. -/
@[expose] def reflectBody (K : ConvexBody E) : ConvexBody E := (-1 : ℝ) • K

theorem mem_reflectBody (K : ConvexBody E) (x : E) : x ∈ reflectBody K ↔ -x ∈ K := by
  change x ∈ (-1 : ℝ) • (K : Set E) ↔ _
  simp

theorem support_reflectBody (K : ConvexBody E) (n : E) :
    support (reflectBody K) n = support K (-n) := by
  apply le_antisymm
  · apply (support_le_iff _ _ _).2
    intro x hx
    simpa only [inner_neg_left, inner_neg_right, neg_neg] using
      inner_le_support K (-n) ((mem_reflectBody K x).1 hx)
  · obtain ⟨x, hx, hs, _⟩ := exists_support_point K (-n)
    have hx' : -x ∈ reflectBody K := (mem_reflectBody K (-x)).2 (by simpa using hx)
    simpa only [inner_neg_left, inner_neg_right, hs] using
      inner_le_support (reflectBody K) n hx'

theorem reflectBody_add (K L : ConvexBody E) :
    reflectBody (K + L) = reflectBody K + reflectBody L := by
  simp only [reflectBody, smul_add]

theorem eq_of_unit_support_eq {K L : ConvexBody E}
    (h : ∀ n, ‖n‖ = 1 → support K n = support L n) : K = L := by
  apply SetLike.ext
  intro x
  simp only [mem_iff_unit_inner_le_support]
  constructor <;> intro hx n hn
  · rw [← h n hn]
    exact hx n hn
  · rw [h n hn]
    exact hx n hn

/-- The closed unit ball in the Euclidean space of the theorem. -/
@[expose] def unitBallBody : ConvexBody Space where
  carrier := closedBall 0 1
  convex' := convex_closedBall _ _
  isCompact' := isCompact_closedBall _ _
  nonempty' := nonempty_closedBall.2 (by norm_num)

theorem mem_unitBallBody {x : Space} : x ∈ unitBallBody ↔ ‖x‖ ≤ 1 := by
  change x ∈ closedBall (0 : Space) 1 ↔ _
  simp

theorem support_unitBallBody {n : Space} (hn : ‖n‖ = 1) : support unitBallBody n = 1 := by
  apply le_antisymm
  · apply (support_le_iff _ _ _).2
    intro x hx
    have hi := real_inner_le_norm n x
    rw [hn, one_mul] at hi
    exact hi.trans (mem_unitBallBody.1 hx)
  · have hn' : n ∈ unitBallBody := mem_unitBallBody.2 hn.le
    simpa only [real_inner_self_eq_norm_sq, hn, one_pow] using
      inner_le_support unitBallBody n hn'

theorem bodyVolume_unitBallBody : bodyVolume unitBallBody = 4 * Real.pi / 3 := by
  rw [bodyVolume]
  change (volume (closedBall (0 : Space) 1)).toReal = _
  rw [EuclideanSpace.volume_closedBall_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

theorem bodyVolume_reflectBody (K : ConvexBody Space) :
    bodyVolume (reflectBody K) = bodyVolume K := by
  unfold bodyVolume reflectBody
  change (volume ((-1 : ℝ) • (K : Set Space))).toReal = _
  simp

theorem reflectBody_unitBallBody : reflectBody unitBallBody = unitBallBody := by
  apply eq_of_unit_support_eq
  intro n hn
  rw [support_reflectBody, support_unitBallBody hn,
    support_unitBallBody (show ‖-n‖ = 1 by simpa using hn)]

/-- The difference body of a body of width one is exactly the unit ball. -/
theorem HasConstantWidth.add_reflectBody {K : ConvexBody Space} (hK : HasConstantWidth K 1) :
    K + reflectBody K = unitBallBody := by
  apply eq_of_unit_support_eq
  intro n hn
  rw [support_add, support_reflectBody, support_unitBallBody hn]
  exact hK n hn

/-- Adding a ball of radius `t` when `t` is nonnegative. -/
@[expose] def parallelBody (K : ConvexBody Space) (t : ℝ) : ConvexBody Space :=
  K + t • unitBallBody

theorem parallelBody_zero (K : ConvexBody Space) : parallelBody K 0 = K := by
  apply SetLike.ext
  intro x
  change x ∈ (K : Set Space) + (0 : ℝ) • (unitBallBody : Set Space) ↔ x ∈ K
  simp [Set.zero_smul_set unitBallBody.nonempty]

theorem subset_parallelBody (K : ConvexBody Space) (t : ℝ) :
    (K : Set Space) ⊆ (parallelBody K t : Set Space) := by
  intro x hx
  refine ⟨x, hx, 0, ?_, by simp⟩
  exact ⟨0, mem_unitBallBody.2 (by simp), by simp⟩

theorem zero_mem_interior_parallelBody {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) (t : ℝ) :
    (0 : Space) ∈ interior (parallelBody K t : Set Space) :=
  interior_mono (subset_parallelBody K t) h0

theorem support_parallelBody (K : ConvexBody Space) {t : ℝ} (ht : 0 ≤ t)
    {n : Space} (hn : ‖n‖ = 1) : support (parallelBody K t) n = support K n + t := by
  rw [parallelBody, support_add, support_smul _ _ ht, support_unitBallBody hn, mul_one]

theorem bodyVolume_mono {K L : ConvexBody Space} (h : (K : Set Space) ⊆ (L : Set Space)) :
    bodyVolume K ≤ bodyVolume L :=
  ENNReal.toReal_mono L.isCompact.measure_lt_top.ne (measure_mono h)

theorem HasConstantWidth.parallelBody_width {K : ConvexBody Space} {w t : ℝ}
    (hK : HasConstantWidth K w) (ht : 0 ≤ t) :
    HasConstantWidth (parallelBody K t) (w + 2 * t) := by
  intro n hn
  rw [support_parallelBody K ht hn,
    support_parallelBody K ht (show ‖-n‖ = 1 by simpa using hn)]
  linarith only [hK n hn]

/-- The parallel body can also be written using the body and its reflection. -/
theorem HasConstantWidth.parallelBody_eq_smul_add_reflectBody {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) {t : ℝ} (ht : 0 ≤ t) :
    parallelBody K t = (1 + t) • K + t • reflectBody K := by
  apply eq_of_unit_support_eq
  intro n hn
  rw [support_parallelBody K ht hn, support_add,
    support_smul K n (by linarith), support_smul _ _ ht, support_reflectBody]
  nlinarith only [congrArg (fun s : ℝ ↦ t * s) (hK n hn)]

end BlaschkeLebesgue
