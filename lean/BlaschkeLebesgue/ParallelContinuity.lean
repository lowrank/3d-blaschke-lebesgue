module

public import BlaschkeLebesgue.ParallelInverse

/-!
# Continuity of parallel volume at radius zero

An inner ball bounds the parallel body by a slightly enlarged copy of the
original body. Cubic scaling and monotonicity then give right continuity of
its actual Lebesgue volume.
-/

public noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped Pointwise

namespace BlaschkeLebesgue

theorem parallelBody_subset_smul_of_innerBall {K : ConvexBody Space} {a t : ℝ}
    (ha : 0 < a) (hball : closedBall (0 : Space) a ⊆ (K : Set Space)) (ht : 0 ≤ t) :
    (parallelBody K t : Set Space) ⊆ ((1 + t / a) • K : ConvexBody Space) := by
  intro x hx
  apply (mem_iff_unit_inner_le_support _ _).2
  intro n hn
  rw [support_smul K n (by positivity)]
  have hs := support_ge_of_innerBall ha.le hball hn
  have hx' := inner_le_support (parallelBody K t) n hx
  rw [support_parallelBody K ht hn] at hx'
  have h := mul_le_mul_of_nonneg_left hs (div_nonneg ht ha.le)
  have ht' : t / a * a = t := div_mul_cancel₀ t ha.ne'
  nlinarith only [h, hx', ht']

theorem parallelBody_volume_sandwich {K : ConvexBody Space} {a t : ℝ}
    (ha : 0 < a) (hball : closedBall (0 : Space) a ⊆ (K : Set Space)) (ht : 0 ≤ t) :
    bodyVolume K ≤ bodyVolume (parallelBody K t) ∧
      bodyVolume (parallelBody K t) ≤ (1 + t / a) ^ 3 * bodyVolume K := by
  refine ⟨bodyVolume_mono (subset_parallelBody K t), ?_⟩
  have h := bodyVolume_mono (parallelBody_subset_smul_of_innerBall ha hball ht)
  rwa [bodyVolume_smul K (by positivity)] at h

theorem parallelBody_volume_tendsto_zero {K : ConvexBody Space}
    (h0 : (0 : Space) ∈ interior (K : Set Space)) :
    Tendsto (fun t => bodyVolume (parallelBody K t)) (𝓝[≥] (0 : ℝ)) (𝓝 (bodyVolume K)) := by
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h0)
  have hball : closedBall (0 : Space) (r / 2) ⊆ (K : Set Space) :=
    (closedBall_subset_ball (by linarith)).trans hrball
  have hcont : Continuous (fun t : ℝ => (1 + t / (r / 2)) ^ 3 * bodyVolume K) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => (1 + t / (r / 2)) ^ 3 * bodyVolume K)
      (𝓝[≥] 0) (𝓝 (bodyVolume K)) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (parallelBody_volume_sandwich (by positivity) hball ht).1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (parallelBody_volume_sandwich (by positivity) hball ht).2

end BlaschkeLebesgue
