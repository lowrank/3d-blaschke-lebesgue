module

public import BlaschkeLebesgue.Certificates.ClippedHullBucket
public import BlaschkeLebesgue.CompletionPatchSum

/-! # The larger-radius branch assembled from the three finite certificates

The computational statements remain explicit premises until all generated
kernel modules have passed and the unconditional suite is imported.
-/

public noncomputable section

namespace BlaschkeLebesgue.BalancedContacts

open Certificates.ClippedHull BlaschkeLebesgue.BalancedContacts.Opposite

variable (c : BalancedContacts 4 Space)

theorem near_volume_bound_of_certificates
    (checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true)
    (baselineChecks : ∀ i : Fin 32, baselineSignCheck 128 64 i 32 = true)
    (secantChecks : ∀ i : Fin 512, secantCheck 128 64 i 512 = true)
    (affine : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 2 / 25 →
      153 / 100000 - 601 / 100000 * a + 317 / 20000 * b < Completion.F a b)
    {K : ConvexBody Space} (hK : HasConstantWidth K 1)
    (hcontacts : Set.range c.point ⊆ (K : Set Space)) (hball : ∀ p ∈ K, ‖p‖ ≤ c.radius)
    (hR : 60849 / 100000 ≤ c.radius) : 259 / 625 < bodyVolume K := by
  have hR0 : 0 ≤ c.radius := by linarith
  have hR1 : c.radius < 1 := by nlinarith [c.radius_sq_le (by decide)]
  have hA := (c.deficit_budget hR).2.2.le
  obtain ⟨i, hlo, hhi⟩ := radius_bucket_cover hR (c.radius_sq_le (by decide))
  have hv := c.clipped_volume_ge_certified_bucket checks baselineChecks i (secantChecks i)
    hlo hhi (hne := hK.clippedOuter_nonempty hcontacts hball) hR0 hR1.le
  have hc := clipped_volume_ge_completion_sum c hK hcontacts hball hA hR1
  dsimp only at hc
  have hF : ∀ j, 153 / 100000 - 601 / 100000 * pairEdgeBudget c j +
      317 / 20000 * pairCrossBudget c j < Completion.F (pairEdgeBudget c j) (pairCrossBudget c j) := by
    intro j
    have hp := pair_rectangle_bounds c hA j
    exact affine _ _ hp.1 hp.2.1 (by linarith [hp.2.2.1])
  have hsum := sum_pair_affine_bounds c hF
  have hL := (c.deficit_in_radius_bucket i hlo hhi).1
  have hresponse : (secantResponse i 512 : ℝ) ≤ (8 / 23 : ℝ) *
      (∑ j : Fin 3, Completion.F (pairEdgeBudget c j) (pairCrossBudget c j)) := by
    unfold secantResponse
    push_cast
    nlinarith
  have hbucket := (secantCheck_sound_512 i (secantChecks i)).2
  linarith only [hv, hc, hresponse, hbucket]

end BlaschkeLebesgue.BalancedContacts
