module

public import BlaschkeLebesgue.SupportInterior

/-!
# Interpolating nested summands of the ball

Minkowski interpolation preserves the ball-summand property. After adding a
positive parallel radius, its supporting points give the concrete family used
to parametrize the region between the endpoint bodies.
-/

public noncomputable section

open Set NormedSpace
open scoped InnerProductSpace Pointwise

namespace BlaschkeLebesgue

@[expose] def interpolateBody (D K : ConvexBody Space) (t : ℝ) : ConvexBody Space :=
  (1 - t) • D + t • K

theorem support_interpolateBody (D K : ConvexBody Space) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (u : Space) : support (interpolateBody D K t) u =
      (1 - t) * support D u + t * support K u := by
  rw [interpolateBody, support_add, support_smul D u (sub_nonneg.2 ht.2), support_smul K u ht.1]

theorem interpolateBody_complement {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    interpolateBody D K t + interpolateBody D' K' t = unitBallBody := by
  apply eq_of_unit_support_eq
  intro u hu
  have hd := congrArg (fun E : ConvexBody Space => support E u) hD
  have hk := congrArg (fun E : ConvexBody Space => support E u) hK
  rw [support_add, support_unitBallBody hu] at hd hk
  rw [support_add, support_interpolateBody D K ht, support_interpolateBody D' K' ht,
    support_unitBallBody hu]
  nlinarith only [hd, hk, congrArg (fun z : ℝ => t * z) hd,
    congrArg (fun z : ℝ => t * z) hk]

theorem normalSupport_unit (K : ConvexBody Space) {u : Space} (hu : ‖u‖ = 1) :
    normalSupport K u = supportPoint K u := by
  simp only [normalSupport, normalize_eq_self_of_norm_eq_one hu]

theorem interpolate_supportPoint {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {u : Space} (hu : ‖u‖ = 1) :
    supportPoint (interpolateBody D K t) u =
      (1 - t) • normalSupport D u + t • normalSupport K u := by
  symm
  apply supportPoint_unique_of_ball_sum (interpolateBody_complement hD hK ht) hu
  · exact Set.add_mem_add (Set.smul_mem_smul_set (normalSupport_mem D u))
      (Set.smul_mem_smul_set (normalSupport_mem K u))
  · rw [inner_add_right, inner_smul_right, inner_smul_right, inner_normalSupport,
      inner_normalSupport, support_interpolateBody D K ht]

@[expose] def shellBody (D K : ConvexBody Space) (ε δ t : ℝ) : ConvexBody Space :=
  parallelBody (interpolateBody D K t) (ε + t * δ)

@[expose] def shellPoint (D K : ConvexBody Space) (ε δ t : ℝ) (u : Space) : Space :=
  (1 - t) • normalSupport D u + t • normalSupport K u + (ε + t * δ) • u

theorem support_shellBody (D K : ConvexBody Space) {ε δ t : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (ht : t ∈ Icc (0 : ℝ) 1)
    {u : Space} (hu : ‖u‖ = 1) :
    support (shellBody D K ε δ t) u =
      support D u + ε + t * (support K u - support D u + δ) := by
  rw [shellBody, support_parallelBody _ (add_nonneg hε (mul_nonneg ht.1 hδ)) hu,
    support_interpolateBody D K ht]
  ring

theorem shellPoint_mem (D K : ConvexBody Space) (ε δ t : ℝ) {u : Space} (hu : ‖u‖ = 1) :
    shellPoint D K ε δ t u ∈ shellBody D K ε δ t := by
  exact Set.add_mem_add
    (Set.add_mem_add (Set.smul_mem_smul_set (normalSupport_mem D u))
      (Set.smul_mem_smul_set (normalSupport_mem K u)))
    (Set.smul_mem_smul_set (mem_unitBallBody.2 hu.le))

theorem inner_shellPoint (D K : ConvexBody Space) {ε δ t : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (ht : t ∈ Icc (0 : ℝ) 1)
    {u : Space} (hu : ‖u‖ = 1) :
    ⟪u, shellPoint D K ε δ t u⟫_ℝ = support (shellBody D K ε δ t) u := by
  rw [shellPoint, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_normalSupport, inner_normalSupport,
    real_inner_self_eq_norm_sq, hu, one_pow, mul_one, support_shellBody D K hε hδ ht hu]
  ring

theorem shellPoint_unique {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (ht : t ∈ Icc (0 : ℝ) 1)
    {u x : Space} (hu : ‖u‖ = 1) (hx : x ∈ shellBody D K ε δ t)
    (hs : ⟪u, x⟫_ℝ = support (shellBody D K ε δ t) u) :
    x = shellPoint D K ε δ t u := by
  have h := parallel_support_point_unique (interpolateBody_complement hD hK ht)
    (add_nonneg hε (mul_nonneg ht.1 hδ)) hu hx hs
  rw [interpolate_supportPoint hD hK ht hu] at h
  exact h

end BlaschkeLebesgue
