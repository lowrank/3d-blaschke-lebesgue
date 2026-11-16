module

public import BlaschkeLebesgue.Minkowski
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Support maps of summands of the unit ball

If two actual convex bodies add to the unit ball, each has a unique support point
in every unit direction. Their support maps are 1-Lipschitz on the sphere. Bodies
of constant width one satisfy the hypothesis by their difference-body identity.
-/

public noncomputable section

open MeasureTheory Set NormedSpace
open scoped InnerProductSpace

namespace BlaschkeLebesgue

/-- Choose a support point of the actual body. Uniqueness is proved below when applicable. -/
@[expose] def supportPoint (K : ConvexBody Space) (u : Space) : Space :=
  (exists_support_point K u).choose

theorem supportPoint_mem (K : ConvexBody Space) (u : Space) : supportPoint K u ∈ K :=
  (exists_support_point K u).choose_spec.1

theorem inner_supportPoint (K : ConvexBody Space) (u : Space) :
    ⟪u, supportPoint K u⟫_ℝ = support K u :=
  (exists_support_point K u).choose_spec.2.1.symm

theorem eq_unit_of_norm_le_inner_eq {u x : Space} (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1)
    (hi : ⟪u, x⟫_ℝ = 1) : x = u := by
  have hs := (sq_le_sq₀ (norm_nonneg x) zero_le_one).2 hx
  have hd := norm_sub_sq_real u x
  rw [hu, hi] at hd
  have hzero : ‖u - x‖ ^ 2 = 0 := by nlinarith only [hd, hs, sq_nonneg ‖u - x‖]
  exact (sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 hzero))).symm

theorem support_add_point_eq_unit {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    {u x y : Space} (hu : ‖u‖ = 1) (hx : x ∈ K) (hy : y ∈ L)
    (hsx : ⟪u, x⟫_ℝ = support K u) (hsy : ⟪u, y⟫_ℝ = support L u) : x + y = u := by
  apply eq_unit_of_norm_le_inner_eq hu
  · apply mem_unitBallBody.1
    rw [← hKL]
    exact Set.add_mem_add hx hy
  · rw [inner_add_right, hsx, hsy, ← support_add, hKL, support_unitBallBody hu]

theorem supportPoint_add_eq_unit {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    {u : Space} (hu : ‖u‖ = 1) : supportPoint K u + supportPoint L u = u :=
  support_add_point_eq_unit hKL hu (supportPoint_mem K u) (supportPoint_mem L u)
    (inner_supportPoint K u) (inner_supportPoint L u)

theorem supportPoint_unique_of_ball_sum {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    {u x : Space} (hu : ‖u‖ = 1) (hx : x ∈ K) (hsx : ⟪u, x⟫_ℝ = support K u) :
    x = supportPoint K u := by
  have h1 := support_add_point_eq_unit hKL hu hx (supportPoint_mem L u) hsx
    (inner_supportPoint L u)
  have h2 := supportPoint_add_eq_unit hKL hu
  exact add_right_cancel (h1.trans h2.symm)

/-- The firm Lipschitz inequality follows from the two crossed pairs of support points. -/
theorem supportPoint_firm_of_ball_sum {K L : ConvexBody Space} (hKL : K + L = unitBallBody)
    {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖supportPoint K u - supportPoint K v‖ ^ 2 ≤
      ⟪supportPoint K u - supportPoint K v, u - v⟫_ℝ := by
  let d := supportPoint K u - supportPoint K v
  have hsumv := supportPoint_add_eq_unit hKL hv
  have hsumu := supportPoint_add_eq_unit hKL hu
  have h1 : ‖d + v‖ ≤ 1 := by
    have heq : d + v = supportPoint K u + supportPoint L v := by
      calc
        d + v = d + (supportPoint K v + supportPoint L v) :=
          congrArg (fun z ↦ d + z) hsumv.symm
        _ = _ := by dsimp [d]; abel
    rw [heq]
    apply mem_unitBallBody.1
    rw [← hKL]
    exact Set.add_mem_add (supportPoint_mem K u) (supportPoint_mem L v)
  have h2 : ‖u - d‖ ≤ 1 := by
    have heq : u - d = supportPoint K v + supportPoint L u := by
      calc
        u - d = (supportPoint K u + supportPoint L u) - d :=
          congrArg (fun z ↦ z - d) hsumu.symm
        _ = _ := by dsimp [d]; abel
    rw [heq]
    apply mem_unitBallBody.1
    rw [← hKL]
    exact Set.add_mem_add (supportPoint_mem K v) (supportPoint_mem L u)
  have hs1 := (sq_le_sq₀ (norm_nonneg (d + v)) zero_le_one).2 h1
  have hs2 := (sq_le_sq₀ (norm_nonneg (u - d)) zero_le_one).2 h2
  rw [norm_add_sq_real, hv] at hs1
  rw [norm_sub_sq_real, hu] at hs2
  change ‖d‖ ^ 2 ≤ ⟪d, u - v⟫_ℝ
  rw [inner_sub_right]
  nlinarith only [hs1, hs2, real_inner_comm d u]

theorem supportPoint_norm_sub_le_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖supportPoint K u - supportPoint K v‖ ≤ ‖u - v‖ := by
  have hfirm := supportPoint_firm_of_ball_sum hKL hu hv
  have hi := real_inner_le_norm (supportPoint K u - supportPoint K v) (u - v)
  by_cases hz : ‖supportPoint K u - supportPoint K v‖ = 0
  · simpa only [hz] using norm_nonneg (u - v)
  · apply le_of_mul_le_mul_left (a := ‖supportPoint K u - supportPoint K v‖)
      (by nlinarith only [hfirm, hi])
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)

theorem supportPoint_lipschitz_sphere_of_ball_sum {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    LipschitzWith 1 (fun u : UnitSphere ↦ supportPoint K u) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm] using
    supportPoint_norm_sub_le_of_ball_sum hKL (UnitSphere.norm_eq_one u) (UnitSphere.norm_eq_one v)

theorem HasConstantWidth.supportPoint_lipschitz_sphere {K : ConvexBody Space}
    (hK : HasConstantWidth K 1) : LipschitzWith 1 (fun u : UnitSphere ↦ supportPoint K u) :=
  supportPoint_lipschitz_sphere_of_ball_sum hK.add_reflectBody

end BlaschkeLebesgue
