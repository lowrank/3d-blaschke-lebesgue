module

public import BlaschkeLebesgue.Contacts
public import BlaschkeLebesgue.EnclosingBall
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Contact configurations constructed from a convex body

This file supplies the geometric input to the deficit estimates: the contacts are
points of the given body, their radius is its minimum enclosing radius, and their
strictly positive weights and affine independence follow from Carathéodory's theorem.
-/

public noncomputable section

open scoped InnerProductSpace BigOperators

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Balanced contacts of a specified minimum enclosing ball, expressed relative to
its center. Membership, positivity, and affine independence are retained. -/
structure EnclosingContacts {K : ConvexBody E} (b : MinimumEnclosingBall K) (n : ℕ)
    extends BalancedContacts n E where
  radius_eq : radius = b.radius
  point_mem : ∀ i, point i + b.center ∈ K
  affineIndependent : AffineIndependent ℝ point
  weight_pos : ∀ i, 0 < weight i

namespace MinimumEnclosingBall

variable {K : ConvexBody E} (b : MinimumEnclosingBall K)

theorem exists_contacts [FiniteDimensional ℝ E] (hK : HasConstantWidth K 1) :
    ∃ n ≤ Module.finrank ℝ E + 1, Nonempty (EnclosingContacts b n) := by
  obtain ⟨n, hn, w, z, haff, hw, hsum, hz, hbalance⟩ :=
    exists_small_positive_convex_combination b.center_mem_convexHull_contacts
  refine ⟨n, hn, ⟨{
    point := fun i ↦ z i - b.center
    weight := w
    radius := b.radius
    weight_nonneg := fun i ↦ (hw i).le
    weight_sum := hsum
    balance := ?_
    on_sphere := fun i ↦ (hz i).2
    diameter_le := ?_
    radius_eq := rfl
    point_mem := ?_
    affineIndependent := ?_
    weight_pos := hw }⟩⟩
  · simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, hbalance]
    simp
  · intro i j
    have hid : (z i - b.center) - (z j - b.center) = z i - z j := by abel
    rw [hid]
    exact hK.norm_sub_le (by norm_num) (hz i).1 (hz j).1
  · intro i
    simpa using (hz i).1
  · have h := haff.vadd (v := -b.center)
    convert h using 1
    funext i
    change z i - b.center = -b.center + z i
    abel

/-- A unit-width body cannot fit in a ball of radius less than one half. -/
theorem radius_ge_half [Nontrivial E] (hK : HasConstantWidth K 1) :
    (1 / 2 : ℝ) ≤ b.radius := by
  obtain ⟨u, hu⟩ := exists_norm_eq (E := E) (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨x, hx, hsupport, _⟩ := exists_support_point K u
  have hy := hK.opposite_point hu hx hsupport.symm
  have hdist : ‖x - (x - u)‖ = 1 := by simpa using hu
  have htriangle : ‖x - (x - u)‖ ≤ ‖x - b.center‖ + ‖(x - u) - b.center‖ := by
    simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub x b.center (x - u)
  linarith [b.norm_sub_center_le hx, b.norm_sub_center_le hy]

end MinimumEnclosingBall

namespace EnclosingContacts

variable {K : ConvexBody E} {b : MinimumEnclosingBall K} {n : ℕ}
  (c : EnclosingContacts b n)

include c in
theorem card_eq_four (hn : n ≤ 4) (hR : (1 / 3 : ℝ) < b.radius ^ 2) : n = 4 := by
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ c.toBalancedContacts.weight_le i
  simp only [c.weight_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, c.radius_eq] at hsum
  have hfactor : 0 ≤ 1 - 2 * b.radius ^ 2 := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n : (0 : ℝ) ≤ n) h.le
    linarith
  by_contra h
  have hsmall : (n : ℝ) ≤ 3 := by exact_mod_cast (show n ≤ 3 by omega)
  nlinarith [mul_le_mul_of_nonneg_right hsmall hfactor]

end EnclosingContacts

/-- Jung's bound now applies to the actual minimum radius of every unit-width body. -/
theorem MinimumEnclosingBall.radius_sq_le {K : ConvexBody Space}
    (b : MinimumEnclosingBall K) (hK : HasConstantWidth K 1) : b.radius ^ 2 ≤ 3 / 8 := by
  obtain ⟨n, hn, ⟨c⟩⟩ := b.exists_contacts hK
  have hn' : n ≤ 4 := by simpa [Space] using hn
  simpa only [c.radius_eq] using c.toBalancedContacts.radius_sq_le hn'

/-- Above the three-contact threshold, four genuine contacts supply the previously
proved deficit budget. -/
theorem MinimumEnclosingBall.exists_four_contacts {K : ConvexBody Space}
    (b : MinimumEnclosingBall K) (hK : HasConstantWidth K 1)
    (hR : (1 / 3 : ℝ) < b.radius ^ 2) : Nonempty (EnclosingContacts b 4) := by
  obtain ⟨n, hn, ⟨c⟩⟩ := b.exists_contacts hK
  have hn' : n ≤ 4 := by simpa [Space] using hn
  have hn4 := c.card_eq_four hn' hR
  subst n
  exact ⟨c⟩

/-- The four selected contacts form a genuine tetrahedron with the circumcenter
strictly inside it. -/
theorem EnclosingContacts.zero_mem_interior_convexHull {K : ConvexBody Space}
    {b : MinimumEnclosingBall K} (c : EnclosingContacts b 4) :
    (0 : Space) ∈ interior (convexHull ℝ (Set.range c.point)) := by
  classical
  let B : AffineBasis (Fin 4) ℝ Space := ⟨c.point, c.affineIndependent,
    c.affineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by simp [Space])⟩
  change (0 : Space) ∈ interior (convexHull ℝ (Set.range B))
  rw [B.interior_convexHull]
  intro i
  have hzero : Finset.univ.affineCombination ℝ B c.weight = 0 := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ c.weight_sum]
    exact c.balance
  have hcoord := B.coord_apply_combination_of_mem (Finset.mem_univ i) c.weight_sum
  rw [hzero] at hcoord
  rw [hcoord]
  exact c.weight_pos i

/-- The high-radius branch starts with an actual contact tetrahedron satisfying
the full edge-deficit budget; no balanced configuration is assumed. -/
theorem MinimumEnclosingBall.exists_contacts_with_deficit_budget {K : ConvexBody Space}
    (b : MinimumEnclosingBall K) (hK : HasConstantWidth K 1)
    (hR : 60849 / 100000 ≤ b.radius) :
    ∃ c : EnclosingContacts b 4,
      16 * (3 / 8 - b.radius ^ 2) ≤ c.toBalancedContacts.totalDeficit ∧
      c.toBalancedContacts.totalDeficit ≤ 16 * (3 / 8 - b.radius ^ 2) /
        (1 - 8 * (3 / 8 - b.radius ^ 2)) ∧ c.toBalancedContacts.totalDeficit < 2 / 25 := by
  have hR' : (1 / 3 : ℝ) < b.radius ^ 2 := by nlinarith
  obtain ⟨c⟩ := b.exists_four_contacts hK hR'
  refine ⟨c, ?_⟩
  have hc := c.toBalancedContacts.deficit_budget (c.radius_eq ▸ hR)
  simpa only [c.radius_eq] using hc

end BlaschkeLebesgue
