module

public import BlaschkeLebesgue.Contacts

/-! # Relabeling the actual contact configuration -/

public noncomputable section

open scoped BigOperators

namespace BlaschkeLebesgue.BalancedContacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (c : BalancedContacts n E)

/-- Permuting labels preserves all the geometric and balancing data. -/
@[expose] def relabel (e : Equiv.Perm (Fin n)) : BalancedContacts n E where
  point i := c.point (e i)
  weight i := c.weight (e i)
  radius := c.radius
  weight_nonneg i := c.weight_nonneg (e i)
  weight_sum := (Equiv.sum_comp e c.weight).trans c.weight_sum
  balance := (Equiv.sum_comp e (fun i ↦ c.weight i • c.point i)).trans c.balance
  on_sphere i := c.on_sphere (e i)
  diameter_le i j := c.diameter_le (e i) (e j)

theorem edgeDeficit_relabel (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    (c.relabel e).edgeDeficit i j = c.edgeDeficit (e i) (e j) := rfl

theorem totalDeficit_relabel (c : BalancedContacts 4 E) (e : Equiv.Perm (Fin 4)) :
    (c.relabel e).totalDeficit = c.totalDeficit := by
  rw [(c.relabel e).totalDeficit_eq, c.totalDeficit_eq]
  have hs := Equiv.sum_comp e c.point
  have hs' : c.point (e 0) + c.point (e 1) + c.point (e 2) + c.point (e 3) =
      c.point 0 + c.point 1 + c.point 2 + c.point 3 := by
    simpa [Fin.sum_univ_succ, Fin.succ, add_assoc] using hs
  change 6 - 16 * c.radius ^ 2 +
      ‖c.point (e 0) + c.point (e 1) + c.point (e 2) + c.point (e 3)‖ ^ 2 = _
  rw [hs']

end BlaschkeLebesgue.BalancedContacts
