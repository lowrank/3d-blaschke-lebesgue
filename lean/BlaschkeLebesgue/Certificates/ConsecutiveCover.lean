module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-! # Closed coverage by consecutive scalar intervals -/

public section

namespace BlaschkeLebesgue.Certificates

theorem exists_consecutive_interval {f : ℕ → ℝ} {x : ℝ} {n : ℕ}
    (hn : 0 < n) (h0 : f 0 ≤ x) (hx : x ≤ f n) :
    ∃ i < n, f i ≤ x ∧ x ≤ f (i + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by omega, h0, hx⟩
    · by_cases hxn : x ≤ f n
      · obtain ⟨i, hi, hlo, hhi⟩ := ih (by omega) hxn
        exact ⟨i, by omega, hlo, hhi⟩
      · exact ⟨n, by omega, (lt_of_not_ge hxn).le, hx⟩

end BlaschkeLebesgue.Certificates
