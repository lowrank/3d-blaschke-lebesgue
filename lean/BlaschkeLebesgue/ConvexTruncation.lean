module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic

/-! # Extending a decreasing convex function constantly past an endpoint -/

public section

namespace BlaschkeLebesgue

theorem convexOn_truncate_right {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hanti : AntitoneOn f (Set.Icc a b)) :
    ConvexOn ℝ (Set.Ici a) (fun x ↦ f (min x b)) := by
  have himage : (fun x : ℝ ↦ min x b) '' Set.Ici a = Set.Icc a b := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨le_min hy hab, min_le_right _ _⟩
    · intro hx
      exact ⟨x, hx.1, min_eq_left hx.2⟩
  have hmin : ConcaveOn ℝ (Set.Ici a) (fun x : ℝ ↦ min x b) :=
    (concaveOn_id (convex_Ici a)).inf (concaveOn_const b (convex_Ici a))
  have hf' : ConvexOn ℝ ((fun x : ℝ ↦ min x b) '' Set.Ici a) f := by rwa [himage]
  have ha' : AntitoneOn f ((fun x : ℝ ↦ min x b) '' Set.Ici a) := by rwa [himage]
  exact hf'.comp_concaveOn hmin ha'

end BlaschkeLebesgue
