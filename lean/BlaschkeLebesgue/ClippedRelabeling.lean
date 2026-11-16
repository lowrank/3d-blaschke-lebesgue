module

public import BlaschkeLebesgue.ProjectiveCurvature

/-! # Permuting contact labels preserves the actual clipped bodies -/

public noncomputable section

namespace BlaschkeLebesgue.BalancedContacts

variable (c : BalancedContacts 4 Space)

theorem range_point_relabel (e : Equiv.Perm (Fin 4)) : Set.range (c.relabel e).point = Set.range c.point := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp only [relabel, e.apply_symm_apply]⟩

theorem clippedOuter_relabel (e : Equiv.Perm (Fin 4)) :
    clippedOuter (c.relabel e).radius (Set.range (c.relabel e).point) =
      clippedOuter c.radius (Set.range c.point) := by
  rw [range_point_relabel]
  rfl

theorem clippedOuterBody_relabel (e : Equiv.Perm (Fin 4))
    (hne' : (clippedOuter (c.relabel e).radius (Set.range (c.relabel e).point)).Nonempty)
    (hne : (clippedOuter c.radius (Set.range c.point)).Nonempty) :
    clippedOuterBody (c.relabel e).radius (Set.range (c.relabel e).point) hne' =
      clippedOuterBody c.radius (Set.range c.point) hne := by
  apply SetLike.ext
  intro x
  change x ∈ clippedOuter (c.relabel e).radius (Set.range (c.relabel e).point) ↔ _
  rw [clippedOuter_relabel]
  rfl

theorem clippedInnerBody_relabel (e : Equiv.Perm (Fin 4))
    (hne' : (clippedOuter (c.relabel e).radius (Set.range (c.relabel e).point)).Nonempty)
    (hne : (clippedOuter c.radius (Set.range c.point)).Nonempty)
    (hbound' : (c.relabel e).radius ≤ 1) (hbound : c.radius ≤ 1) :
    clippedInnerBody (c.relabel e).radius (Set.range (c.relabel e).point) hne' hbound' =
      clippedInnerBody c.radius (Set.range c.point) hne hbound := by
  apply SetLike.ext
  intro x
  change x ∈ ballTransform (clippedOuterBody (c.relabel e).radius (Set.range (c.relabel e).point) hne' : Set Space) ↔
    x ∈ ballTransform (clippedOuterBody c.radius (Set.range c.point) hne : Set Space)
  rw [clippedOuterBody_relabel]

@[expose] def supportContactLabels (C : ConvexBody Space) (n : Space) : Set (Fin 4) :=
  {i | ‖normalSupport C n - c.point i‖ = 1}

theorem supportContactLabels_relabel (e : Equiv.Perm (Fin 4)) (C : ConvexBody Space) (n : Space) :
    supportContactLabels (c.relabel e) C n = e ⁻¹' supportContactLabels c C n := rfl

theorem image_supportContactLabels_relabel (e : Equiv.Perm (Fin 4)) (C : ConvexBody Space) (n : Space) :
    e '' supportContactLabels (c.relabel e) C n = supportContactLabels c C n := by
  rw [supportContactLabels_relabel]
  exact Set.image_preimage_eq _ e.surjective

end BlaschkeLebesgue.BalancedContacts
