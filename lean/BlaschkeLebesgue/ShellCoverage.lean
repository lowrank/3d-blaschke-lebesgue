module

public import BlaschkeLebesgue.ShellInjectivity

/-!
# The shell parametrization covers the actual region

For a point between the two endpoint bodies, maximize its normalized support
deficit over the sphere. The maximizing ratio is an interpolation time in
`[0,1]`; it gives membership in that intermediate body and equality at a
supporting plane. Uniqueness of support points identifies the point exactly.
-/

public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def bodyShell (D K : ConvexBody Space) (ε δ : ℝ) : Set Space :=
  (parallelBody K (ε + δ) : Set Space) \ interior (parallelBody D ε : Set Space)

theorem shellPoint_mem_bodyShell {D K : ConvexBody Space}
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ t : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (ht : t ∈ Icc (0 : ℝ) 1)
    {u : Space} (hu : ‖u‖ = 1) : shellPoint D K ε δ t u ∈ bodyShell D K ε δ := by
  constructor
  · apply (mem_iff_unit_inner_le_support (parallelBody K (ε + δ)) _).2
    intro v hv
    have hi := inner_le_support (shellBody D K ε δ t) v (shellPoint_mem D K ε δ t hu)
    rw [support_shellBody D K hε hδ ht hv] at hi
    rw [support_parallelBody K (add_nonneg hε hδ) hv]
    have hg := add_nonneg (sub_nonneg.2 (support_mono_of_subset hDK v)) hδ
    nlinarith only [hi, mul_nonneg (sub_nonneg.2 ht.2) hg]
  · intro hx
    have hi := inner_lt_support_of_mem_interior (parallelBody D ε) hx hu
    rw [inner_shellPoint D K hε hδ ht hu, support_shellBody D K hε hδ ht hu,
      support_parallelBody D hε hu] at hi
    have hg := add_nonneg (sub_nonneg.2 (support_mono_of_subset hDK u)) hδ
    linarith only [hi, mul_nonneg ht.1 hg]

/-- Every point of the actual closed shell occurs at a supporting point of an intermediate body. -/
theorem exists_shellPoint_eq {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) {x : Space} (hx : x ∈ bodyShell D K ε δ) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ u : UnitSphere, x = shellPoint D K ε δ t u := by
  let g : UnitSphere → ℝ := fun u => support K u - support D u + δ
  have hg (u : UnitSphere) : 0 < g u := by
    dsimp only [g]
    linarith only [support_mono_of_subset hDK u, hδ]
  let q : UnitSphere → ℝ := fun u => (⟪(u : Space), x⟫_ℝ - support D u - ε) / g u
  have hqc : Continuous q :=
    ((continuous_subtype_val.inner continuous_const).sub (continuous_support_sphere hD)
      |>.sub continuous_const).div
      (((continuous_support_sphere hK).sub (continuous_support_sphere hD)).add continuous_const)
      (fun u => (hg u).ne')
  have hne : (univ : Set UnitSphere).Nonempty := by
    let b := EuclideanSpace.basisFun (Fin 3) ℝ
    exact ⟨⟨b 0, by simp only [mem_sphere, dist_zero_right, b.norm_eq_one]⟩, mem_univ _⟩
  obtain ⟨u, _, hmax⟩ := isCompact_univ.exists_isMaxOn hne hqc.continuousOn
  let t := q u
  have hmax' (v : UnitSphere) : ⟪(v : Space), x⟫_ℝ - support D v - ε ≤ t * g v :=
    (div_le_iff₀ (hg v)).1 (hmax (mem_univ v))
  have ht1 : t ≤ 1 := by
    have hi := inner_le_support (parallelBody K (ε + δ)) (u : Space) hx.1
    rw [support_parallelBody K (add_nonneg hε hδ.le) u.norm_eq_one] at hi
    change (⟪(u : Space), x⟫_ℝ - support D u - ε) / g u ≤ 1
    apply (div_le_iff₀ (hg u)).2
    dsimp only [g]
    linarith only [hi]
  have ht0 : 0 ≤ t := by
    by_contra ht
    have htneg : t < 0 := lt_of_not_ge ht
    apply hx.2
    apply mem_interior_of_support_margin (parallelBody D ε) (r := -t * δ) (mul_pos (neg_pos.2 htneg) hδ)
    intro v hv
    let v' : UnitSphere := ⟨v, by simpa only [mem_sphere, dist_zero_right] using hv⟩
    have hm := hmax' v'
    have hgd : δ ≤ g v' := by
      dsimp only [g]
      linarith only [support_mono_of_subset hDK v]
    have hgneg := mul_le_mul_of_nonpos_left hgd htneg.le
    rw [support_parallelBody D hε hv]
    change ⟪v, x⟫_ℝ - support D v - ε ≤ t * g v' at hm
    linarith only [hm, hgneg]
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hxt : x ∈ shellBody D K ε δ t := by
    apply (mem_iff_unit_inner_le_support _ x).2
    intro v hv
    let v' : UnitSphere := ⟨v, by simpa only [mem_sphere, dist_zero_right] using hv⟩
    have hm := hmax' v'
    rw [support_shellBody D K hε hδ.le ht hv]
    change ⟪v, x⟫_ℝ - support D v - ε ≤ t * (support K v - support D v + δ) at hm
    linarith only [hm]
  have hsupport : ⟪(u : Space), x⟫_ℝ = support (shellBody D K ε δ t) u := by
    rw [support_shellBody D K hε hδ.le ht u.norm_eq_one]
    have he : t * g u = ⟪(u : Space), x⟫_ℝ - support D u - ε := by
      dsimp only [t, q]
      exact div_mul_cancel₀ _ (hg u).ne'
    dsimp only [g] at he
    linarith only [he]
  exact ⟨t, ht, u, shellPoint_unique hD hK hε hδ.le ht u.norm_eq_one hxt hsupport⟩

theorem shellPoint_image {D D' K K' : ConvexBody Space}
    (hD : D + D' = unitBallBody) (hK : K + K' = unitBallBody)
    (hDK : (D : Set Space) ⊆ (K : Set Space)) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) :
    (fun p : ℝ × UnitSphere => shellPoint D K ε δ p.1 p.2) '' (Icc (0 : ℝ) 1 ×ˢ univ) =
      bodyShell D K ε δ := by
  ext x
  constructor
  · rintro ⟨⟨t, u⟩, hp, rfl⟩
    exact shellPoint_mem_bodyShell hDK hε hδ.le hp.1 u.norm_eq_one
  · intro hx
    obtain ⟨t, ht, u, he⟩ := exists_shellPoint_eq hD hK hDK hε hδ hx
    exact ⟨(t, u), ⟨ht, mem_univ _⟩, he.symm⟩

end BlaschkeLebesgue
