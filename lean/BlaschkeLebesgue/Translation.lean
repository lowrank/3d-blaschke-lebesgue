module

public import BlaschkeLebesgue.EnclosingBall
public import BlaschkeLebesgue.Target

/-! # Translation of actual convex bodies, support functions, and volume -/

public noncomputable section

open scoped InnerProductSpace

namespace BlaschkeLebesgue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Translation of a convex body by a vector. -/
@[expose] def translateBody (K : ConvexBody E) (v : E) : ConvexBody E where
  carrier := (fun x ↦ v + x) '' (K : Set E)
  convex' := K.convex.translate v
  isCompact' := K.isCompact.image (by fun_prop)
  nonempty' := K.nonempty.image _

@[simp] theorem mem_translateBody (K : ConvexBody E) (v x : E) :
    x ∈ translateBody K v ↔ x - v ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [add_sub_cancel_left, SetLike.mem_coe] using hy
  · intro hx
    exact ⟨x - v, hx, by abel_nf⟩

theorem support_translateBody (K : ConvexBody E) (v n : E) :
    support (translateBody K v) n = ⟪n, v⟫_ℝ + support K n := by
  apply le_antisymm
  · apply (support_le_iff _ _ _).2
    rintro x ⟨y, hy, rfl⟩
    rw [inner_add_right]
    exact add_le_add le_rfl (inner_le_support K n hy)
  · obtain ⟨x, hx, hmax, _⟩ := exists_support_point K n
    have hx' : v + x ∈ translateBody K v := ⟨x, hx, rfl⟩
    simpa only [inner_add_right, hmax] using inner_le_support (translateBody K v) n hx'

theorem HasConstantWidth.translateBody {K : ConvexBody E} {w : ℝ}
    (hK : HasConstantWidth K w) (v : E) : HasConstantWidth (translateBody K v) w := by
  intro n hn
  rw [support_translateBody, support_translateBody, inner_neg_left]
  linarith [hK n hn]

theorem enclosingRadius_translateBody (K : ConvexBody E) (v c : E) :
    enclosingRadius (translateBody K v) c = enclosingRadius K (c - v) := by
  apply le_antisymm
  · apply (enclosingRadius_le_iff _ _ _).2
    rintro x ⟨y, hy, rfl⟩
    have hid : v + y - c = y - (c - v) := by abel
    rw [hid]
    exact norm_sub_le_enclosingRadius K (c - v) hy
  · apply (enclosingRadius_le_iff _ _ _).2
    intro x hx
    have hx' : v + x ∈ translateBody K v := ⟨x, hx, rfl⟩
    have hid : v + x - c = x - (c - v) := by abel
    simpa only [hid] using norm_sub_le_enclosingRadius (translateBody K v) c hx'

/-- Ordinary Lebesgue volume is unchanged by translation. -/
theorem bodyVolume_translateBody (K : ConvexBody Space) (v : Space) :
    bodyVolume (translateBody K v) = bodyVolume K := by
  have hset : (translateBody K v : Set Space) = (fun x ↦ -v + x) ⁻¹' (K : Set Space) := by
    ext x
    simp only [SetLike.mem_coe, mem_translateBody, Set.mem_preimage]
    abel_nf
  unfold bodyVolume
  rw [hset, MeasureTheory.measure_preimage_add]

namespace MinimumEnclosingBall

variable {K : ConvexBody E} (b : MinimumEnclosingBall K)

/-- Place the minimum enclosing center at the origin. -/
@[expose] def centeredBody : ConvexBody E := translateBody K (-b.center)

theorem centeredBody_width (hK : HasConstantWidth K 1) : HasConstantWidth b.centeredBody 1 :=
  hK.translateBody (-b.center)

theorem centeredBody_norm_le {x : E} (hx : x ∈ b.centeredBody) : ‖x‖ ≤ b.radius := by
  have hx' : x + b.center ∈ K := by simpa [centeredBody] using hx
  simpa using b.norm_sub_center_le hx'

/-- The translated ball is still a minimum enclosing ball, now centered at zero. -/
@[expose] def centeredBall : MinimumEnclosingBall b.centeredBody where
  center := 0
  radius := b.radius
  radius_eq := by simp only [centeredBody, enclosingRadius_translateBody, zero_sub, neg_neg,
    b.radius_eq]
  minimal := fun c ↦ by
    rw [centeredBody, enclosingRadius_translateBody]
    exact b.minimal _

end MinimumEnclosingBall

end BlaschkeLebesgue
