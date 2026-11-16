module

public import BlaschkeLebesgue.FrameProductCoordinates
public import BlaschkeLebesgue.PolarHomogeneous

/-! # Integrating a homogeneous function over a projective cone -/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue.ObliqueFrame

variable (f : ObliqueFrame)

@[expose] def projectiveSector (s : Set (ℝ × ℝ)) : Set Space :=
  {q | 0 < ⟪f.normal, q⟫_ℝ ∧ f.projectiveCoordinates q ∈ s}

@[expose] def projectiveCone (s : Set (ℝ × ℝ)) : Set Space := ball 0 1 ∩ f.projectiveSector s

@[expose] def projectiveConeParameters (s : Set (ℝ × ℝ)) : Set Space :=
  {p | ⟪f.normal, p⟫_ℝ ∈ Ioo (0 : ℝ) 1 ∧ (⟪f.axis₁, p⟫_ℝ, ⟪f.transverse₁, p⟫_ℝ) ∈ s}

theorem measurable_projectiveCoordinates : Measurable f.projectiveCoordinates := by
  unfold projectiveCoordinates
  fun_prop

theorem measurableSet_projectiveSector {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (f.projectiveSector s) := by
  change MeasurableSet ({q : Space | (0 : ℝ) < ⟪f.normal, q⟫_ℝ} ∩ f.projectiveCoordinates ⁻¹' s)
  exact (isOpen_lt continuous_const (continuous_const.inner continuous_id)).measurableSet.inter
    (hs.preimage f.measurable_projectiveCoordinates)

theorem measurableSet_projectiveConeParameters {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (f.projectiveConeParameters s) :=
  (isOpen_Ioo.preimage (continuous_const.inner continuous_id)).measurableSet.inter
    (hs.preimage ((continuous_const.inner continuous_id).prodMk (continuous_const.inner continuous_id)).measurable)

theorem projectiveSector_smul_iff (s : Set (ℝ × ℝ)) (q : Space) {r : ℝ} (hr : 0 < r) :
    r • q ∈ f.projectiveSector s ↔ q ∈ f.projectiveSector s := by
  simp only [projectiveSector, mem_ofPred_eq, real_inner_smul_right,
    f.projectiveCoordinates_smul q hr.ne', mul_pos_iff_of_pos_left hr]

theorem radialProjectiveMap_image_cone (s : Set (ℝ × ℝ)) :
    f.radialProjectiveMap '' f.projectiveConeParameters s = f.projectiveCone s := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpos : 0 < ⟪f.normal, p⟫_ℝ := hp.1.1
    refine ⟨?_, f.radialProjectiveMap_normal_pos hpos, ?_⟩
    · rw [mem_ball, dist_zero_right, f.radialProjectiveMap_norm hpos]
      exact hp.1.2
    · rw [f.radialProjectiveMap_coordinates hpos]
      exact hp.2
  · rintro ⟨hqn, hqz, hqs⟩
    have hq0 : q ≠ 0 := by intro h; simp [h] at hqz
    have hnorm : ‖q‖ ∈ Ioo (0 : ℝ) 1 := ⟨norm_pos_iff.2 hq0, by simpa using hqn⟩
    refine ⟨f.radialPoint ‖q‖ (f.projectiveCoordinates q).1 (f.projectiveCoordinates q).2, ?_, ?_⟩
    · change _ ∈ Ioo (0 : ℝ) 1 ∧ _ ∈ s
      rw [f.normal_inner_radialPoint, f.axis₁_inner_radialPoint, f.transverse₁_inner_radialPoint,
        Prod.mk.eta]
      exact ⟨hnorm, hqs⟩
    · rw [f.radialProjectiveMap_radialPoint, f.projectiveNormal_coordinates_normalize hqz,
        NormedSpace.normalize, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hq0), one_smul]

theorem integral_projectiveCone {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (g : Space → ℝ)
    (hg : ∀ r : ℝ, 0 < r → ∀ q, g (r • q) = g q) :
    (∫ q in f.projectiveCone s, g q) =
      (∫ q in s, g (f.projectiveNormal q.1 q.2) / (f.sine * Real.sqrt (f.W q.1 q.2) ^ 3)) / 3 := by
  have hparams := f.measurableSet_projectiveConeParameters hs
  have hpos : f.projectiveConeParameters s ⊆ {p : Space | 0 < ⟪f.normal, p⟫_ℝ} := fun _ hp ↦ hp.1.1
  rw [← f.radialProjectiveMap_image_cone, f.integral_image_radialProjectiveMap hparams hpos]
  calc
    _ = ∫ p in f.projectiveConeParameters s, ⟪f.normal, p⟫_ℝ ^ 2 *
        (g (f.projectiveNormal ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ) /
          (f.sine * Real.sqrt (f.W ⟪f.axis₁, p⟫_ℝ ⟪f.transverse₁, p⟫_ℝ) ^ 3)) := by
      apply setIntegral_congr_fun hparams
      intro p hp
      dsimp only
      rw [f.radialProjectiveMap_eq, hg _ hp.1.1]
      ring
    _ = (∫ r in Ioo (0 : ℝ) 1, r ^ 2) *
        ∫ q in s, g (f.projectiveNormal q.1 q.2) / (f.sine * Real.sqrt (f.W q.1 q.2) ^ 3) :=
      f.integral_frame_product (Ioo (0 : ℝ) 1) s (fun r ↦ r ^ 2)
        (fun q ↦ g (f.projectiveNormal q.1 q.2) / (f.sine * Real.sqrt (f.W q.1 q.2) ^ 3))
    _ = _ := by
      have hrad : (∫ r in Ioo (0 : ℝ) 1, r ^ 2) = (1 / 3 : ℝ) := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num [integral_pow]
      rw [hrad]
      ring

end BlaschkeLebesgue.ObliqueFrame
