module

public import BlaschkeLebesgue.ProjectiveCone

/-!
# The actual spherical change of variables for the projective chart

Polar integration and the radial chart have the same radial factor `1/3`.
Cancelling it identifies the explicit planar density with spherical area.
-/

public noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace

namespace BlaschkeLebesgue

@[expose] def sphereExtension (h : UnitSphere → ℝ) (x : Space) : ℝ :=
  if hx : x = 0 then 0 else h ⟨NormedSpace.normalize x, by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩

theorem sphereExtension_smul (h : UnitSphere → ℝ) {r : ℝ} (hr : 0 < r) (x : Space) :
    sphereExtension h (r • x) = sphereExtension h x := by
  by_cases hx : x = 0
  · simp only [hx, smul_zero]
  · have hrx : r • x ≠ 0 := smul_ne_zero hr.ne' hx
    simp only [sphereExtension, dite_eq_right hx, dite_eq_right hrx]
    congr 1
    apply Subtype.ext
    exact NormedSpace.normalize_smul_of_pos hr x

theorem sphereExtension_unit (h : UnitSphere → ℝ) (u : UnitSphere) : sphereExtension h u = h u := by
  rw [sphereExtension, dite_eq_right u.ne_zero]
  congr 1
  apply Subtype.ext
  exact NormedSpace.normalize_eq_self_of_norm_eq_one u.norm_eq_one

namespace ObliqueFrame

variable (f : ObliqueFrame)

@[expose] def projectivePatch (s : Set (ℝ × ℝ)) : Set UnitSphere :=
  (Subtype.val : UnitSphere → Space) ⁻¹' f.projectiveSector s

theorem measurableSet_projectivePatch {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (f.projectivePatch s) :=
  (f.measurableSet_projectiveSector hs).preimage measurable_subtype_coe

theorem projectiveUnitNormal_mem_patch_iff (s : Set (ℝ × ℝ)) (x y : ℝ) :
    f.projectiveUnitNormal x y ∈ f.projectivePatch s ↔ (x, y) ∈ s := by
  change 0 < ⟪f.normal, f.projectiveNormal x y⟫_ℝ ∧ f.projectiveCoordinates (f.projectiveNormal x y) ∈ s ↔ _
  rw [f.normal_inner_projectiveNormal, f.projectiveCoordinates_normal,
    and_iff_right (inv_pos.2 (Real.sqrt_pos.2 (f.W_pos x y)))]

theorem projectivePatch_eq_image (s : Set (ℝ × ℝ)) :
    f.projectivePatch s = (fun q : ℝ × ℝ ↦ f.projectiveUnitNormal q.1 q.2) '' s := by
  ext u
  constructor
  · intro hu
    refine ⟨f.projectiveCoordinates u, hu.2, ?_⟩
    apply Subtype.ext
    exact f.projectiveNormal_coordinates u.norm_eq_one hu.1
  · rintro ⟨q, hq, rfl⟩
    exact (f.projectiveUnitNormal_mem_patch_iff s q.1 q.2).2 hq

theorem projectivePatch_disjoint_antipode (s t : Set (ℝ × ℝ)) :
    Disjoint (f.projectivePatch s) (sphereAntipode '' f.projectivePatch t) := by
  apply Set.disjoint_left.2
  intro u hu hv
  rcases hv with ⟨v, hv, rfl⟩
  have h1 : 0 < ⟪f.normal, ((sphereAntipode v) : Space)⟫_ℝ := hu.1
  have h2 : 0 < ⟪f.normal, (v : Space)⟫_ℝ := hv.1
  rw [sphereAntipode_val, inner_neg_right] at h1
  linarith

theorem projectiveSector_indicator_smul (s : Set (ℝ × ℝ)) (g : Space → ℝ)
    (hg : ∀ r : ℝ, 0 < r → ∀ q, g (r • q) = g q) {r : ℝ} (hr : 0 < r) (q : Space) :
    (f.projectiveSector s).indicator g (r • q) = (f.projectiveSector s).indicator g q := by
  by_cases hq : q ∈ f.projectiveSector s
  · rw [indicator_of_mem hq, indicator_of_mem ((f.projectiveSector_smul_iff s q hr).2 hq), hg r hr]
  · rw [indicator_of_notMem hq,
      indicator_of_notMem (fun h ↦ hq ((f.projectiveSector_smul_iff s q hr).1 h))]

theorem integral_projectivePatch_homogeneous {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (g : Space → ℝ)
    (hg : ∀ r : ℝ, 0 < r → ∀ q, g (r • q) = g q) :
    (∫ u in f.projectivePatch s, g (u : Space) ∂sphereMeasure) =
      ∫ q in s, g (f.projectiveNormal q.1 q.2) / (f.sine * Real.sqrt (f.W q.1 q.2) ^ 3) := by
  have h := integral_ball_homogeneous_zero ((f.projectiveSector s).indicator g)
    (fun r hr q ↦ f.projectiveSector_indicator_smul s g hg hr q)
  rw [setIntegral_indicator (f.measurableSet_projectiveSector hs)] at h
  have he : (fun u : UnitSphere ↦ (f.projectiveSector s).indicator g (u : Space)) =
      (f.projectivePatch s).indicator (fun u : UnitSphere ↦ g (u : Space)) := by
    funext u
    by_cases hu : u ∈ f.projectivePatch s
    · rw [indicator_of_mem hu, indicator_of_mem (show (u : Space) ∈ f.projectiveSector s from hu)]
    · rw [indicator_of_notMem hu, indicator_of_notMem (show (u : Space) ∉ f.projectiveSector s from hu)]
  rw [he, integral_indicator (f.measurableSet_projectivePatch hs)] at h
  change (∫ q in f.projectiveCone s, g q) = _ at h
  rw [f.integral_projectiveCone hs g hg] at h
  linarith only [h]

/-- The projective area formula, for the sphere measure defined from ordinary
Lebesgue volume. It includes integrability's usual Bochner convention. -/
theorem integral_projectivePatch {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (h : UnitSphere → ℝ) :
    (∫ u in f.projectivePatch s, h u ∂sphereMeasure) =
      ∫ q in s, h (f.projectiveUnitNormal q.1 q.2) / (f.sine * Real.sqrt (f.W q.1 q.2) ^ 3) := by
  have he := f.integral_projectivePatch_homogeneous hs (sphereExtension h)
    (fun _ hr x ↦ sphereExtension_smul h hr x)
  simp_rw [sphereExtension_unit] at he
  convert he using 1
  apply setIntegral_congr_fun hs
  intro q _
  dsimp only
  rw [show f.projectiveNormal q.1 q.2 = (f.projectiveUnitNormal q.1 q.2 : Space) from rfl,
    sphereExtension_unit]

end ObliqueFrame
end BlaschkeLebesgue
