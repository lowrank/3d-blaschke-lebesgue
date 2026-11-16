module

public import BlaschkeLebesgue.NormalDerivative
public import BlaschkeLebesgue.RadialVolume

/-!
# Almost-everywhere support derivatives on the sphere

Degree-zero homogeneity transports differentiability along each positive ray.
Consequently the exceptional directions form a cone of ambient measure zero;
the defining cone formula for spherical measure gives spherical measure zero.
-/

public noncomputable section

open MeasureTheory Set NormedSpace Filter Topology
open scoped InnerProductSpace Pointwise

namespace BlaschkeLebesgue

theorem normalSupport_hasFDerivAt_smul {K : ConvexBody Space} {x : Space}
    {A : Space →L[ℝ] Space} (hd : HasFDerivAt (normalSupport K) A x)
    {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (normalSupport K) (r⁻¹ • A) (r • x) := by
  have hd' : HasFDerivAt (normalSupport K) A (r⁻¹ • (r • x)) := by
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using hd
  have h := hd'.comp (r • x) ((hasFDerivAt_id (r • x)).const_smul r⁻¹)
  simpa only [Function.comp_def, normalSupport_smul K (inv_pos.2 hr),
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using h

theorem normalSupport_differentiableAt_smul_iff (K : ConvexBody Space) (x : Space)
    {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (normalSupport K) (r • x) ↔
      DifferentiableAt ℝ (normalSupport K) x := by
  constructor
  · intro hd
    have h := (normalSupport_hasFDerivAt_smul hd.hasFDerivAt (inv_pos.2 hr)).differentiableAt
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using h
  · intro hd
    exact (normalSupport_hasFDerivAt_smul hd.hasFDerivAt hr).differentiableAt

/-- The actual support map is differentiable at almost every unit normal. -/
theorem normalSupport_sphere_ae_differentiable {K L : ConvexBody Space}
    (hKL : K + L = unitBallBody) :
    ∀ᵐ u : UnitSphere ∂sphereMeasure, DifferentiableAt ℝ (normalSupport K) (u : Space) := by
  rw [ae_iff]
  have hm : MeasurableSet {u : UnitSphere | ¬DifferentiableAt ℝ (normalSupport K) (u : Space)} :=
    (measurableSet_of_differentiableAt ℝ (normalSupport K)).compl.preimage measurable_subtype_coe
  rw [sphereMeasure, Measure.toSphere_apply' _ hm]
  have hn : volume {x : Space | ¬DifferentiableAt ℝ (normalSupport K) x} = 0 :=
    ae_iff.1 (normalSupport_ae_differentiable hKL)
  have hc : Ioo (0 : ℝ) 1 • (Subtype.val ''
      {u : UnitSphere | ¬DifferentiableAt ℝ (normalSupport K) (u : Space)}) ⊆
      {x : Space | ¬DifferentiableAt ℝ (normalSupport K) x} := by
    rintro _ ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩ hd
    exact hu ((normalSupport_differentiableAt_smul_iff K u hr.1).1 hd)
  rw [measure_mono_null hc hn, mul_zero]

end BlaschkeLebesgue
