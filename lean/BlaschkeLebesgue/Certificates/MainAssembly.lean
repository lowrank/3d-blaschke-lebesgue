module

public import BlaschkeLebesgue.Certificates.NearBranchAssembly
public import BlaschkeLebesgue.Certificates.RadialVolume
public import BlaschkeLebesgue.Normalization

/-! # Reduction of the full geometric target to the finite kernel certificates

No computational premise is an axiom. The unconditional main theorem requires
all of these premises to be discharged by the generated kernel suites.
-/

public noncomputable section

namespace BlaschkeLebesgue.Certificates

open ClippedHull

variable
    (checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true)
    (baselineChecks : ∀ i : Fin 32, baselineSignCheck 128 64 i 32 = true)
    (secantChecks : ∀ i : Fin 512, secantCheck 128 64 i 512 = true)
    (affine : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 2 / 25 →
      153 / 100000 - 601 / 100000 * a + 317 / 20000 * b < Completion.F a b)
include checks baselineChecks secantChecks affine

theorem unitWidthVolumeBound_of_certificates : UnitWidthVolumeBound := by
  intro K _ hK
  obtain ⟨L, b, hL, hb, _, _, _, hvol⟩ := exists_centered_unit_body (by norm_num : (0 : ℝ) < 1) hK
  norm_num at hvol
  suffices h : (259 / 625 : ℝ) < bodyVolume L by rwa [hvol] at h
  by_cases hR : b.radius ≤ 60849 / 100000
  · exact b.volume_gt_of_radius_le_radial_cutoff hL hR
  · have hR' : 60849 / 100000 ≤ b.radius := (lt_of_not_ge hR).le
    obtain ⟨c, _⟩ := b.exists_contacts_with_deficit_budget hL hR'
    apply c.toBalancedContacts.near_volume_bound_of_certificates checks baselineChecks secantChecks affine hL
    · rintro _ ⟨i, rfl⟩
      change c.point i ∈ L
      simpa only [hb, add_zero] using c.point_mem i
    · intro p hp
      rw [c.radius_eq, b.radius_eq]
      have hh := norm_sub_le_enclosingRadius L b.center hp
      simpa only [hb, sub_zero] using hh
    · simpa only [c.radius_eq] using hR'

theorem constantWidthVolumeBound_of_certificates : ConstantWidthVolumeBound :=
  unitWidthVolumeBound_iff.mp (unitWidthVolumeBound_of_certificates checks baselineChecks secantChecks affine)

end BlaschkeLebesgue.Certificates
