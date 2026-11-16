module

public import BlaschkeLebesgue.ClippedScalarDomain

/-! # The manuscript edge formulas in squared edge-length coordinates -/

public noncomputable section

namespace BlaschkeLebesgue.ClippedDifferential

theorem U_eq_unitFaceAngle {R x : ℝ} (hx : 0 ≤ x) :
    U R x = ClippedEdge.unitFaceAngle R (Real.sqrt x) := by
  simp only [U, ClippedEdge.unitFaceAngle, s, ClippedEdge.radius, r, k, Real.sq_sqrt hx]

theorem V_eq_radiusFaceAngle {R x : ℝ} (hR : 1 / 2 < R) (hx : 0 ≤ x) :
    V R x = ClippedEdge.radiusFaceAngle R (Real.sqrt x) := by
  have hk : k R ≠ 0 := (ClippingCircle.radius_pos hR).ne'
  unfold V ClippedEdge.radiusFaceAngle
  rw [Real.sq_sqrt hx]
  change Real.arccos ((2 * k R ^ 2 - x) / (2 * k R ^ 2)) =
    Real.arccos (1 - x / (2 * k R ^ 2))
  congr 1
  field_simp

theorem Psi_eq_cutAngle {R x : ℝ} (hx : 0 ≤ x) :
    Psi R x = ClippedEdge.cutAngle R (Real.sqrt x) := by
  simp only [Psi, ClippedEdge.cutAngle, s, ClippedEdge.midpointNorm, m, k, Real.sq_sqrt hx]

theorem phi_eq_arcAngle {R x : ℝ} (hx : 0 ≤ x) :
    phi R x = ClippedEdge.arcAngle R (Real.sqrt x) := by
  simp only [phi, ClippedEdge.arcAngle, ClippedEdge.radius, r, ClippedEdge.midpointNorm, m,
    Real.sq_sqrt hx]

theorem T_eq_radical {R x : ℝ} (hx : 0 ≤ x) :
    T R x = ClippedEdge.radical R (Real.sqrt x) := by
  simp only [T, ClippedEdge.radical, s, q, Real.sq_sqrt hx]

theorem F_eq_smallF {x : ℝ} (hx : 0 ≤ x) : F x = ClippedFormula.smallF (Real.sqrt x) := by
  simp only [F, ClippedFormula.smallF, s, theta, r, ClippedEdge.radius, Real.sq_sqrt hx]

@[expose] def outer (R x : ℝ) : ℝ :=
  (-4 * U R x - 2 * R ^ 3 * V R x + (-3 * s x / 2 + s x ^ 3 / 8) * phi R x +
    T R x / 2 + (4 * R ^ 3 + 3 / (2 * R)) * Psi R x) / 3

@[expose] def inner (R x : ℝ) : ℝ :=
  4 / 3 * U R x - 2 * ClippedFormula.z R * V R x + phi R x * F x - T R x / 6 -
    4 * ClippedFormula.b R * Psi R x

@[expose] def outerDx (R x : ℝ) : ℝ :=
  (2 - x) * q R x / (4 * s x * (4 * R ^ 2 - x)) - (4 - x) * phi R x / (16 * s x)

@[expose] def innerDx (R x : ℝ) : ℝ :=
  phi R x * (-s x / 16 + theta x / (8 * r x)) +
    (x + 6 - 8 * R) * q R x / (4 * s x * (4 * R ^ 2 - x)) -
    (6 * R ^ 2 - R ^ 2 * x - 2) * theta x / (2 * r x * q R x * (4 * R ^ 2 - x)) -
    (2 * R * k R) * (1 - 2 * R ^ 2) * ClippedEdge.normalAngle R /
      (s x * q R x * (4 * R ^ 2 - x))

@[expose] def combinedDx (R x : ℝ) : ℝ := (47 * innerDx R x - outerDx R x) / 46

theorem outer_eq_manuscript {R x : ℝ} (hR : 1 / 2 < R) (hx : 0 ≤ x) :
    outer R x = ClippedFormula.outerEdge R (1 - x) := by
  rw [ClippedFormula.outerEdge, sub_sub_cancel]
  unfold outer ClippedFormula.outerEdgeLength
  rw [U_eq_unitFaceAngle hx, V_eq_radiusFaceAngle hR hx, phi_eq_arcAngle hx,
    T_eq_radical hx, Psi_eq_cutAngle hx]
  rfl

theorem inner_eq_manuscript {R x : ℝ} (hR : 1 / 2 < R) (hx : 0 ≤ x) :
    inner R x = ClippedFormula.innerEdge R (1 - x) := by
  rw [ClippedFormula.innerEdge, sub_sub_cancel]
  unfold inner ClippedFormula.innerEdgeLength
  rw [U_eq_unitFaceAngle hx, V_eq_radiusFaceAngle hR hx, phi_eq_arcAngle hx,
    F_eq_smallF hx, T_eq_radical hx, Psi_eq_cutAngle hx]

end BlaschkeLebesgue.ClippedDifferential
