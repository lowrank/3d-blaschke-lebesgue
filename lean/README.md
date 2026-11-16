# Lean 4.35 formalization

**Status: incomplete. The manuscript's volume theorem has not yet been proved in Lean.**

Source: `volume_bound_04144.tex` at upstream commit
`8e57642c283f232ae9a782ad86408bfb7182dfb0`. The target is the strict bound
`Vol(K) > (259/625) * w^3` for three-dimensional convex bodies of constant width
`w > 0`. `BlaschkeLebesgue.ConstantWidthVolumeBound` records this statement using
Lebesgue volume, compact convex sets, nonempty interior, and opposite support
functions. It is a proposition definition, not a proved theorem.

The completion criterion is an end-to-end proof of this proposition, with no
`sorry`, custom axioms, or unproved geometric interfaces. Intermediate milestones
do not satisfy that criterion.

## Build and audit

From this directory:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
python3 scripts/generate_radial.py --check
```

Lean is pinned to **4.35.0**, and mathlib to its matching release
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Lake's local artifact cache is enabled;
restored build files use hard links to the shared cache rather than independent
copies. No machine-specific dependency paths are committed.

CI runs the build, audits all declarations in the `BlaschkeLebesgue` namespace,
checks generated candidate provenance, and checks the existing manuscript report provenance.
The axiom audit permits
only `propext`, `Classical.choice`, and `Quot.sound`; it rejects placeholders,
custom axioms, and native-evaluation axioms. CI passing certifies the implemented
lemmas, not the unproved main proposition.

## Milestone 1: support functions and unit-ball duality

`BlaschkeLebesgue/Basic.lean` proves:

- support maxima exist and characterize membership in a compact convex set;
- positive dilation scales support functions and constant width;
- constant width bounds every pairwise distance;
- the point opposite a unit-width support point belongs to the body;
- a unit-width body equals its unit-ball transform;
- an outer approximation gives a forced inner approximation;
- the opposite-point property gives the radial normal inequality.

These are geometric statements about actual sets in real inner product spaces.
Their hypotheses do not contain the volume conclusion.

## Milestone 2: contacts, radial algebra, and normalization

`Contacts.lean` proves the squared-radius bound `R^2 ≤ 3/8`, the exact centroid
and weighted-deficit identities, and the two-sided deficit budget, including
`A < 2/25` when `R ≥ 60849/100000`. Its input is a finite collection of actual
points on a sphere with balancing weights and diameter at most one. Milestone 4
constructs these contacts from the original convex body.

`Radial.lean` proves the tangent majorant by an exact factorization, the soundness
of the squared rational positive- and negative-cap tests, the rational unit-circle
identity, and the low-radius numerical consequence of the scalar master inequality.
The master inequality itself is not assumed as a global axiom or claimed as proved.

`Target.lean` proves that dilation scales Lebesgue volume by the cube and that the
unit-width target is equivalent to the full-width target, including preservation
of nonempty interior. Both target propositions remain unproved.

## Milestone 3: exact radial arithmetic and further analytic lemmas

`Certificates/RadialRows.lean` assembles **eight kernel-checked arithmetic rows**:
5,836 positive propagation tests and 14,814 negative-cap tests. Each generated
`Row*.verified` theorem evaluates the rational checker using `decide +kernel`.
No `native_decide`, external oracle, report status, or trusted generator is used.
The checker recomputes separation tests, ordering conditions, radical inequalities,
downward-rounded ring contributions, and the final coefficient. It also verifies
that the recomputed coefficient equals the coefficient recorded in the candidate
input. The input coefficient is therefore checked data, not a premise.

`RadialSoundness.lean` proves that downward rounding is conservative, the accepted
squared tests imply the real square-root inequalities, and each accepted row has
real value `pi * coefficient > 4144109/10000000`. This uses mathlib's proved
20-decimal lower bound for pi instead of assuming the manuscript's 40-term arcsine
evaluation. `certified_radius_cover` proves that these eight intervals cover
`[3/5, 60849/100000]` without gaps.

The generated imports form a chain so a cold build checks one row at a time.
On the development machine each row takes roughly 1–2 minutes; cached builds
reuse the compiled theorems. `scripts/generate_radial.py` only copies the literal
input data and emits theorem statements. Its `--check` mode verifies deterministic
regeneration against the original JSON and its SHA256.

`InnerOuter.lean` proves the concentric inner-ball inclusion and the actual clipped
sandwich. `RadialAnalysis.lean` proves the tangent deficit decreases below its
tangent point and increases above it, and that a uniform margin survives limits.
`CompletionAlgebra.lean` proves the polynomial minorant, the scalar curvature-weight
inequality, the two convexity polynomials, and the coupled affine-budget sum.

**Boundary:** the arithmetic row theorems alone do not bound the volume of an arbitrary
body. Milestones 5 and 6 prove both cap bounds, their disjointness, and the
pointwise tangent-deficit estimates. Milestone 7 integrates these contributions
against the actual spherical measure. Milestone 8 proves the parallel-volume
comparison and Blaschke identity and completes the radial branch.
The completion-integral and clipped-hull finite certificates have not yet been
checked in Lean.

## Milestone 4: actual circumspheres, contacts, and normalization

`EnclosingBall.lean` defines the enclosing radius as the maximum distance to the
body and proves the existence of a minimizing center. Its contact set is nonempty
and compact. The center lies in the contacts' convex hull: otherwise, projection
onto that hull provides a direction in which a small displacement strictly reduces
the enclosing radius. `CompactHull.lean` supplies finite-dimensional compactness
of convex hulls and a finite, positive Carathéodory representation.

`ContactExistence.lean` constructs at most four affinely independent contacts with
strictly positive balancing weights, retaining their membership in the original
body and their actual enclosing radius. Consequently a unit-width body's radius
satisfies `1/2 ≤ R` and `R^2 ≤ 3/8`. If `R^2 > 1/3`, four contacts are necessary,
and the circumcenter lies strictly inside their tetrahedron. For `R ≥ 60849/100000`,
`exists_contacts_with_deficit_budget` supplies these actual contacts with the
two-sided budget and `A < 2/25`.

`Translation.lean` proves that translation preserves width and Lebesgue volume
and moves the minimum enclosing center as expected. `Normalization.lean` constructs
a centered unit-width representative of every positive-width body, proves that
zero is in its interior, and proves the exact cubic relation between their volumes.
These steps no longer require an assumed contact configuration or circumsphere.

## Milestone 5: geometric meaning of the negative-cap certificates

`ContactDirections.lean` derives both scalar-product bounds on the normalized
contact directions from the actual balancing weights and diameter constraint.
The upper bound is the manuscript's `4 * eta^2 / (1 - eta) - 1`; it does not assume
a regular tetrahedron or an angular-separation hypothesis.

`RadialGeometry.lean` proves the negative-cap quadratic and radical bounds for
every point of a unit-width body, without smoothness assumptions. It also proves
cap disjointness directly from inner products and Cauchy–Schwarz.

`Certificates/RadialGeometry.lean` connects those results to the rational grid,
the checked separation threshold, and every index of the recursive negative
candidate checker. The candidate's rational tangent deficit is a lower bound
for the actual tangent deficit throughout its cap.

`all_rows_negative_body_bound` applies all **14,814 stored negative candidates**
to actual points of the centered body using its constructed enclosing contacts.
`all_rows_negative_caps_disjoint` proves the four caps in each negative layer are
disjoint. Both use the already kernel-checked row theorems, so their statements
have no hypothesis assuming that the numerical checker succeeds.

## Milestone 6: radial function and positive-cap propagation

`RadialFunction.lean` constructs the radial function from the reciprocal Minkowski
functional. It proves continuity away from zero, positivity, the exact radial
membership interval, the boundary-point property, and the values at circumsphere
contacts. Hahn–Banach separation and the Riesz representation theorem provide a
supporting unit normal at every radial boundary point.

`PositivePropagation.lean` proves the geometric one-step propagation theorem
directly from that supporting plane, the opposite-point inequality, and orthogonal
components of unit vectors. The proof applies to nonsmooth bodies. It compares
the actual normal with the candidate's normal cone, avoiding a differentiability
assumption on the boundary or a separate analytic monotonicity assumption.

`SphericalCaps.lean` constructs a preceding direction on a great-circle arc for
every point in the next cap. `Certificates/RadialGrid.lean` proves that the exact
rational grid coordinates and step coordinates are the corresponding cosines
and sines. `Certificates/PositiveCaps.lean` then proves the propagation induction
for every index of the actual candidate list.

`all_rows_positive_radial_bound` applies all **5,836 positive candidates** to the
radial function of the centered body. Together with the negative candidates,
the checked rows now give actual pointwise tangent-deficit bounds on both cap
families. The four positive caps in each layer are pairwise disjoint, as are the
four negative caps, and every positive cap is disjoint from every negative cap. These are
geometric consequences of the kernel-checked arithmetic and the constructed
contacts. Milestone 7 supplies the spherical integration; milestone 8 supplies
the radial branch's volume conclusion.

## Milestone 7: actual radial volume and cap integrals

`RadialVolume.lean` defines spherical measure from ordinary Lebesgue measure using
mathlib's polar-coordinate construction and proves its total mass is `4 * pi`.
The radial subgraph of the body's interior has the same Lebesgue measure as the
body, since a convex boundary has measure zero. This gives the actual identity
`integral (rho^3) = 3 * bodyVolume K`, without a smoothness hypothesis.

`SphericalMeasure.lean`, `SliceVolume.lean`, and `CapArea.lean` prove the exact cap
area `2 * pi * (1 - c)` for `0 < c ≤ 1`. A cap's measure is three times the volume
of its truncated solid cone. Orthogonal maps preserve that volume. Separating
one coordinate and integrating the planar disk slices computes the cone's volume;
the disk areas and polynomial integrals are kernel-checked theorems.

`CapIntegration.lean` proves the annulus area formula, finite integration of
pointwise bounds on disjoint pieces, integrability of the radial deficit and flux,
and the integrated tangent identity with actual body volume.

`Certificates/CapIntegrals.lean` applies these results simultaneously to the four
positive and four negative contact families. This accounts for **82,600 annulus
contributions** across the eight rows. Their complete exact sum and the checker's
downward-rounded sum both bound the actual spherical tangent-deficit integral.
`all_rows_gap_integral_lower` applies the stored, kernel-checked rows to an arbitrary
unit-width body in the corresponding radius interval and constructs the four
contacts itself. It assumes neither a numerical verification result nor an
unproved cap-area or integration formula.

The integral bounds are used in milestone 8 to prove the radial branch's volume
bound. The near-Jung completion branch remains incomplete.

## Milestone 8: Blaschke identity and the complete radial branch

`Minkowski.lean` proves the actual difference-body identity `K + (-K) = B` for
unit-width bodies. `SupportMap.lean` proves uniqueness of support points and their
1-Lipschitz dependence on the unit normal for every summand of the unit ball.
`SupportParametrization.lean` extends this map homogeneously to the whole space
and applies mathlib's Rademacher theorem to obtain differentiability almost
everywhere.

`ParallelParametrization.lean` proves that adding `t` times the identity to this
map sends the closed unit ball onto the actual parallel body `K + tB`.
`ParallelInverse.lean` proves a quantitative inverse bound and injectivity for
`t > 0`. `LipschitzJacobian.lean` proves that the exceptional set and its image
have volume zero, allowing mathlib's Jacobian theorem to apply without assuming
smoothness. `ParallelJacobian.lean` proves positivity of the determinant and
identifies its integral with actual parallel volume.

`JacobianCubic.lean`, `ParallelContinuity.lean`, and `ParallelPolynomial.lean`
derive the cubic parallel-volume formula, including its value and right
derivative at zero. `BlaschkeIdentity.lean` uses complementary support maps and
reflection to prove that the linear coefficient is `2 * bodyVolume K + 2*pi/3`
and the quadratic coefficient is `2*pi`. These coefficients are defined through
actual volume; no mixed-volume or boundary-area formula is assumed.

`ParallelVolume.lean` bounds the radial expansion of actual parallel bodies
using supporting planes and the opposite-point inequality. `RadialMaster.lean`
combines that bound with the proved right derivative to obtain the radial master
inequality. It proves the strict volume bound for enclosing radius `R ≤ 3/5`.

`Certificates/RadialVolume.lean` combines the master inequality with the eight
kernel-checked rows and their geometric integral bounds. It proves
`bodyVolume K > 4144109/10000000` for `3/5 ≤ R ≤ 60849/100000`. The theorem
`MinimumEnclosingBall.volume_gt_of_radius_le_radial_cutoff` therefore gives
`bodyVolume K > 259/625` for every unit-width body with minimum enclosing radius
at most `60849/100000`. This is an end-to-end proof of the whole radial branch,
including nonsmooth bodies, with no unproved geometric interfaces.

**Boundary:** the unrestricted main theorem is still unproved. The remaining
radius range is `60849/100000 < R ≤ sqrt(3/8)`.

## Milestone 9: actual clipped complements and their volume identities

`SmallBallIntersections.lean` proves that an intersection of balls of radius at
most one lies in every unit ball tangent to a supporting plane. It uses an
explicit quadratic perturbation of a chord, followed by a limit at its endpoint.
The proof applies without a smoothness assumption or a normal-cone formula.

`ComplementaryBodies.lean` bundles the actual ball transform and proves
`C + (-D) = B` when `D = B(C)` and `C` is such an intersection. The determinant
polynomial then gives the complementary identities
`V_D = 4*pi/3 - M_C + S_C - V_C`, `S_D = 4*pi - 2*M_C + S_C`, and
`M_C + M_D = 4*pi`, where `S` and `M` are the proved parallel-volume coefficients.

`ClippedBodies.lean` constructs `C = RB ∩ B(Y)` and `D = B(C)` as actual compact
convex bodies. It proves their complementarity, interior, volume sandwich around
the original constant-width body, and all three coefficient identities.
Nonemptiness follows from the original body and its contact-set inclusion.
These results establish the manuscript's complementary-body step; the weighted
completion inequality and explicit clipped-boundary integrals remain open.

## Milestone 10: nonsmooth curvature and the actual support-volume formula

`SupportDifferentiation.lean` proves that the derivative of the actual support
function is its supporting point. The normalized support map is differentiable
almost everywhere, and its derivative is symmetric wherever it exists.
`NormalDerivative.lean` proves that this derivative kills the normal direction,
maps into the tangent plane, and is positive semidefinite with upper bound the
tangent projection. These statements require no smoothness assumption.

`SphericalDifferentiation.lean` transfers almost-everywhere differentiability
from ambient Lebesgue volume to spherical area: homogeneity makes the exceptional
set a union of rays, and the defining cone formula for spherical measure proves
it has area zero. `CurvatureOperator.lean` defines the actual measurable derivative
`Q_K` and proves `Q_L = I_tangent - Q_K` almost everywhere when `K + L = B`.

`SpectralBounds.lean` and `CurvatureDensity.lean` prove measurability, integrability,
and the bounds `0 ≤ det Q_K ≤ 1`, `0 ≤ tr Q_K ≤ 2`, and
`tr Q_K - 1 ≤ det Q_K`. The tangent determinant is calculated as the ambient
determinant after adding the normal projection, avoiding a choice of moving frame.

`TangentJacobian.lean` proves that the Jacobian of the actual homogeneous support
parametrization is `h_K * det Q_K` almost everywhere. Its proof separates the
normal support height with a rank-one determinant identity.
`HomogeneousDifferentiation.lean` and `PolarHomogeneous.lean` prove the derivative's
degree-zero homogeneity and the corresponding polar integral formula.
`SupportVolumeFormula.lean` combines these with the established Jacobian volume
formula to prove `3 * bodyVolume K = integral (h_K * det Q_K)` for actual summands
of the unit ball containing the origin in their interior.

**Boundary:** this proves the support-volume formula and the curvature bounds
used in the completion branch. The mixed-volume variation identities and the
weighted completion inequality are still unproved.

## Milestone 11: tangent determinant and parallel-volume coefficient integrals

`NormalFrame.lean` extends each unit normal to an orthonormal basis and proves
the matrix representation of the normal projection. `TangentDeterminant.lean`
uses these coordinates to prove
`det_tangent(s Q + t I) = s^2 det Q + s*t tr Q + t^2`.
It also proves the complementary determinant identity
`det Q_L = 1 - tr Q_K + det Q_K` almost everywhere when `K + L = B`.

`ParallelCurvature.lean` proves, on one common full-measure subset of the sphere
and for every real `t`, that the parallel Jacobian is
`(h_K + t) * (det Q_K + t tr Q_K + t^2)`. Integrating and comparing polynomial
coefficients identifies the actual parallel-volume coefficients:
`3 S_K = integral (det Q_K + h_K tr Q_K)` and
`3 M_K = integral (tr Q_K + h_K)`.

**Boundary:** the integration identities that simplify these expressions to
`S_K = integral (det Q_K)` and `M_K = integral h_K`, and the mixed-volume
variation identities, are still unproved. This milestone does not assume them.

## Milestone 12: an actual shell-volume variation formula

For nested summands `D ⊆ K` of the unit ball, `MinkowskiInterpolation.lean`
constructs the intermediate bodies `(1-t)D + tK + (epsilon + t*delta)B`.
`ShellInjectivity.lean` and `ShellCoverage.lean` prove that their supporting
points, for `0 ≤ t ≤ 1`, parametrize exactly the region between
`D + epsilon B` and `K + (epsilon + delta)B`, with unique parameters when
`epsilon, delta > 0`. Coverage follows by maximizing a support-deficit ratio
over the sphere, using the actual bodies and supporting planes.

`ShellParametrization.lean` transfers this map to the compact Euclidean annulus
`1 ≤ norm x ≤ 2`. `ShellLipschitz.lean` proves Lipschitz regularity on that
annulus. `LocalJacobian.lean` supplies the corresponding change-of-variables
theorem, including the null exceptional set and its null image.

`ShellDerivative.lean` and `ShellJacobian.lean` prove the actual derivative
and its determinant. `PolarAnnulus.lean` cancels the radial Jacobian factor.
`ShellVolume.lean` consequently proves

```text
V(K + (epsilon + delta)B) - V(D + epsilon B)
  = integral_sphere integral_0^1
      (h_K - h_D + delta)
      det_tangent((1-t)Q_D + t Q_K + (epsilon + t*delta)I) dt.
```

This formula requires no boundary smoothness or assumed mixed-volume identity.
**Boundary:** removing the positive rounding parameters and extracting the
volume and area variation identities are supplied by milestone 13.

## Milestone 13: nonsmooth volume and area variation identities

`MixedTangentDeterminant.lean` proves the quadratic polarization identity for
the two-dimensional tangent determinant. `MixedCurvature.lean` proves
measurability and integrability of the actual mixed curvature density.

`ShellPolynomial.lean` integrates the shell determinant exactly in interpolation
time. `ShellIntegralPolynomial.lean` proves that its spherical integral is a
polynomial in the rounding parameters, with integrable coefficients.
`VolumeVariation.lean` removes both positive rounding parameters by polynomial
continuity and compares the resulting coefficients. For nested actual summands
`D ⊆ K`, with zero in the interior of `D`, this proves

```text
3(V_K - V_D) = integral (h_K - h_D)(det Q_D + D2(Q_D,Q_K) + det Q_K)
2(S_K - S_D) = integral (h_K - h_D)(tr Q_D + tr Q_K)
  M_K - M_D  = integral (h_K - h_D).
```

Here `S` and `M` are the coefficients already proved to govern actual parallel
volume. These are the manuscript's two variation identities, plus the mean-
coefficient identity, proved without a smoothing assumption or mixed-volume
interface. The nested clipped bodies used in the completion branch satisfy the
interior hypothesis.

## Remaining proof obligations

The larger-radius completion branch still needs quantitative tetrahedral geometry,
the simplified area and mean-coefficient integral formulas, the weighted completion
inequality, clipped-body boundary formulas, the antipodal completion integral,
the completion-integral and clipped-hull certificate verifiers, and final assembly. None of these
is hidden behind a custom axiom or an assumed instance claiming the main theorem.
The radial branch and the support-volume formula need no further smoothing.

A fresh execution of the original Python/C++ verifier at 52/192-bit precision
passed on 2026-11-15: 584 integral rectangles, 3,200 derivative boxes, 512 hull
intervals, and eight radial rows. That execution is external numerical evidence;
it is not a kernel verification of the certificate algorithms or their geometric
soundness.
