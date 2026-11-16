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
python3 scripts/generate_projective_cover.py --check
python3 scripts/generate_centered_first.py --check
python3 scripts/generate_first_gradient.py --check
python3 scripts/generate_projective_suite.py --check
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

## Milestone 14: the area and mean-coefficient integral formulas

`BallCurvature.lean` constructs an actual centered inner ball and computes its
support, tangent curvature, and parallel-volume coefficients. Applying the mean
variation identity from this ball to `K` proves
`M_K = integral h_K`. The previously established coefficient formula then gives
`integral tr Q_K = 2 M_K`.

`CurvatureIntegrals.lean` applies area variation from the same inner ball to
prove `integral (h_K tr Q_K) = 2 S_K`. Comparing with the parallel-volume
coefficient formula proves `S_K = integral det Q_K`. These identities hold for
actual summands of the unit ball with zero in their interior, including the
nonsmooth bodies in the completion argument.

## Milestone 15: the weighted antipodal completion bound

`PositiveTrace.lean` and `TangentCofactor.lean` prove the operator positivity
facts needed to compare mixed curvature. `MixedCurvatureBound.lean` identifies
the mixed determinant with a cofactor trace and proves
`2 D2(Q_D,Q_K) ≥ det(Q_D) tr(Q_K)`. This controls every relative orientation
of the two actual curvature operators.

`CurvatureWeight.lean` connects the scalar contraction estimate to these actual
operators and integrates the resulting inequality using the proved variation
identities. `AntipodalIntegration.lean` proves that spherical measure is invariant
under negation, directly from its cone definition. `AntipodalCompletion.lean`
pairs the support gaps with the even weight given by the smaller opposite
curvature determinant.

`WeightedCompletion.lean` combines these facts with the Blaschke identity and
the complementary-body coefficient identities to prove the manuscript's bound:

```text
V_K ≥ (47 V_D - V_C)/46 + (4/23) integral g(u) psi(d_*(u)),
g(u) = 1 - h_D(u) - h_D(-u),
d_*(u) = min(det Q_D(u), det Q_D(-u)).
```

The theorem `HasConstantWidth.clipped_weighted_completion` applies this to the
actual clipped bodies constructed from the original constant-width body and
any supplied subset of its points. No curvature field, volume identity, or
completion inequality is assumed. The explicit geometric and numerical lower
bounds for the right-hand side remain separate obligations.

## Milestone 16: opposite-edge geometry and contact-circle clipping

`ContactRelabeling.lean`, `OppositeEdges.lean`, and `OppositeEdgeBounds.lean`
derive the exact midpoint-separation identity and the normalized scalar-product
bounds from the six actual contact deficits. `OppositePartitions.lean` applies
them to all three pairings and proves `sum a_j = A` and `sum b_j = 2 A`.
`CompletionRegion.lean` proves the bounds on the exact radical expressions:
`c <= 1/25`, `eta < 1/16`, and `1/2 < T <= 1/sqrt(2) < 3/4`.

`TwoAxisProjection.lean` constructs the common normal by inverting the two-axis
Gram matrix and proves its residual is nonzero. `ContactNormal.lean` projects
the actual contact balance onto it to put the two midpoints strictly on opposite
sides of the origin. This does not assume an orientation or that the midpoint
separation is itself perpendicular to the two edges.

`ContactCircleBounds.lean` proves the circle's nondegeneracy and its clipping
cosine bound by a factored polynomial inequality. `ContactCircle.lean` proves
both directions of the parametrization of the intersection of the two actual
unit spheres, and identifies clipping by the enclosing ball with the claimed
arc inequality. These results do not yet prove membership in the other two
unit balls, the complete clipped-boundary incidence, or the common-normal
rectangle's validity as a support region.

## Milestone 17: circle support and actual clipped-body curvature

`CircleNormalCone.lean` proves that the proposed normal is a nonnegative
combination of the two sphere normals on the exact two-ball normal cone.
`CircleSupport.lean` uses this to prove the support formula whenever the
candidate passes the remaining ball constraints. A positive complementary
radius implies the strict normal-cone condition, with the required nonzero
projection hypothesis explicitly retained.

`CircleDerivative.lean` differentiates the circle candidate and computes its
curvature trace and tangent determinant. `CircleSupportRegion.lean` proves
that strict membership in the enclosing ball and the other two unit balls
gives a neighborhood where the actual clipped-body support map equals this
candidate. Consequently its actual curvature trace is
`r / sqrt(1 - <k,n>^2)`, and its actual curvature determinant is zero.

`CurvatureReflection.lean` proves pointwise reflection and complement identities
at differentiability points. On those same explicit regions it gives the forced
inner body's actual determinant at the opposite normal:
`det Q_D(-n) = 1 - r / sqrt(1 - <k,n>^2)`.
These statements do not assume curvature formulas or differentiability of the
clipped body. The remaining incidence and angle arguments must still establish
that the proposed integration rectangles satisfy the explicit ball constraints.

## Milestone 18: the full clipped unit-unit arcs are valid

`ContactBallConstraints.lean` extends the weighted squared-distance identity
to every point: `sum lambda_i |x-y_i|^2 = |x|^2 + R^2`. Together with the
contact weight bound, this excludes a triple unit-sphere intersection inside
the enclosing ball. A positive incident deficit excludes the closed ball as
well. Neither claim needs face normals or an assumed boundary incidence.

`ContactArcCenter.lean` proves that the inward center of each clipped circle
arc lies strictly in the other two unit balls for every configuration with
`A <= 2/25`. `SphericalCapPath.lean` constructs a normalized-chord path within
the clipping cap. `ContactArcIncidence.lean` then uses the intermediate value
theorem and the triple-intersection exclusion to prove that every open arc
point is strictly in the other balls. Continuity includes both endpoints in
their closed balls.

Thus the entire radius-clipped unit-sphere intersection is an actual arc of
the four-ball clipped body, including configurations with zero deficits. This
argument does not require continuation through the deficit simplex. The local
curvature theorems from milestone 17 now require only the normal-cone condition
and strict radius clipping; the other-ball constraints are proved consequences.
The full surface decomposition and boundary-volume integration still remain.

## Milestone 19: common-normal coordinates and rectangle clipping

`ObliqueFrame.lean` constructs the two transverse unit vectors from the actual
edge axes and proves their Gram matrix and coordinate decompositions.
`ContactFrameBounds.lean` derives the normalized midpoint error bound `eta`
and the corresponding normal-alignment bounds. The orientation is supplied
by the contact balance already proved in milestone 16.

`RectangleClipping.lean` proves the exact angular margin of `T(a,b)` algebraically.
`ProjectiveCoordinates.lean` constructs the projective normal and proves
`W = 1 + |m|^2`, the two circle-plane projections, and their exact lengths.
`OppositePairSwap.lean` exchanges the opposite edges while preserving the
deficit budgets and the clipped body.

`ProjectiveClipping.lean` combines these results to prove that the first
circle candidate is strictly radius-clipped whenever `|x| < T`, and the
opposite second candidate whenever `|y| < T`. The previously proved arc
incidence gives membership in all four unit balls. The normal-cone condition
is still required for these candidates to be support points; it is distinct
from radius clipping. The projective area Jacobian and the explicit joint
integral estimate remain to be proved.

## Milestone 20: actual paired completion integrand and coupled radii

`ProjectiveCurvature.lean` and `ProjectivePairSupport.lean` prove the exact
support-gap formula and both opposite curvature determinants on the positive
curvature region. Positivity supplies the strict normal-cone condition; the
rectangle clipping and arc incidence supply every ball constraint. These are
formulas for the actual clipped bodies.

`RadiusAllocation.lean` proves the coupled radius allocation inequality
directly by squaring nonnegative radicals. `ProjectiveAllocation.lean`
identifies these radii with the actual edge circles, bounds the longitudinal
separation, and constructs a common determinant lower bound below `1/5`.

`ProjectivePairing.lean` proves that the coordinate sign pair `(x,y)` and
`(-x,-y)` cancels the transverse midpoint error exactly. It also bounds the
actual smaller antipodal curvature determinant, including the zero-clamped
region. `ProjectiveCompletionLower.lean` combines these facts with nonnegative
missing width and the polynomial minorant `q` to prove the paired pointwise
lower bound for the actual completion integrand. Its contact corollary derives
the inner-body containment from the original constant-width body.

The projective area change of variables, obliquity averaging, integration,
and summation over disjoint patches remain unproved at this milestone.

## Milestone 21: clamped convexity and averaging edge obliquity

`CompletionPhiCalculus.lean` proves both derivatives of the unclamped integrand
and identifies the second derivative with the manuscript's `B1` and `B2`
polynomials. Their previously checked bounds prove nonnegative second
derivative on the active interval.

`ConvexTruncation.lean` proves that a decreasing convex function remains convex
when extended constantly past an endpoint. `CompletionPhi.lean` applies this
at the first zero of the two factors, proving monotonicity and convexity for
the integrand with both positive-part clamps. Thus the cutoff is covered by
the theorem, not only its smooth interior.

`CompletionObliquity.lean` verifies the parameter domain from the actual
deficit budgets and proves Jensen averaging of the two coordinate signs,
followed by the uniform obliquity bound. `ProjectiveFourSigns.lean` combines
this with milestone 20: the sum over four signs of the actual completion
weight, multiplied by the explicit projective area factor, is at least four
times the uniform integrand. Identifying that area factor with spherical
measure and then integrating and summing the patches remain separate proof
obligations.

## Milestone 22: projective chart, radial Jacobian, and actual change of variables

`ProjectiveChart.lean` constructs the inverse projective coordinates and a
homeomorphism from the plane onto the open hemisphere. `RadialProjectiveMap.lean`
extends this chart along positive rays, proves differentiability, and proves
injectivity on the whole positive parameter half-space.

`ProjectiveJacobian.lean` computes the derivative's determinant in the proved
orthonormal frame. It is exactly `r^2 / (sqrt(1-chi^2) * sqrt(W)^3)`; the
rank-one normalization terms cancel in the determinant. The ordinary Lebesgue
change-of-variables formula is proved for every measurable subset of the
positive parameter half-space.

`ProjectiveAnnulus.lean` identifies parameter cylinders with the actual
annulus patches cut out by the hemisphere and projective coordinates, then
specializes the integral formula to those patches. Separating the radial
factor by Fubini and comparing with polar integration is still needed for
the final spherical chart integral identity.

## Milestone 23: the actual spherical area and completion integral formulas

`FrameProductCoordinates.lean` constructs measure-preserving product coordinates
in the actual orthonormal frame and proves the radial/planar factorization of
integrals. `ProjectiveCone.lean` identifies the image of the positive radial
cylinder with its actual cone and computes its integral using the Jacobian.

`ProjectiveSphereIntegral.lean` compares this cone integral with the previously
proved polar formula. The common radial factor `1/3` cancels, giving the
spherical chart formula with density `1 / (sqrt(1-chi^2) * sqrt(W)^3)` for
arbitrary functions on the unit sphere. The patch is proved to be the chart
image, measurable for measurable parameter sets, and disjoint from every
antipodal patch in the same frame.

`ProjectiveCompletionIntegral.lean` applies this measure identity to the actual
missing width and antipodal curvature weight. Thus the chart integrand from
milestone 21 now represents the actual spherical completion integral.
Milestone 24 integrates this identity over the positive-curvature regions.

## Milestone 24: the actual positive-curvature patch contributes at least F

`ActiveProjectiveRegion.lean` discards contributions outside the region where
the common curvature lower bound is strictly positive. This is necessary for
the later disjointness argument: both circle support formulas hold on that
region. The paired and four-sign inequalities survive the restriction because
the scalar minorant vanishes at nonpositive common curvature.

`ProjectiveIntegrability.lean` proves integrability of the actual chart density
and its restriction, and continuity of the scalar density.
`RectangleSignIntegration.lean` proves measure preservation under both
coordinate reflections and integrates the four-sign inequality.
`ActiveCompletionIntegral.lean` therefore bounds the actual spherical patch
integral by the scalar rectangle integral, with all geometric and integrability
hypotheses supplied by the constant-width body and its contacts.

`RectangleQuadrantIntegral.lean` identifies the rectangle integral with the
manuscript's `F(a,b) = 4 * integral_[0,T]^2 Phi`, including equality to the
iterated interval integral. `AntipodalPatchIntegral.lean` proves that the union
of the patch and its antipodal image contributes at least `2 * F(a,b)` to the
actual missing-width/curvature integral. Milestone 25 proves disjointness
between different opposite-edge pairs and sums their contributions.

## Milestone 25: disjoint edge patches and the geometric completion estimate

`ClippedRelabeling.lean` proves that arbitrary permutations of the four
contacts preserve the actual clipped outer and inner bodies.
`ActiveSupportLabels.lean` proves that the actual support point of every
retained normal has exactly its two defining unit balls active. It lies
strictly inside the other two balls; the antipodal normal selects the
opposite edge.

`DisjointCompletionPatches.lean` constructs a common-normal frame for each
of the three opposite-edge partitions and proves that their patch pairs
are disjoint. The proof compares the exact active contact labels of the
unique actual support point, and covers all six edge labels.

`CompletionPatchSum.lean` integrates over this disjoint union and applies
the weighted completion bound. It proves the manuscript's geometric estimate
`V_K >= (47 V_D - V_C)/46 + (8/23) * sum_j F(a_j,b_j)` for actual clipped
bodies constructed from the original constant-width body and its contacts.
All frames, integrability, circle support, curvature, and disjointness facts
used in this estimate have been proved.

## Milestone 26: the completion certificate's exact fixed-square integral

`SymmetricSquareIntegral.lean` splits a continuous symmetric square integral
into two triangles, proves that the diagonal has zero measure, and derives
the exact substitution `x = T*s`, `y = T*s*t` with Jacobian `T^2*s`.

`CompletionFixedSquare.lean` applies this to the actual scalar `F(a,b)`.
It identifies `F` with the unit-square integral of the certificate's density,
proves continuity, integrability, and nonnegativity, and removes the
`min(x^2,y^2)`/`max(x^2,y^2)` switch on the ordered triangle. The density equals
the explicit smooth expression when both gap and determinant factors are
nonnegative, and vanishes whenever either factor is nonpositive.
Milestone 27 proves the quadrature error bounds. The interval arithmetic,
parameter cover, and finite certificate evaluation remain to be formalized.

## Milestone 27: the retained-cell midpoint quadrature rule is sound

`MidpointQuadrature.lean` proves a quadratic tangent lower bound from an
explicit second-derivative lower bound and integrates it exactly. On an
interval of half-width `h`, the resulting midpoint correction is `M*h^2/6`.

`RectangleQuadrature.lean` applies this twice to prove the rectangular rule
with correction `Mx*h^2/6 + My*k^2/6`, using only pure second derivatives.
It also proves that a nonnegative cell integrand permits clamping the
computed lower value to zero.

`CompletionCellQuadrature.lean` transfers this bound from the smooth formula
to the actual clamped completion density on a retained cell. The cell must
lie in the unit square, both smooth factors must be nonnegative, and the
first and second derivatives and their bounds are explicit hypotheses.
These are obligations for the interval/jet checker, not assumed numerical
facts. Milestone 28 supplies finite grid aggregation; evaluating the
certificate's cell bounds remains to be formalized.

## Milestone 28: finite grid aggregation and the parameter extension

`UniformGridIntegral.lean` proves exact decomposition of a continuous
unit-square integral into a finite uniform grid, including the cell endpoint,
midpoint, and area identities. Summing proved cell lower bounds gives a lower
bound for the full integral. Unretained cells may be assigned zero because
the actual completion density is nonnegative.

`CompletionParameterExtension.lean` defines the fixed-square integral beyond
the geometric parameter triangle and proves that it equals `F` on that
triangle. Continuity, nonnegativity, and the smooth formula on retained cells
are proved under the broader condition `abs(obliquity a b) < 1` (with `a >= 0`
for nonnegativity). The quadrature theorem now works on this extended domain.
This matters because 38 of the 584 accepted parameter boxes have centers
outside `a+b <= 2/25`; the largest sum of box upper endpoints is `17/200`.
Their center evaluations must refer to the extension, not rely on a geometric
identity outside its proved domain.

No interval/jet evaluations or parameter Lipschitz estimates are assumed to
be correct by these results. Milestone 29 checks the accepted-leaf cover.

## Milestone 29: a kernel-checked cover by all 584 parameter boxes

`Certificates/ParameterCover.lean` implements a rational bisection checker and
proves its soundness for the closed triangle `a >= 0`, `b >= 0`, `a+b <= 2/25`.
A leaf must match a supplied box exactly or have its lower corner strictly
outside the triangle. Thus the check also covers the triangle boundary.

`Certificates/Generated/ProjectiveCover.lean` checks the subdivision for the
584 boxes in the 52-bit report using `decide +kernel`. It also checks that every
box lies in `a >= 0`, `b >= 0`, `a+b <= 17/200`, which is inside the parameter
extension's obliquity domain. Both statements are theorems about real points,
not just comparisons of recorded areas or leaf counts.

The generator emits literal rational boxes and a candidate tree. Lean checks
every lookup, bisection, and discarded leaf. CI checks deterministic generation
against the source report and its hash. This result certifies coverage and
domain bounds only: the report's integral and derivative columns are not used
as proof inputs and remain to be verified.

## Milestone 30: parameter variation through the positive-part cutoffs

`CutoffMeanValue.lean` proves signed secant bounds for a continuous function
whose derivative is known only where the function is nonzero. The derivative
interval must include zero. The proof uses the first and last zero on a compact
interval and the mean value theorem on the remaining pieces; it does not
require finitely many zeros or differentiability at a cutoff. This proves the
verifier's `hullzero` rule. Strictly active cells retain their sharper original
signed derivative interval.

`CompletionParameterRegularity.lean` proves continuity of the actual certificate
expressions in the parameters on `a,b >= 0`, `a+b <= 1/10`, by proving their
denominators are positive. This region contains all 584 parameter boxes.
`CompletionParameterVariation.lean` applies the cutoff rules to the actual
completion density along parameter curves, including coordinate segments.

`UniformGridBounds.lean` integrates signed cell bounds and proves bounds on
differences of the full integrals. Thus verified derivative enclosures can
control parameter variation without exchanging differentiation and integration.
The analytic rules are proved; constructing and evaluating the interval/jet
enclosures and the unconditional numerical lower bound remain open. Milestone
31 verifies the final box acceptance arithmetic.

## Milestone 31: exact box acceptance arithmetic and conditional assembly

`ParameterBoxEstimate.lean` turns signed coordinate secant bounds into a bound
on the affine residual's variation over a parameter box. A proved center
integral lower bound exceeding the affine center value plus this variation
implies the desired strict affine bound throughout the box.

`Certificates/ProjectiveAcceptance.lean` implements the exact rational final
acceptance test and proves its soundness. The generated module checks all
584 candidates using `decide +kernel`: derivative intervals are ordered,
each recomputed margin is positive and at least its recorded lower margin,
and the candidate boxes exactly match the already verified cover.

`completion_affine_lower_of_analytic_bounds` assembles these checks into the
affine lower bound for the geometric `F`, using its fixed-square extension
for centers outside the triangle. Its analytic premise remains **unproved**:
for every candidate, the stated center-integral lower bound and both signed
coordinate-secant enclosures must be constructed by the interval/jet checker
and the proved quadrature/variation rules. The report values are candidate
data, not assumed theorems. This is a conditional assembly result, not yet a
verified completion-integral certificate or a proof of the volume target.

## Milestone 32: sound fixed-dyadic interval arithmetic

`Certificates/FixedPointRounding.lean` implements signed floor/ceiling division
and integer square-root rounding, and proves that their scaled values bound
the actual real operations. Negative denominators are normalized before
Euclidean division. Square-root candidates come from Lean's proved integer
square root, with no floating-point proposal.

`Certificates/FixedInterval.lean` implements the verifier's interval operations
at an arbitrary common scale `2^precision`: rational constants, spans,
addition, subtraction, multiplication, reciprocal, division, square root,
squaring, positive part, hull with zero, and absolute bound. Every operation
has a real containment theorem. Reciprocal and root rules require explicit
domain checks; squaring across zero has exact lower endpoint zero. Unbounded
integers avoid the C++ implementation's machine overflow issue.

These are sound executable primitives. Milestone 33 supplies the second-order
jet propagation. Certificate expression evaluation and actual finite grid
computations still need to be connected to the analytic bounds.

## Milestone 33: real and interval second-order jets

`SecondOrderJet.lean` proves the actual first and second derivative rules for
constant and variable jets, sums, products, composition, quotients, squares,
and square roots. A jet tracks one derivative direction; the two pure
derivatives needed by quadrature can be treated independently. No mixed
derivative is needed.

`Certificates/IntervalJet.lean` implements the same formulas with fixed-dyadic
intervals and proves containment of all three real components. Reciprocal
checks exclude zero. Square-root jet checks require a positive input enclosure
and exclude zero from both derivative denominators. Thus the interval output
can bound the actual derivatives once the certificate expressions and their
input boxes are supplied. Milestone 34 supplies the full expression evaluator.

## Milestone 34: checked expressions and their actual derivatives

`Certificates/IntervalExpression.lean` gives expressions four interpretations:
real values, real second-order jets, executable intervals, and executable
interval jets. Expressions include rational constants, variables, arithmetic,
squares, square roots, and a binding operation for shared intermediate values.
The executable interpreters return `none` when a required domain check fails.

Structural induction proves that every successful evaluation encloses the
corresponding real value or all three real jet components. A second theorem
uses the successful domain checks to prove actual differentiability: the jet's
first derivative component is the derivative of the ordinary real expression,
and its second derivative component is the derivative of the first. This includes bindings whose
stored intermediate values depend on the differentiation parameter.

The evaluator and its soundness are complete. Milestone 35 encodes the
particular certificate formulas. Evaluating the finite grids and deriving
the candidate analytic bounds remain to be done; no report column is assumed
correct.

## Milestone 35: the actual certificate formulas and their derivatives

`Certificates/IntervalProgram.lean` evaluates shared intermediate expressions
and returns several outputs from the same environment. Its containment and
derivative theorems apply to every output. Parameter expressions can therefore
be evaluated once per box and reused on the quadrature cells.

`Certificates/ProjectiveExpressions.lean` encodes the radical parameter
formulas and the integrand formulas from the C++ verifier. Lean proves that
their real interpretations are exactly the existing geometric parameters,
`squareGap`, `squareDetLower`, and `unitSquareSmoothDensity`. These identities
hold without assuming a numerical report or a successful interval evaluation.
Successful interval evaluations enclose these actual functions.

`Certificates/ProjectiveJets.lean` proves that successful evaluations also
give actual first and second derivatives of the smooth density, with interval
enclosures. Constant and identity input jets select spatial or parameter
directions. The shared-parameter case needed for point quadrature is included.

Milestone 36 connects the point quadrature's finite grid sums. The cutoff
variation checker remains open. The 584 candidates' analytic bounds are still
unproved; this milestone does not certify their numerical columns.

## Milestone 36: sound executable point-integral quadrature

`Certificates/ProjectiveSpatialJets.lean` specializes the checked derivative
rules to the two spatial directions. `Certificates/ProjectiveCell.lean` uses
these actual derivatives to prove the point-cell algorithm sound. Retained
cells use the checked midpoint value minus the pure-second-derivative error;
the proof includes the outward-rounded correction, truncation at zero, and
rounded area multiplication. Unretained cells contribute zero using the
nonnegativity of the true clamped density.

`Certificates/ProjectivePointIntegral.lean` implements exact integer summation
over a uniform grid. Every successful evaluation, at any positive grid size
and fixed-dyadic precision, gives a proved lower bound on the actual
`fixedSquareIntegral`. The hypotheses require contained parameters, `a >= 0`,
and `abs(obliquity a b) < 1`; they do not assume the quadrature values or any
derivative bounds. This also covers the accepted centers outside the geometric
parameter triangle.

`ProjectivePointExample.lean` checks a complete 8-by-8 grid at `a=b=0` using
`decide +kernel` and deduces the unconditional geometric bound
`F(0,0) >= 49/100000`. Separately, a local executable evaluation at the first
report center, `a=b=1/1600`, with the full 192-by-192 grid returned exactly
`6998590736130 / 2^52`, matching the report. That larger comparison is an
execution check, not a kernel certificate for that center.

The point-integral checker is proved sound. Milestone 37 supplies the
parameter-variation checker. Their kernel evaluations for all 584 candidates
and the unconditional completion affine bound remain to be completed.

## Milestone 37: sound executable parameter-variation quadrature

`Certificates/ProjectiveParameterJets.lean` proves the checked derivative
rules in both parameter directions. `Certificates/ProjectiveGradientCell.lean`
implements the verifier's three cases: an inactive cell has slope zero, a
strictly active cell keeps the signed derivative interval, and a boundary
cell adjoins zero. Successful evaluations imply signed secant bounds for the
actual clamped density throughout each parameter subsegment. No derivative
at an activation boundary is assumed.

`Certificates/ProjectiveGradientIntegral.lean` multiplies each slope interval
by its outward-rounded cell area and sums with exact integer addition. Its
soundness theorem integrates the cell secant bounds and yields
`SecantBounds` for the actual `fixedSquareIntegral` in either parameter
direction. The supplied parameter rectangle must lie in `a,b >= 0`,
`a+b <= 1/10`, which contains all accepted boxes. Numerical derivative
enclosures are consequences of the successful computation, not hypotheses.

Local executable 52-bit evaluations on the first accepted box with the
64-by-64 gradient grid reproduced all four report endpoints exactly:
`[-38305472032463,-8962798632166] / 2^52` in the `a` direction and
`[23361772611441,131824902922151] / 2^52` in the `b` direction. These are
execution comparisons; the full certificate still requires kernel checks.

Both projective numerical algorithms now have soundness proofs. Milestone 38
connects them to every candidate. Checking the resulting finite computations
in the kernel remains open.

## Milestone 38: candidate analytic bounds from a finite computation check

`Certificates/ProjectiveAnalyticBounds.lean` combines the point and gradient
algorithms with the reported candidate bounds. Its checker verifies the box
domain, positive grid sizes, all three algorithm outputs, and the rational
comparisons needed to imply the reported center and slope bounds. The
soundness theorem constructs `Candidate.AnalyticBounds` for the actual
fixed-square integral, including the centers outside the geometric triangle.

`allComputations` is the explicit Boolean check for all 584 candidates at
52-bit precision, using the 192-by-192 point grid and 64-by-64 gradient grid.
`completion_affine_lower_of_computations` proves that its truth implies the
affine lower bound for the geometric `F` on the full parameter triangle.
This theorem's remaining premise is finite computation, with no assumed
derivative or integral estimates. **The truth of `allComputations` has not
yet been proved.** The full volume theorem also retains the separate
clipped-body geometry and clipped-hull certificate obligations below.

## Milestone 39: smaller kernel-check imports and checked root proposals

`Certificates/FixedPointComputation.lean`, `ExpressionComputation.lean`, and
`ProjectiveComputation.lean` now contain the executable definitions independently
of their analytic proofs. The existing soundness theorems use these same
definitions. `ProjectivePointKernel.lean` checks the 8-by-8 example with this
smaller dependency set, and `ProjectivePointExample.lean` connects the checked
integer result to the geometric integral.

`CheckedSquareRoot.lean` proves that bounded Newton iteration followed by exact
square inequalities returns the same answer as `Nat.sqrt`, with a fallback
when the proposed answer fails the checks. This optimization preserves every
interval endpoint, for every precision and integer input.

The arithmetic-only import graph has 101 build jobs, compared with over 3,800
for the previous analytic import path. On the development machine, the same
kernel-checked 8-by-8 computation used about 2.0 GiB peak resident memory,
down from about 4.9 GiB. This prepares larger checks; it does not establish
`allComputations` or the main volume theorem.

## Milestone 40: centered retention and the first report-center bound

`RectangleVariation.lean` proves the coordinate mean-value bound used to
enclose a function throughout a cell from its midpoint and two derivative
bounds. `Certificates/ProjectiveSpatialVariation.lean` supplies those
derivatives for the actual gap and determinant functions, and
`CenteredRetention.lean` proves the resulting activation checks sound.

`CenteredComputation.lean` and `CenteredPointIntegral.lean` implement and
justify the improved point quadrature. A cell may pass either its original
interval test or the centered test. Its integral contribution still uses the
proved second-derivative correction and outward-rounded arithmetic.

`Generated/CenteredFirstKernel.lean` checks all 48 rows at the first report
center, `a=b=1/1600`, using `decide +kernel`. The JSON row totals are proposals;
each theorem recomputes the full row, and the parameter intervals are checked
separately. `CenteredFirst.lean` proves their sum and derives the unconditional
bound

```text
7008754898294 / 4503599627370496 <= F(1/1600, 1/1600).
```

This is stronger than that center's reported lower bound and uses 2,304 cells
instead of the original 36,864. Only this first report-center bound is certified
here. The parameter-slope certificates and the other report centers still need
kernel verification; the main volume theorem remains unproved.

## Milestone 41: the complete first parameter-box certificate

`Generated/FirstGradientKernel.lean` checks the parameter jets and all 128 rows
of the first box's two 64-by-64 gradient grids using `decide +kernel`.
`FirstGradient.lean` proves the exact sums and the resulting signed secant
bounds for the actual fixed-square integral.

`CenteredAnalyticBounds.lean` allows a separate precision and grid size for
each certificate entry. It proves that checked entries whose boxes match the
known cover imply the full completion affine bound. The required complete
list of successful entries has not yet been constructed.

`FirstProjectiveBox.lean` identifies its candidate with the first row of the
original report, proves that its complete entry passes, and derives

```text
153/100000 - (601/100000)*a + (317/20000)*b < F(a,b)
```

for every `0 <= a <= 1/800` and `0 <= b <= 1/800`. The center, both secant
enclosures, and final acceptance arithmetic are all proved. This closes
**one of the 584 parameter boxes**; the remaining boxes and the larger-radius
volume argument remain open.

## Milestone 42: enclosing-sphere circles and actual corner angles

`ClippingCircle.lean` constructs the circle where a contact unit sphere meets
the enclosing sphere. It proves both directions of the parametrization, with
center height `R - 1/(2R)` and radius `sqrt(1 - 1/(4R^2))`, and turns every
remaining unit-ball constraint into its exact linear inequality in the circle
direction.

`ClippedVertexAngles.lean` computes the scalar products of the three actual
sphere normals at a clipped vertex. It projects them into each face's tangent
plane and proves the manuscript's corner-angle formulas:

```text
U = arccos(s / (4 R sqrt(1-s^2/4) kappa))
V = arccos(1 - s^2/(2 kappa^2)),  kappa = sqrt(1-1/(4R^2)).
```

The angles are defined using mathlib's Euclidean angle, so these identities
also determine the intended supplementary angles.

`ClippedCapSeparation.lean` proves every contact weight is at least `11/50`
in the stated deficit range. At any point of the closed enclosing ball,
three contact distances that are at least one must all equal one. In
particular, three strict exclusions cannot occur, and a unit-sphere equality
cannot coexist with two other exclusions. This includes zero deficits.

**Boundary:** these results supply local geometry for the clipped-volume
calculation. The global boundary decomposition, surface integrals, and
separable volume identities remain to be proved.

## Milestone 43: exact forbidden intervals and null cap boundaries

`ClippingCircleCuts.lean` proves that the other contact ball removes exactly
the interval of circle directions with angular distance less than

```text
Psi = arccos((1-2R^2) s / (4 R kappa m)),
kappa = sqrt(1-1/(4R^2)),  m = sqrt(R^2-s^2/4).
```

The axis is constructed from the actual contact projection. The proof also
establishes `0 < Psi < pi/2` throughout the deficit range, including zero
edge deficits.

`CapBoundaries.lean` extends the exact spherical cap area to strict caps and
to every height in `[-1,1]`, including hemispheres and poles. It proves that
every affine plane with nonzero normal intersects the unit sphere in a set
of zero spherical measure. Consequently, replacing a closed cap by its
strict version preserves it almost everywhere. These results supply the
boundary measure statements needed for the later face integrals; the global
clipped-volume formulas remain open.

## Milestone 44: actual face regions and cap inclusion-exclusion

`ClippedFaceCaps.lean` defines a contact-face normal by requiring the actual
point `y_i + n` to belong to the clipped body, and an enclosing-face normal
by requiring `R n` to belong to it. It proves that these parametrizations
give the actual support points and supports.

The contact-face region is the enclosing cap minus three disjoint removed
pieces. Its area and the integral of any integrable scalar function split
accordingly. Each removed piece is the enclosing cap minus its intersection
with another cap. On the enclosing sphere, no three excluded caps overlap;
`FourSetInclusion.lean` proves the resulting exact inclusion-exclusion
identity for both areas and integrals. In particular, its normal-region area
is the full sphere area minus four explicit cap areas plus the six pairwise
cap-intersection areas. All statements include zero deficits.

These are identities for the actual measurable normal regions. Evaluating
the cap-intersection areas and moments, and assembling the global curvature
integrals into the claimed volume formulas, remain separate proof obligations.

## Milestone 45: actual face curvature and the surface-volume integrals

`ActiveBallCurvature.lean` derives the perpendicularity of the support-map
derivative to every active ball normal. If the tangent determinant is nonzero,
that normal must equal the support direction; its sign is proved from the
actual containing ball and membership of the origin. The determinant therefore
vanishes everywhere outside the actual spherical face regions.

`ClippedFaceBoundaries.lean` proves the contact points are distinct in the
deficit range, the five normal regions are disjoint, and their defining
inequalities are strict almost everywhere. `ClippedFaceCurvature.lean`
differentiates the actual support map on each strict face region. The unit
faces have trace `2` and determinant `1`; the enclosing faces have trace `2R`
and determinant `R^2`. Together these give the full determinant as a sum of
face indicators almost everywhere, including zero edge deficits.

`ClippedSurfaceIntegrals.lean` substitutes this identity in the already proved
support-curvature integrals. With `F_i` and `F_R` the actual normal regions,
it proves

```text
S_C = sum_i area(F_i) + R^2 area(F_R),
3 V_C = sum_i area(F_i) + R^3 area(F_R)
        + sum_i integral_{F_i} <y_i,n> d sigma.
```

The areas and first moments here are actual spherical integrals, not interface
inputs. Their explicit inverse-trigonometric evaluation and the integrated
edge contributions to `M_C` remain to be proved before the manuscript's
separable one-edge volume formulas follow.

## Milestone 46: spherical height integration and exact cap moments

`SphereHeightIntegral.lean` proves that the pushforward of spherical measure
under `n -> <u,n>`, for unit `u`, is exactly `2 pi` times Lebesgue measure on
`[-1,1]`. It derives one-dimensional integration formulas on the sphere and
on any cap. `SphereIsometry.lean` proves invariance of the actual spherical
measure under every ambient orthogonal isometry, directly from its cone
definition.

Reflection about the cap axis then gives the full first-moment formula in
`CapMoments.lean`:

```text
integral_{<u,n> >= c} <v,n> d sigma = <v,u> pi (1-c^2),
```

for every unit `u`, ambient vector `v`, and `-1 <= c <= 1`. In particular,
the enclosing cap of a contact face has center-weighted first moment
`-R pi (1-1/(4R^2))`. Removed-piece moments are reduced exactly to
cap-intersection moments. Those intersection moments and areas, and the
remaining edge curvature integrals, still require explicit evaluation.

## Milestone 47: exact joint height-longitude measure

`LongitudeRotation.lean` constructs rotations about the coordinate pole and
proves their action on the longitude defined by the transverse complex
argument. The two poles form a null set. `LongitudeMeasure.lean` proves that
the longitude pushforward of every cap is the circle's Haar measure, scaled
by `1-c`. Its normalization follows from the already proved cap area.

It then proves the full joint distribution:

```text
sigma.map (n -> (<e0,n>, longitude n))
  = (Lebesgue restricted to [-1,1]) product (circle Lebesgue measure).
```

Thus a cap sector of angular width `2r` has area `2r(1-c)`, including
hemispheres, poles, and full angular width. This supplies actual spherical
coordinates for the remaining cap-intersection integrals; their explicit
inverse-trigonometric evaluation and the edge curvature integrals remain open.

## Milestone 48: actual cap intersections as latitude integrals

`SphereCoordinates.lean` reconstructs every unit vector from its height and
longitude, including both poles, and proves Fubini formulas on the full sphere
and on a cap. `LongitudeSlice.lean` evaluates the angular measure of
`cos(theta) >= q` as `2 arccos(q)` for every real `q`, using the clamped
inverse cosine outside `[-1,1]`.

`CapLensSlices.lean` then reduces a coordinate lens to a single real integral.
`CapLensCoordinates.lean` constructs two orthogonal reflections that put any
pair of unit axes in those coordinates. For nonparallel unit axes `u,v`,
`c = <u,v>`, and a continuous height weight `g`, it proves

```text
integral_{<u,n> >= a, <v,n> >= b} g(<u,n>) d sigma
  = integral_{a}^{1} 2 arccos((b-c z)/(sqrt(1-c^2) sqrt(1-z^2))) g(z) dz.
```

This includes the actual lens area (`g=1`) and its first moment along the
first axis (`g(z)=z`). Endpoint values do not affect the integral, as proved
using the null singleton sets. Evaluating these one-dimensional integrals in
closed form, and the edge curvature integrals, remains necessary for the
separable volume formulas.

## Milestone 49: exact closed-form lens area and first moment

`LensScalar.lean` proves the two antiderivatives, and `LensUpperHeight.lean`
identifies the upper crossing latitude and the limiting angles there. It also
determines whether the latitude slices above that crossing are full or empty.
`LensIntegrals.lean` applies the fundamental theorem of calculus, with the
continuity, integrability, and endpoint values proved explicitly.

For unit cap axes `u,v`, set `c=<u,v>`, `D=1-a^2-b^2-c^2+2abc`, and

```text
alpha = arccos((b-ac)/(sqrt(1-a^2) sqrt(1-c^2))),
beta  = arccos((a-bc)/(sqrt(1-b^2) sqrt(1-c^2))),
phi   = arccos((c-ab)/(sqrt(1-a^2) sqrt(1-b^2))).
```

`CapLensFormula.lean` evaluates the actual intersection of the caps
`<u,n> >= a` and `<v,n> >= b`:

```text
area = 2 pi - 2 phi - 2 a alpha - 2 b beta,
integral <u,n> d sigma = (1-a^2) alpha + (1-b^2) c beta - b sqrt(D).
```

The proved hypotheses are `a,b,c` in `(-1,1)`, `D>0`, and `b != c`; the
last condition excludes an upper crossing at the pole. These formulas now
require substitution into the actual clipped-face sums. The integrated edge
curvature contributions to `M_C` and the final separable identities remain open.

## Milestone 50: explicit clipped volume and surface area

`ClippedLensParameters.lean` verifies every hypothesis of the lens formulas
from the original balanced-contact assumptions and `A <= 2/25`. In particular,
it proves `37/100 <= R^2 <= 3/8`, every squared edge length is at least `23/25`,
and both kinds of lens have positive Gram determinant. These estimates include
zero edge deficits.

`ClippedLensFaces.lean` normalizes the actual cap axes and evaluates each
contact-face lens, its center-weighted first moment, and each pair of excluded
enclosing-sphere caps. `ClippedVolumeLenses.lean` substitutes these evaluations
into the geometric area and volume integrals. Write `B` for the base cap area,
`J` for its center-weighted moment, `L(s)` and `N(s)` for a contact lens area
and moment, and `P(s)` for an enclosing-sphere lens area. All are explicit
inverse-trigonometric expressions proved equal to their actual integrals. With
`T = 4 pi - 8 pi (2-1/(2R^2))`, the proved formulas are

```text
S_C = R^2 (T + sum P(s)) - 8 B + 2 sum L(s),
V_C = (-8 B - 8 J + R^3 T)/3
      + sum (2 L(s) + 2 N(s) + R^3 P(s))/3.
```

Each sum runs over the six unordered contact pairs. Thus the actual clipped
volume now has an explicit separable formula. Rewriting its scalar terms in
the manuscript's angle notation, proving the remaining edge contributions to
`M_C`, and deriving the explicit dual-body formula are still pending.

## Milestone 51: zero vertex curvature and exact normal-wedge integrals

`ThreeActiveCurvature.lean` proves that three active unit-ball normals are
linearly independent throughout the deficit range. It also proves independence
for two active unit balls and the enclosing sphere, using the exact Gram
determinant. The actual support-map derivative annihilates each active normal,
so it is zero at every such support point. In particular, these vertex normal
regions contribute zero to the integrated curvature trace.

`LongitudeWedgeIntegral.lean` evaluates the circle-curvature density over an
actual spherical height-longitude wedge:

```text
integral_{a <= height <= b, longitude in S} r/sqrt(1-height^2) d sigma
  = r length(S) (arcsin(b)-arcsin(a)).
```

The specializations give `2 r length(S) arcsin(s/2)` for a unit--unit
normal wedge and `r length(S) arccos(1/(2R))` for a unit--enclosing-sphere
normal wedge. These are spherical integral identities. Identifying all actual
edge normal regions with the wedges and assembling their curvature integrals
into `M_C` are still separate outstanding obligations.

## Milestone 52: necessary normal cones at actual edges

`ActiveSupportLocalization.lean` proves that inactive ball constraints can be
deleted when finding a support maximum: they hold locally, and a local maximum
of a linear functional on a convex set is global. With exactly one possible
active constraint, the actual support point is the explicit spherical face
point.

`TwoBallSupport.lean` proves the necessary axial bounds for a support point on
both boundaries of a two-ball intersection. `ClippedActiveSupport.lean` applies
them to the actual clipped body. When the other constraints are strict, the
unit--unit edge has normal height in `[-s/2,s/2]`, and the unit--enclosing-sphere
edge has normal height in `[-1/(2R),1-1/(2R^2)]`. In both cases the actual support
point is proved equal to its explicit circle candidate. These necessity results
complement the earlier sufficient unit--unit normal-cone theorem. The remaining
enclosing-sphere edge curvature, boundary bookkeeping, and integral assembly
are not yet complete.

## Complete projective suite: kernel verification pending

`scripts/generate_projective_suite.py` now emits the proposed proofs for all
584 boxes, using 76,784 separate kernel row checks. The grid sizes vary by box:
the proposals use 568,064 point cells and 3,243,136 gradient cells. Their exact
rational acceptance margins are positive. These external calculations and
generated proof texts do not establish the all-box theorem before compilation.
`Generated/ProjectiveProposalChecks.lean`, included in the default build, checks
the new candidates' exact box cover and rational acceptance arithmetic in Lean;
it does not assume or certify their proposed center and gradient enclosures.

`Generated/ProjectiveKernel/Box*.lean` recomputes every parameter interval,
parameter jet, and row total with `decide +kernel`. The corresponding
`Generated/ProjectiveBoxes/Box*.lean` files assemble the complete analytic
certificates. `Generated/ProjectiveSuite.lean` connects their exact box list
to the proved cover and states the resulting unconditional affine bound.
This suite is not yet imported by the default library target while its full
kernel verification is pending.

The separate **Complete projective kernel certificate** workflow checks 64
balanced shards, with one box at a time in each runner. Completed module
artifacts are cached even if a later box fails. Only after all shards pass
does the assembly job compile the analytic certificates and run
`ProjectiveAxiomAudit.lean`. It refuses to recompute missing kernel shards in
the assembly runner. Each arithmetic runner fetches only the small mathlib
dependency cache it needs.

To reproduce the proposed integers from this repository's root:

```sh
g++ -std=c++17 -O3 lean/scripts/propose_projective.cpp -o /tmp/propose-projective
/tmp/propose-projective lean/data/projective_grids.txt > /tmp/projective-proposals.json
cmp /tmp/projective-proposals.json lean/data/projective_proposals.json
```

To check the suite serially on a machine with limited memory, run
`python3 lean/scripts/projective_ci.py build NN` for every shard `00` through
`63`, then `python3 lean/scripts/projective_ci.py assemble`. This is a long
kernel computation. Existing local mathlib artifacts continue to use the
shared Lake cache; the transfer script also preserves cache hard links when
replacing build files.

## Remaining proof obligations

The larger-radius completion branch still needs the edge curvature integrals,
the explicit dual-body volume formula and the scalar identities matching the
manuscript's coefficients,
completed kernel verification of the full
completion-integral certificate, the clipped-hull certificate verifier and its
kernel checks, and final assembly. None of these is hidden behind a custom axiom
or an assumed instance claiming the main theorem.
The radial branch and the support-volume formula need no further smoothing.

A fresh execution of the original Python/C++ verifier at 52/192-bit precision
passed on 2026-11-15: 584 integral rectangles, 3,200 derivative boxes, 512 hull
intervals, and eight radial rows. That execution is external numerical evidence;
it is not a kernel verification of the certificate algorithms or their geometric
soundness.
