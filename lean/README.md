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

## Remaining proof obligations

The larger-radius completion branch still needs the clipped-body boundary
decomposition and volume formulas, the completion-integral and clipped-hull certificate
verifiers, and final assembly. None of these is hidden behind a custom axiom
or an assumed instance claiming the main theorem.
The radial branch and the support-volume formula need no further smoothing.

A fresh execution of the original Python/C++ verifier at 52/192-bit precision
passed on 2026-11-15: 584 integral rectangles, 3,200 derivative boxes, 512 hull
intervals, and eight radial rows. That execution is external numerical evidence;
it is not a kernel verification of the certificate algorithms or their geometric
soundness.
