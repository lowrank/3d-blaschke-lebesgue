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

**Boundary:** the arithmetic row theorems do not yet bound the volume of an arbitrary
body. Milestones 5 and 6 prove both cap bounds, their disjointness, and the
pointwise tangent-deficit estimates. Milestone 7 integrates these contributions
against the actual spherical measure. The surface-area comparison and Blaschke
identity needed to turn the resulting integral into a volume bound remain open.
The completion-integral and clipped-hull
finite certificates have not yet been checked in Lean.

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
contacts. Milestone 7 supplies the spherical integration; the volume conclusion
is still unproved.

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

**Boundary:** these integral bounds still need the geometric surface-area
comparison and Blaschke's mixed-volume identity to imply the radial branch's
volume bound. The near-Jung completion branch also remains incomplete.

## Remaining proof obligations

The main proof still needs quantitative tetrahedral geometry,
mixed-volume and curvature variation identities, clipped-body boundary formulas,
the antipodal completion integral, the radial surface-area inequality,
the completion-integral and clipped-hull certificate verifiers, and final smoothing
and assembly. None of these is hidden behind a custom axiom
or an assumed instance claiming the main theorem.

A fresh execution of the original Python/C++ verifier at 52/192-bit precision
passed on 2026-11-15: 584 integral rectangles, 3,200 derivative boxes, 512 hull
intervals, and eight radial rows. That execution is external numerical evidence;
it is not a kernel verification of the certificate algorithms or their geometric
soundness.
