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
body. The geometric propagation, disjoint spherical caps, and integration of their
contributions still need to be formalized. The completion-integral and clipped-hull
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

## Remaining proof obligations

The main proof still needs quantitative tetrahedral geometry,
mixed-volume and curvature variation identities, clipped-body boundary formulas,
the antipodal completion integral, the radial integration and geometric cap estimates,
the completion-integral and clipped-hull certificate verifiers, and final smoothing
and assembly. None of these is hidden behind a custom axiom
or an assumed instance claiming the main theorem.

A fresh execution of the original Python/C++ verifier at 52/192-bit precision
passed on 2026-11-15: 584 integral rectangles, 3,200 derivative boxes, 512 hull
intervals, and eight radial rows. That execution is external numerical evidence;
it is not a kernel verification of the certificate algorithms or their geometric
soundness.
