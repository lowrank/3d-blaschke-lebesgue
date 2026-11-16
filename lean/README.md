# Lean 4.35 formalization

**Status: incomplete. The manuscript's volume theorem has not yet been proved in Lean.**

Source: `volume_bound_04144.tex` at upstream commit
`8e57642c283f232ae9a782ad86408bfb7182dfb0`. The target is the strict bound
`Vol(K) > (259/625) * w^3` for three-dimensional convex bodies of constant width
`w > 0`. `BlaschkeLebesgue.ConstantWidthVolumeBound` records this statement using
Lebesgue volume, compact convex sets, nonempty interior, and opposite support
functions. It is a proposition definition, not a proved theorem.

## Build and audit

From this directory:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Lean is pinned to **4.35.0**, and mathlib to its matching release
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Lake's local artifact cache is enabled;
restored build files use hard links to the shared cache rather than independent
copies. No machine-specific dependency paths are committed.

CI runs the build, audits all declarations in the `BlaschkeLebesgue` namespace,
and checks the existing manuscript report provenance. The axiom audit permits
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

## Remaining proof obligations

The main proof still needs the minimum circumsphere and balanced contacts,
mixed-volume and curvature variation identities, clipped-body boundary formulas,
the antipodal completion integral, the radial integration and cap estimates,
sound Lean verifiers for all three finite certificate families, and final
smoothing, assembly, and rescaling. None of these is hidden behind a custom axiom
or an assumed instance claiming the main theorem.

A fresh execution of the original Python/C++ verifier at 52/192-bit precision
passed on 2026-11-15: 584 integral rectangles, 3,200 derivative boxes, 512 hull
intervals, and eight radial rows. That execution is external numerical evidence;
it is not a kernel verification of the certificate algorithms or their geometric
soundness.
