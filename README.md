# A self-contained proof of the 0.4144 constant-width volume bound

## Main manuscript

`volume_bound_04144.pdf` and `volume_bound_04144.tex` give the detailed
33-page proof of

    Vol(K) > (259/625) w^3 = 0.4144 w^3

for every three-dimensional convex body of constant width w > 0. Improving
the existing result by Hyra's [0.411040](https://github.com/Tencent-Hunyuan/Hyra-results/tree/main/AI4Science/3d_blaschke_lebesgue).


The manuscript includes support-function and mixed-volume preliminaries,
Blaschke's relation, all contact and clipping arguments, the complete
spherical-face/edge volume derivation, the weighted completion estimate,
projective normal coordinates, the radial argument, and the finite
verification statements. Its three illustrations are embedded TikZ code.
No separate illustration files or other working manuscripts are needed.

The bibliography contains public mathematical references only. The
computer-assisted theorem is not a proof of the sharp Meissner conjecture.

## Full numerical verification

Requirements: Python 3 and a C++17 compiler supporting signed 128-bit integers
(the command uses g++). No third-party Python package is required.

From the package root:

    cd verification
    python verify.py --output reports/recheck_48_128
    python verify.py --cpp-bits 52 --interval-bits 192 --output reports/recheck_52_192

Each command reconstructs the adaptive integration certificate, recompiles
the C++ program, recomputes every accepted cell, independently checks the
complete parameter cover, checks the geometric constants, computes the
clipped-hull derivative and secant estimates, and verifies every rational
radial propagation step. It does not trust stored numerical endpoints.

Two complete executions were performed for this manuscript and are supplied:

- `verification/reports/run_48_128/`
- `verification/reports/run_52_192/`

Both passed. Each verifies 584 accepted integral parameter rectangles,
3,200 derivative boxes, 512 clipped-hull radius intervals, and eight radial
rows. The integral check uses 192 x 192 point-parameter quadrature cells and
a separate 64 x 64 derivative grid. All acceptance comparisons are exact
integer or rational comparisons, with outward intervals where required.

The smallest resulting global bound is the exact fraction recorded under
`global_lower` in each `complete_report.json`. It exceeds the conservative
rational number 4144109/10000000, which exceeds 259/625.

The two runs use the same implementation at different precisions. They are
not two independently developed mathematical proofs, and the result has not
been formally verified in a proof assistant or independently peer-reviewed.
The analytic implications connecting the finite certificates to the theorem
are proved in the manuscript; successful software execution alone does not
replace those implications.

## A short report-provenance audit

From the package root:

    python verify_manuscript.py

This checks source/data hashes against BOTH complete reports, their stated
counts, and the exact comparisons supporting the manuscript's compressed
constants. It reads the reports and is NOT a substitute for the full
numerical verification commands above.

`manuscript_audit.json` records the completed audit.

## Continuing toward the sharp gap

`continuation/quadratic_support_program.pdf` and its TeX source give a
separate seven-page analytical continuation. It develops an exactly rational
quadratic energy matrix for finite support values on an antipodal spherical
triangulation. Exact support-point interpolation retains genuine
constant-width realizability, and an explicit error bounds the difference
between the quadratic objective and the volume of any completion.

The finite objective is a concave quadratic to be minimized over convex
second-order-cone constraints. The optimization is NONCONVEX. No competitive
global optimization, sharper numerical bound, or sharpness theorem is
claimed in this continuation.

To reproduce its exact finite algebra checks, using the Python standard
library only:

    cd continuation
    python check_rational_energy.py --output recheck

The script enumerates supporting facets using exact fractions, constructs
antipodally paired triangulations, checks the closed oriented covers,
assembles the rational energy matrices, proves positive semidefiniteness by
exact elimination on the odd subspace, checks translation nullspaces, and
checks a nonspherical feasible test body's support data. The shipped
`continuation/reports/` contains the two exact matrices, triangulations,
and successful report. The test energies are evaluations, NOT optimized
bounds.

## Building the PDFs

A standard LaTeX installation with pdfLaTeX, Latin Modern, microtype, AMS
packages, booktabs, longtable, TikZ, hyperref, and cleveref is sufficient.
From the package root run:

    sh build.sh

The verification programs do not require LaTeX.

## File integrity

`SHA256SUMS.txt` lists the delivered file hashes. Compiler binaries, LaTeX
intermediates, cache files, and visual-QA images are not part of this release.
The complete numerical reports include their own source/data hashes.
