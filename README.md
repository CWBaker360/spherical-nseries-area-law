# A Spherical N-Series Area Law for Regular Refinement Families

**Author:** C. Wayne Baker  
**Date:** June 3, 2026  
**Status:** Revised numerical/conjectural paper and reproducibility archive

This repository studies scale cancellation for geometric area approximations on the unit sphere. Four regular refinement families exhibit the order ladder

\[
2\longrightarrow4\longrightarrow6\longrightarrow8,
\]

while a perturbed-grid experiment marks the boundary of the clean high-order regime.


## Current reviewed manuscript — v2.3 (October 29, 2026)

- [Read v2.3 PDF](paper/spherical_nseries_v2_3.pdf)
- [LaTeX source v2.3](paper/spherical_nseries_v2_3.tex)

These are the latest reviewed manuscript files. Earlier `paper/spherical_nseries_area_law.*` files are retained for version history. Empirical observations are not proofs of a universal law, and pre-asymptotic fit behavior should not be interpreted as a precision floor.


## Earlier manuscript files (retained)

- [`paper/spherical_nseries_area_law.pdf`](paper/spherical_nseries_area_law.pdf)
- [`paper/spherical_nseries_area_law.tex`](paper/spherical_nseries_area_law.tex)

## Evidence families

- spherical caps with geodesic polygon boundaries;
- chordal triangulations of right spherical triangles;
- chordal latitude-longitude cells;
- fixed irregular spherical polygon domains under regular fan refinement;
- smooth interior-grid perturbations as a regularity stress test.

## Mathematical status

The scale operators and their moment cancellation are exact conditional statements. The general spherical even-power area law is conjectural. The tables are numerical evidence for the tested families, not a theorem for arbitrary spherical meshes.

The perturbation table is diagnostic: values above a nominal operator order are not interpreted as genuine superconvergence. They show that a one-step observed-order quotient is not identifying a stable asymptotic regime in those cases.

## Reproduce the smoke audit

```bash
python -m pip install mpmath
python scripts/spherical_nseries_area_suite.py --case smoke --N 4 --dps 70 --outdir output
```

The compatibility wrappers preserve the historical script names recorded in the manuscript.

## Supplementary Lean 4 verification — November 24, 2026

Independent Linux verification successfully reproduced all 31 Lean modules, 126 declaration axiom audits and 65 archived file checksums.

Both principal theorems passed:
- `BakerSpherical.AreaLaw.spherical_area_law`
- `BakerSpherical.AreaLaw.richardson_fourth_order`

Standard axioms only: `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` dependencies.

Environment: Lean v4.36.0-rc2; Mathlib revision ccd6c8476363fc81f2e4bee2eeb1a62c99338549.

The verification covers the fixed regular-patch fourth-order area law and Richardson cancellation under the stated smoothness and nondegeneracy assumptions. Universal even-power convergence, sixth- and eighth-order convergence, and arbitrary mesh deformation remain outside its scope.

- [Lean verification archive](https://github.com/CWBaker360/spherical-nseries-area-law/tree/42dbeed373302498cd1b4d8c189fafb44bd316ac/lean-verification/theorem2-regular-patch-2026-11-11)
- [Successful automated verification](https://github.com/CWBaker360/spherical-nseries-area-law/actions/runs/45423440967)

The published v2.3 manuscript and original numerical archive remain unchanged.

## Rights

Copyright © 2026 C. Wayne Baker. All rights reserved unless otherwise stated.

