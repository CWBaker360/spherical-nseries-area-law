# A Spherical N-Series Area Law for Regular Refinement Families

**Author:** C. Wayne Baker  
**Date:** June 3, 2026  
**Status:** Revised numerical/conjectural paper and reproducibility archive

This repository studies scale cancellation for geometric area approximations on the unit sphere. Four regular refinement families exhibit the order ladder

\[
2\longrightarrow4\longrightarrow6\longrightarrow8,
\]

while a perturbed-grid experiment marks the boundary of the clean high-order regime.

## Authoritative paper

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

## Rights

Copyright © 2026 C. Wayne Baker. All rights reserved unless otherwise stated.


## October 30, 2026 source update (PDF synchronization pending)

The reviewed October 29, 2026 manuscript source (v2.3) is now at [`paper/spherical_nseries_v2_3.tex`](paper/spherical_nseries_v2_3.tex). This versioned source was added without modifying the existing authoritative `paper/` LaTeX/PDF pair. The companion v2.3 PDF has **not yet been uploaded**, so links to the existing PDF still point to the previous version. Do not cite that PDF as v2.3 until the matched PDF is committed.
