# Reproducibility

## Requirements

- Python 3.10 or newer
- `mpmath`
- a LaTeX distribution with `pdflatex`

Install the numerical dependency:

```bash
python -m pip install mpmath
```

## Fast audit

```bash
python scripts/spherical_nseries_area_suite.py --case smoke --N 4 --dps 70 --outdir output
```

## Individual geometries

```bash
python scripts/spherical_area_nseries_cap_test.py --N 8 --dps 100 --outdir output/cap
python scripts/spherical_triangle_nseries_area_test.py --N 8 --dps 80 --outdir output/triangle
python scripts/spherical_latlon_cell_nseries_area_test.py --N 8 --dps 80 --outdir output/latlon
python scripts/spherical_irregular_polygon_nseries_test.py --N 8 --dps 80 --outdir output/irregular
python scripts/spherical_perturbed_latlon_nseries_test.py --N 8 --dps 80 --outdir output/perturbed
```

Larger base values require evaluations through `16N` to form two consecutive four-scale residuals, so runtime increases rapidly for triangle and polygon patches.

The CSV files under `output/` record the manuscript's reported tables. The smoke suite independently checks the operator moments and representative geometric convergence behavior.
