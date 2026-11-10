#!/usr/bin/env python3
"""Cross-check of the C2(0) and C2'(0) integrals without Arb (no python-flint needed).

Builds the same symbolic integrands as c2prime_enclosure.py, compiles them to NumPy (float64)
and integrates with tensor Gauss-Legendre rules of increasing size. Not a rigorous enclosure:
it is a second execution of the integral by an unrelated method, accurate to about 14 digits.
Requires: sympy, numpy.
"""
import os
import numpy as np
import sympy as sp
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "c2prime_enclosure.py")).read()
exec(src.split("# ---- 2. numerical guards")[0].replace("from flint import acb, arb, ctx", ""))  # NumPy test does not require FLINT
f0 = sp.lambdify((s, t), E0, "numpy", cse=True)
f1 = sp.lambdify((s, t), E1, "numpy", cse=True)
ref = {"C2(0) ": -0.01189423662103184634603051, "C2'(0)": -0.000680779112122198}
for name, f in (("C2(0) ", f0), ("C2'(0)", f1)):
    for n in (20, 40, 80):
        x, w = np.polynomial.legendre.leggauss(n)
        x = (x + 1) / 2; w = w / 2
        S, T = np.meshgrid(x, x, indexing="ij")
        v = float((np.outer(w, w) * f(S, T)).sum())
        print(f"{name} Gauss-Legendre {n:2d}x{n:<2d}: {v:.18f}   minus Arb midpoint: {v - ref[name]: .2e}")
