#!/usr/bin/env python3
"""Check of the proof supplement's coefficient formula against the measured C2(delta).

The supplement's proof gives  C2(delta) = B0[q2(.,delta)] + B2[q0(.,delta)], where
  G(x,h,delta) = h^2 ( q0 + q2 h^2 + q4 h^4 + ... )   is the paired-cell chordal area, and for
  the midpoint rule on the unit square  B0[q] = int q,   B2[q] = -(1/24) int (q_ss + q_tt).
Here q0, q2 are extracted cell by cell (no grid sums are used), integrated by Gauss-Legendre
quadrature, and compared with the C2(delta) obtained from the N -> infinity grid sums in
cubic_amplitude_test_mpfr.py.  Arithmetic: numpy long double.
"""
import numpy as np
LD = np.longdouble
PI = LD("3.14159265358979323846264338327950288"); D = PI / 180
P0, P1, L0, L1 = 30 * D, 60 * D, LD(0), 30 * D

def F(s, t, d):
    b = np.sin(PI * s) * np.sin(PI * t)
    s2 = s + d * b * np.cos(2 * t + LD("0.3")); t2 = t + d * b * np.sin(3 * s + LD("0.7"))
    ph = P0 + (P1 - P0) * s2; la = L0 + (L1 - L0) * t2
    return np.stack([np.cos(ph) * np.cos(la), np.cos(ph) * np.sin(la), np.sin(ph)], -1)

def g(s, t, h, d):                       # paired-cell area divided by h^2
    k = h / 2
    p00, p10, p11, p01 = F(s - k, t - k, d), F(s + k, t - k, d), F(s + k, t + k, d), F(s - k, t + k, d)
    ar = lambda a, b, c: np.sqrt((np.cross(b - a, c - a) ** 2).sum(-1)) / 2
    return (ar(p00, p10, p11) + ar(p00, p11, p01)) / (h * h)

def q0q2(s, t, d):                       # fit g = q0 + q2 h^2 + q4 h^4 + q6 h^6 at four h
    hs = [LD("0.04"), LD("0.02"), LD("0.01"), LD("0.005")]
    V = np.array([[h ** (2 * k) for k in range(4)] for h in hs], dtype=LD)
    W = np.linalg.inv(V.astype(np.float64)).astype(LD)       # refine once in long double
    W = W + W @ (np.eye(4, dtype=LD) - V @ W)
    vals = np.stack([g(s, t, h, d) for h in hs], 0)
    return np.tensordot(W[0], vals, 1), np.tensordot(W[1], vals, 1)

def evenness(d):                          # max |g(h) - g(-h)| / g over a sample
    s, t = np.meshgrid(np.linspace(0.05, 0.95, 19).astype(LD), np.linspace(0.05, 0.95, 19).astype(LD))
    h = LD("0.03")
    return float(np.max(np.abs(g(s, t, h, d) - g(s, t, -h, d)) / g(s, t, h, d)))

def C2(d, n=48):
    d = LD(d)
    x, w = np.polynomial.legendre.leggauss(n)
    x = ((x + 1) / 2).astype(LD); w = (w / 2).astype(LD)
    S, T = np.meshgrid(x, x, indexing="ij"); Wt = np.outer(w, w)
    e = LD("0.002")
    q0 = lambda s, t: q0q2(s, t, d)[0]
    lap = sum((-q0(S + 2 * a * e, T + 2 * b * e) + 16 * q0(S + a * e, T + b * e) - 30 * q0(S, T)
               + 16 * q0(S - a * e, T - b * e) - q0(S - 2 * a * e, T - 2 * b * e)) / (12 * e * e)
              for a, b in ((1, 0), (0, 1)))
    q2 = q0q2(S, T, d)[1]
    return (Wt * q2).sum() - (Wt * lap).sum() / 24, (Wt * q0(S, T)).sum()

target = {"0": -0.011894236621, "0.02": -0.011909672914, "-0.02": -0.011881749496,
          "0.04": -0.011929781535, "-0.04": -0.011869747851}
A = (L1 - L0) * (np.sin(P1) - np.sin(P0))
print("evenness of the paired cell, max |g(h)-g(-h)|/g:", [f"{evenness(LD(d)):.1e}" for d in ("0", "0.04", "-0.04")])
print(f"{'delta':>6} | {'C2 from proof formula':>22} | {'C2 from grid sums':>18} | diff     | int q0 - A")
for d, tv in target.items():
    c, i0 = C2(d)
    print(f"{d:>6} | {float(c):22.12f} | {tv:18.12f} | {float(c) - tv: .1e} | {float(i0 - A): .1e}")
vals = {d: C2(d)[0] for d in ("0.005", "-0.005", "0.01", "-0.01")}
d1 = (vals["0.005"] - vals["-0.005"]) / LD("0.01"); d2 = (vals["0.01"] - vals["-0.01"]) / LD("0.02")
print(f"C2'(0) from the proof formula: step .005 -> {float(d1):.10f}, step .01 -> {float(d2):.10f}, "
      f"extrapolated {float((4 * d1 - d2) / 3):.10f}   (grid-sum estimate: -0.0006806403)")
