#!/usr/bin/env python3
"""Numerical test of the conditional cubic mechanism (Proposition "Scale-dependent
perturbations can create odd powers") for a chordally triangulated latitude-longitude cell.

Deterministic, no random numbers. Arithmetic: numpy long double (x86 extended, ~18-19 digits).

Cell: latitude 30..60 deg, longitude 0..30 deg; exact area (lam1-lam0)(sin phi1 - sin phi0).
Grid: uniform N x N in normalized parameters (s,t) in [0,1]^2, each cell split along its
      (p00,p11) diagonal; area rule = sum of Euclidean (chordal) triangle areas.
Perturbation field (smooth, vanishing on the boundary of the parameter square):
      V(s,t) = sin(pi s) sin(pi t) * ( cos(2t + 0.3), sin(3s + 0.7) )
Nodes are displaced to (s,t) + delta * V(s,t).

Family F (fixed map):      delta fixed, independent of N  -> classical theorem predicts an
                           even-power expansion; C2(delta) is read off from it.
Family S (scale-dependent): delta = eps / N               -> the proposition predicts an h^3
                           term with coefficient eps*C2'(0), and residuals
                           -1/6, -1/90, -1/810 times eps*C2'(0) h^3 after the 2-, 3-, 4-scale
                           even-power operators.
"""
import numpy as np

LD = np.longdouble
PI = LD(np.pi) if False else LD("3.14159265358979323846264338327950288")
D2R = PI / 180
PHI0, PHI1, LAM0, LAM1 = 30 * D2R, 60 * D2R, 0 * D2R, 30 * D2R
EXACT = (LAM1 - LAM0) * (np.sin(PHI1) - np.sin(PHI0))


def area(N, delta):
    s, t = np.meshgrid(np.arange(N + 1, dtype=LD) / N, np.arange(N + 1, dtype=LD) / N, indexing="ij")
    bump = np.sin(PI * s) * np.sin(PI * t)
    s2 = s + LD(delta) * bump * np.cos(2 * t + LD("0.3"))
    t2 = t + LD(delta) * bump * np.sin(3 * s + LD("0.7"))
    phi = PHI0 + (PHI1 - PHI0) * s2
    lam = LAM0 + (LAM1 - LAM0) * t2
    P = np.stack([np.cos(phi) * np.cos(lam), np.cos(phi) * np.sin(lam), np.sin(phi)], axis=-1)
    p00, p10, p11, p01 = P[:-1, :-1], P[1:, :-1], P[1:, 1:], P[:-1, 1:]

    def tri(a, b, c):
        x = np.cross(b - a, c - a)
        return np.sqrt((x * x).sum(-1)) / 2

    vals = np.concatenate([tri(p00, p10, p11).ravel(), tri(p00, p11, p01).ravel()])
    vals.sort()
    return vals.sum(dtype=LD)


def ops(a, N):
    """Errors of raw, 2-, 3-, 4-scale even-power operators at base N (a: dict N -> A_N)."""
    e = [a[N],
         (4 * a[2 * N] - a[N]) / 3,
         a[N] / 45 - 4 * a[2 * N] / 9 + 64 * a[4 * N] / 45,
         -a[N] / 2835 + 4 * a[2 * N] / 135 - 64 * a[4 * N] / 135 + 4096 * a[8 * N] / 2835]
    return [x - EXACT for x in e]


def order(e1, e2):
    return float(np.log2(abs(e1 / e2)))


NS = [8, 16, 32, 64, 128, 256, 512, 1024]
fmt = lambda x: f"{float(x): .6e}"

print("=== Family F: fixed displacement delta (independent of N) ===")
print("observed orders, base N=32 vs 64:  raw / 2-scale / 3-scale / 4-scale ;  C2(delta) estimate")
C2 = {}
for delta in ["0", "0.02", "-0.02", "0.04", "-0.04"]:
    a = {N: area(N, delta) for N in NS[:7]}
    o = [order(x, y) for x, y in zip(ops(a, 32), ops(a, 64))]
    # C2 from the h^2 coefficient with h^4,h^6 removed: Richardson on e_N * N^2
    g = {N: (a[N] - EXACT) * N * N for N in (64, 128, 256, 512)}
    c2 = (64 * g[512] - 20 * g[256] + g[128]) / 45
    C2[delta] = c2
    print(f"delta={delta:>6}:  " + "  ".join(f"{x:7.4f}" for x in o) + f"   C2 = {float(c2): .12f}")
d1 = (C2["0.02"] - C2["-0.02"]) / LD("0.04")
d2 = (C2["0.04"] - C2["-0.04"]) / LD("0.08")
C2p = (4 * d1 - d2) / 3
print(f"C2'(0) from central differences: {float(d1):.10f} (step .02), {float(d2):.10f} (step .04), "
      f"extrapolated {float(C2p):.10f}")

print("\n=== Family S: scale-dependent displacement delta = eps/N ===")
print("b3 estimates from the 2-scale residual (-6 e2 N^3) at base N; predicted b3 = eps*C2'(0)")
rows = {}
for eps in ["0.1", "-0.1", "0.2", "-0.2"]:
    a = {N: area(N, LD(eps) / N) for N in NS}
    rows[eps] = a
    b3 = {N: -6 * ops(a, N)[1] * LD(N) ** 3 for N in (16, 32, 64, 128)}
    # one Richardson step in 1/N to remove the O(h) drift of the estimate
    b3x = 2 * b3[128] - b3[64]
    print(f"eps={eps:>5}: " + "  ".join(f"N={N}: {float(v): .8f}" for N, v in b3.items())
          + f"   extrap {float(b3x): .8f}   predicted {float(LD(eps) * C2p): .8f}")

print("\nresidual ratios (prediction: e3/e2 -> 1/15 = 0.066667, e4/e3 -> 1/9 = 0.111111)")
for eps in ["0.1", "0.2"]:
    a = rows[eps]
    for N in (16, 32, 64, 128):
        e = ops(a, N)
        print(f"eps={eps} N={N:3d}: e2={fmt(e[1])} e3={fmt(e[2])} e4={fmt(e[3])}   "
              f"e3/e2={float(e[2] / e[1]):.6f}  e4/e3={float(e[3] / e[2]):.6f}")

print("\nobserved orders in family S (base N=32 vs 64 and N=64 vs 128): raw / 2- / 3- / 4-scale")
for eps in ["0.1", "0.2"]:
    a = rows[eps]
    for N in (32, 64):
        print(f"eps={eps} N={N}: " + "  ".join(f"{order(x, y):7.4f}" for x, y in zip(ops(a, N), ops(a, 2 * N))))

print("\nodd/even split of the 2-scale residual in eps (N=64): odd part should carry the h^3 term")
for e_ in ["0.1", "0.2"]:
    ep, em = ops(rows[e_], 64)[1], ops(rows["-" + e_], 64)[1]
    print(f"eps={e_}: odd part {fmt((ep - em) / 2)}   even part {fmt((ep + em) / 2)}")

print("\nmixed-exponent operator {2,3} (weights 1/21, -4/7, 32/21): observed order, expect 4")
for eps in ["0.1", "0.2"]:
    a = rows[eps]
    m = lambda N: a[N] / 21 - 4 * a[2 * N] / 7 + 32 * a[4 * N] / 21 - EXACT
    print(f"eps={eps}: N=32->64: {order(m(32), m(64)):.4f}   N=64->128: {order(m(64), m(128)):.4f}")
