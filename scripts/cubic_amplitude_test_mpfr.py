#!/usr/bin/env python3
"""Second implementation of the cubic amplitude test, in arbitrary precision.

Purpose: remove the platform dependence of scripts/cubic_amplitude_test.py (which uses the
C 'long double' type) and add a numerical triangle-orientation check.

Arithmetic: MPFR via gmpy2 at 160 bits (about 48 significant digits), identical on every
platform. Written separately from the long-double script: scalar loops, exact node formulas,
plain left-to-right summation. Same cell, grid, diagonal and displacement field:

  cell   latitude 30..60 deg, longitude 0..30 deg
  grid   uniform N x N in (s,t) in [0,1]^2, cells split along (p00,p11)
  field  V(s,t) = sin(pi s) sin(pi t) * ( cos(2t + 3/10), sin(3s + 7/10) )
  nodes  (s,t) + delta * V(s,t);   family F: delta fixed;   family S: delta = eps / N

Orientation check, for every triangle of every run:
  (a) the signed area of the displaced triangle in the parameter plane, divided by the
      undisplaced value, must be positive (1 = undisplaced);
  (b) the chordal triangle's normal must point outward (normal . centroid > 0).
The minimum of (a) over all triangles is reported.

Usage: python3 cubic_amplitude_test_mpfr.py [NMAX]     (default 1024; needs: pip install gmpy2)
"""
import sys
from multiprocessing import Pool
import gmpy2
from gmpy2 import mpfr, sin, cos, sqrt, log2

BITS = 160
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1024


def setup():
    gmpy2.get_context().precision = BITS


def consts():
    pi = gmpy2.const_pi()
    d = pi / 180
    return pi, 30 * d, 60 * d, mpfr(0), 30 * d


def area(args):
    """Return (chordal area, min normalized parameter-plane signed area, bad-orientation count)."""
    N, delta_s, scaled = args
    setup()
    pi, phi0, phi1, lam0, lam1 = consts()
    delta = mpfr(delta_s) / N if scaled else mpfr(delta_s)
    c03, c07 = mpfr(3) / 10, mpfr(7) / 10
    S, T, X, Y, Z = [], [], [], [], []
    for i in range(N + 1):
        s = mpfr(i) / N
        rs, rt, rx, ry, rz = [], [], [], [], []
        for j in range(N + 1):
            t = mpfr(j) / N
            bump = sin(pi * s) * sin(pi * t)
            s2 = s + delta * bump * cos(2 * t + c03)
            t2 = t + delta * bump * sin(3 * s + c07)
            ph = phi0 + (phi1 - phi0) * s2
            la = lam0 + (lam1 - lam0) * t2
            cp = cos(ph)
            rs.append(s2); rt.append(t2)
            rx.append(cp * cos(la)); ry.append(cp * sin(la)); rz.append(sin(ph))
        S.append(rs); T.append(rt); X.append(rx); Y.append(ry); Z.append(rz)

    total = mpfr(0)
    jmin = mpfr(10)
    bad = 0
    scale = mpfr(N) * N          # undisplaced triangles give exactly 1
    half = mpfr(1) / 2

    def tri(a, b, c):
        nonlocal total, jmin, bad
        (ia, ja), (ib, jb), (ic, jc) = a, b, c
        ux, uy, uz = X[ib][jb] - X[ia][ja], Y[ib][jb] - Y[ia][ja], Z[ib][jb] - Z[ia][ja]
        vx, vy, vz = X[ic][jc] - X[ia][ja], Y[ic][jc] - Y[ia][ja], Z[ic][jc] - Z[ia][ja]
        nx, ny, nz = uy * vz - uz * vy, uz * vx - ux * vz, ux * vy - uy * vx
        total += half * sqrt(nx * nx + ny * ny + nz * nz)
        # (a) parameter-plane orientation
        jac = ((S[ib][jb] - S[ia][ja]) * (T[ic][jc] - T[ia][ja])
               - (S[ic][jc] - S[ia][ja]) * (T[ib][jb] - T[ia][ja])) * scale
        if jac < jmin:
            jmin = jac
        # (b) outward normal.  In (s,t) = (latitude, longitude) order a positively oriented
        # parameter triangle maps to an inward chordal normal, so outward means dot < 0 here.
        dot = nx * (X[ia][ja] + X[ib][jb] + X[ic][jc]) + ny * (Y[ia][ja] + Y[ib][jb] + Y[ic][jc]) \
            + nz * (Z[ia][ja] + Z[ib][jb] + Z[ic][jc])
        if jac <= 0 or dot >= 0:
            bad += 1

    for i in range(N):
        for j in range(N):
            tri((i, j), (i + 1, j), (i + 1, j + 1))
            tri((i, j), (i + 1, j + 1), (i, j + 1))
    return (N, delta_s, scaled), (str(total), str(jmin), bad)


def main():
    setup()
    pi, phi0, phi1, lam0, lam1 = consts()
    exact = (lam1 - lam0) * (sin(phi1) - sin(phi0))
    ns = [n for n in (8, 16, 32, 64, 128, 256, 512, 1024) if n <= NMAX]
    fixed = ["0", "0.02", "-0.02", "0.04", "-0.04"]
    scaled = ["0.1", "-0.1", "0.2", "-0.2"]
    jobs = [(n, d, False) for d in fixed for n in ns if n <= min(NMAX, 512)] \
         + [(n, e, True) for e in scaled for n in ns]
    jobs.sort(key=lambda j: -j[0])
    with Pool() as pool:
        res = dict(pool.imap_unordered(area, jobs, chunksize=1))
    A = {k: mpfr(v[0]) for k, v in res.items()}
    jmin = min(mpfr(v[1]) for v in res.values())
    bad = sum(v[2] for v in res.values())
    ntri = sum(2 * k[0] * k[0] for k in res)

    def ops(d, sc, n):
        a = lambda m: A[(m, d, sc)]
        e = [a(n), (4 * a(2 * n) - a(n)) / 3,
             a(n) / 45 - 4 * a(2 * n) / 9 + 64 * a(4 * n) / 45,
             -a(n) / 2835 + 4 * a(2 * n) / 135 - 64 * a(4 * n) / 135 + 4096 * a(8 * n) / 2835]
        return [x - exact for x in e]

    order = lambda x, y: float(log2(abs(x / y)))
    f = lambda x, p=8: f"{float(x):.{p}f}"

    print(f"MPFR precision: {BITS} bits; NMAX = {NMAX}; runs: {len(res)}; triangles checked: {ntri}")
    print(f"orientation: {bad} triangles failed; minimum normalized parameter-plane area = {float(jmin):.6f}")

    print("\n=== Family F: fixed displacement ===")
    top = min(NMAX, 512)
    nb = min(32, top // 16)
    print(f"observed orders, base N={nb} vs {2*nb}: raw / 2-scale / 3-scale / 4-scale ; C2(delta)")
    C2 = {}
    for d in fixed:
        o = [order(x, y) for x, y in zip(ops(d, False, nb), ops(d, False, 2 * nb))]
        g = lambda m: (A[(m, d, False)] - exact) * m * m
        c2 = (64 * g(top) - 20 * g(top // 2) + g(top // 4)) / 45
        C2[d] = c2
        print(f"delta={d:>6}: " + "  ".join(f"{x:8.5f}" for x in o) + f"   C2 = {float(c2):.12f}")
    d1 = (C2["0.02"] - C2["-0.02"]) / mpfr("0.04")
    d2 = (C2["0.04"] - C2["-0.04"]) / mpfr("0.08")
    c2p = (4 * d1 - d2) / 3
    print(f"C2'(0): step .02 -> {f(d1,10)}, step .04 -> {f(d2,10)}, extrapolated {f(c2p,10)}")

    print("\n=== Family S: delta = eps/N ===")
    bn = [n for n in (16, 32, 64, 128) if 2 * n <= NMAX]
    for e in scaled:
        b3 = {n: -6 * ops(e, True, n)[1] * mpfr(n) ** 3 for n in bn}
        ext = 2 * b3[bn[-1]] - b3[bn[-2]]
        print(f"eps={e:>5}: " + "  ".join(f"N={n}: {f(v)}" for n, v in b3.items())
              + f"   extrap {f(ext)}   predicted {f(mpfr(e) * c2p)}")
    print("\nresidual ratios (prediction 1/15 = 0.066667 and 1/9 = 0.111111)")
    for e in ("0.1", "0.2"):
        for n in (16, 32, 64, 128):
            if 8 * n > NMAX:
                continue
            r = ops(e, True, n)
            print(f"eps={e} N={n:3d}: e2={float(r[1]): .6e} e3={float(r[2]): .6e} e4={float(r[3]): .6e}  "
                  f"e3/e2={float(r[2]/r[1]):.6f}  e4/e3={float(r[3]/r[2]):.6f}")
    print("\nobserved orders in family S: raw / 2- / 3- / 4-scale")
    for e in ("0.1", "0.2"):
        for n in (32, 64):
            if 16 * n > NMAX:
                continue
            print(f"eps={e} N={n}->{2*n}: " + "  ".join(
                f"{order(x, y):7.4f}" for x, y in zip(ops(e, True, n), ops(e, True, 2 * n))))
    print("\nodd/even split of the 2-scale residual in eps (N=64)")
    for e in ("0.1", "0.2"):
        if 128 > NMAX:
            continue
        ep, em = ops(e, True, 64)[1], ops("-" + e, True, 64)[1]
        print(f"eps={e}: odd {float((ep-em)/2): .6e}   even {float((ep+em)/2): .6e}   "
              f"predicted odd {float(-mpfr(e)*c2p/6/mpfr(64)**3): .6e}")
    print("\nmixed-exponent operator {2,3}: observed order (expect 4)")
    for e in ("0.1", "0.2"):
        m = lambda n: A[(n, e, True)] / 21 - 4 * A[(2 * n, e, True)] / 7 + 32 * A[(4 * n, e, True)] / 21 - exact
        print(f"eps={e}: " + "   ".join(f"N={n}->{2*n}: {order(m(n), m(2*n)):.4f}"
                                        for n in (32, 64, 128) if 8 * n <= NMAX))


if __name__ == "__main__":
    main()
