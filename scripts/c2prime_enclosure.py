#!/usr/bin/env python3
"""Rigorous enclosure of C2'(0) for the v2.4 test field (computer-assisted step).

Setting (as in cubic_amplitude_test_mpfr.py):
  X(s,t) = unit-sphere point at latitude phi0 + dphi*s, longitude lam0 + dlam*t,
           phi0 = 30 deg, dphi = 30 deg, lam0 = 0, dlam = 30 deg;
  V(s,t) = sin(pi s) sin(pi t) ( cos(2t + 3/10), sin(3s + 7/10) );   F_delta = X o (id + delta V).

Cell-coefficient lemma (derived in the supplement; h = cell width, centre x):
  paired-cell chordal area  G = h^2 ( q0 + q2 h^2 + O(h^4) ),  with  N = F_s x F_t,
     q0 = |N|,
     q2 = (R . N) / (48 |N|)  +  (F_st . N)^2 |F_s + F_t|^2 / (8 |N|^3),
     R  = (F_s - F_t) x (d_s + d_t)^3 F  +  (d_s - d_t)^3 F x (F_s + F_t).
Midpoint Euler-Maclaurin on the unit square then gives
     C2(delta) = int q2 dx  -  (1/24) int Laplacian(q0) dx.

This script
  1. builds q2 and C2'(0)'s integrand symbolically (first-order perturbation F = X + delta*(DX.V));
  2. checks the q2 formula numerically against direct paired-cell areas, for the undeformed
     and for a deformed map (not rigorous; a guard against algebra slips);
  3. encloses  C2(0)  and  C2'(0)  by nested certified integration in Arb ball arithmetic
     (python-flint, acb.integral). The integrands are analytic near [0,1]^2: the only
     denominators are powers of cos(latitude), which is >= 1/2 on the cell.
Requires: sympy, mpmath, python-flint.
"""
import sympy as sp
import mpmath as mp
from flint import acb, arb, ctx

s, t = sp.symbols("s t", real=True)
pi = sp.pi
phi = pi / 6 + (pi / 6) * s
lam = (pi / 6) * t
X = sp.Matrix([sp.cos(phi) * sp.cos(lam), sp.cos(phi) * sp.sin(lam), sp.sin(phi)])
bump = sp.sin(pi * s) * sp.sin(pi * t)
V1 = bump * sp.cos(2 * t + sp.Rational(3, 10))
V2 = bump * sp.sin(3 * s + sp.Rational(7, 10))
n0 = (pi / 6) ** 2 * sp.cos(phi)                    # |X_s x X_t|, exact, positive on the cell

ds = lambda f: sp.diff(f, s)
dt = lambda f: sp.diff(f, t)
D1 = lambda f: ds(f) + dt(f)
D2 = lambda f: ds(f) - dt(f)
cube = lambda D, f: D(D(D(f)))


def pieces(F):
    Fs, Ft = ds(F), dt(F)
    N = Fs.cross(Ft)
    R = D2(F).cross(cube(D1, F)) + cube(D2, F).cross(D1(F))
    return N, R.dot(N), dt(Fs).dot(N), (Fs + Ft).dot(Fs + Ft)


# ---- zeroth order (delta = 0) --------------------------------------------------------------
N0, A0, B0, S0 = pieces(X)
q2_0 = A0 / (48 * n0) + B0 ** 2 * S0 / (8 * n0 ** 3)
E0 = q2_0 - (ds(ds(n0)) + dt(dt(n0))) / 24            # integrand of C2(0)

# ---- first order in delta: F = X + delta*F1, F1 = X_s V1 + X_t V2 ---------------------------
F1 = ds(X) * V1 + dt(X) * V2
N1 = ds(F1).cross(dt(X)) + ds(X).cross(dt(F1))
n1 = N0.dot(N1) / n0                                   # d|N|/d delta at 0
R0 = D2(X).cross(cube(D1, X)) + cube(D2, X).cross(D1(X))
R1 = (D2(F1).cross(cube(D1, X)) + D2(X).cross(cube(D1, F1))
      + cube(D2, F1).cross(D1(X)) + cube(D2, X).cross(D1(F1)))
A1 = R1.dot(N0) + R0.dot(N1)
B1 = dt(ds(F1)).dot(N0) + dt(ds(X)).dot(N1)
S1 = 2 * (ds(X) + dt(X)).dot(ds(F1) + dt(F1))
dq2 = ((A1 * n0 - A0 * n1) / (48 * n0 ** 2)
       + (2 * B0 * B1 * S0 + B0 ** 2 * S1) / (8 * n0 ** 3) - 3 * B0 ** 2 * S0 * n1 / (8 * n0 ** 4))
divJV = ds(n0 * V1) + dt(n0 * V2)                      # = d q0 / d delta at 0
E1 = dq2 - (ds(ds(divJV)) + dt(dt(divJV))) / 24        # integrand of C2'(0)


# ---- 2. numerical guards (mpmath, 40 digits) ------------------------------------------------
mp.mp.dps = 40
f_n1 = sp.lambdify((s, t), n1 - divJV, "mpmath")
print("guard: d|N|/d delta - div(J V) at (0.3,0.6):", mp.nstr(f_n1(mp.mpf("0.3"), mp.mpf("0.6")), 5))


def paired_cell_q2(Ffun, s0, t0):
    """q2 from direct paired-cell areas: fit g = G/h^2 in h^2 at four cell widths."""
    def g(h):
        k = h / 2
        P = lambda a, b: mp.matrix(Ffun(s0 + a * k, t0 + b * k))
        p00, p10, p11, p01 = P(-1, -1), P(1, -1), P(1, 1), P(-1, 1)
        cr = lambda u, v: mp.matrix([u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]])
        return (mp.norm(cr(p10 - p00, p11 - p00)) + mp.norm(cr(p11 - p00, p01 - p00))) / (2 * h * h)
    hs = [mp.mpf(1) / 2 ** j for j in (5, 6, 7, 8)]
    M = mp.matrix([[h ** (2 * j) for j in range(4)] for h in hs])
    return mp.lu_solve(M, mp.matrix([g(h) for h in hs]))[1]


Xfun = sp.lambdify((s, t), list(X), "mpmath")
q2fun = sp.lambdify((s, t), q2_0, "mpmath")
dlt = sp.Rational(3, 100)
Fd = X.subs({s: s + dlt * V1, t: t + dlt * V2}, simultaneous=True)
Nd, Ad, Bd, Sd = pieces(Fd)
nd = sp.sqrt(Nd.dot(Nd))
q2d = sp.lambdify((s, t), Ad / (48 * nd) + Bd ** 2 * Sd / (8 * nd ** 3), "mpmath")
Fdfun = sp.lambdify((s, t), list(Fd), "mpmath")
for (a, b) in ((mp.mpf("0.3"), mp.mpf("0.6")), (mp.mpf("0.8"), mp.mpf("0.15"))):
    d0 = q2fun(a, b) - paired_cell_q2(Xfun, a, b)
    d1 = q2d(a, b) - paired_cell_q2(Fdfun, a, b)
    print(f"guard: q2 formula - direct paired-cell value at ({a},{b}): undeformed {mp.nstr(d0, 3)}, "
          f"deformed (delta=0.03) {mp.nstr(d1, 3)}   [q2 ~ {mp.nstr(q2fun(a, b), 6)}]")


# ---- 3. certified integration in Arb ---------------------------------------------------------
ctx.prec = 128


def to_acb(expr):
    """Compile a sympy expression in (s,t) to a function of two acb balls (rational constants exact)."""
    rep, red = sp.cse(expr, optimizations="basic")
    def ev(e, env):
        if e.is_Symbol:
            return env[e]
        if e.is_Integer:
            return acb(int(e))
        if e.is_Rational:
            return acb(int(e.p)) / acb(int(e.q))
        if e is sp.pi:
            return acb.pi()
        if e.is_Add:
            r = ev(e.args[0], env)
            for a in e.args[1:]:
                r = r + ev(a, env)
            return r
        if e.is_Mul:
            r = ev(e.args[0], env)
            for a in e.args[1:]:
                r = r * ev(a, env)
            return r
        if e.is_Pow:
            b, x = e.args
            assert x.is_Integer, e
            r = ev(b, env) ** abs(int(x))
            return r if x > 0 else acb(1) / r
        if e.func is sp.sin:
            return ev(e.args[0], env).sin()
        if e.func is sp.cos:
            return ev(e.args[0], env).cos()
        raise TypeError(e)
    def f(sv, tv):
        env = {s: sv, t: tv}
        for sym, sub in rep:
            env[sym] = ev(sub, env)
        return ev(red[0], env)
    return f


def enclose(expr, tol):
    f = to_acb(expr)
    inner = lambda sv: acb.integral(lambda tv, _: f(sv, tv), 0, 1, rel_tol=arb(tol), abs_tol=arb(tol))
    return acb.integral(lambda sv, _: inner(sv), 0, 1, rel_tol=arb(tol), abs_tol=arb(tol)).real


c20 = enclose(E0, "1e-22")
print("\nC2(0)  enclosure:", c20.str(25), "   (grid-sum value -0.011894236621)")
c2p = enclose(E1, "1e-18")
print("C2'(0) enclosure:", c2p.str(25))
print("C2'(0) < 0 certified:", bool(c2p < 0), "   |C2'(0)| lower bound:", (-c2p).lower().str(12))
