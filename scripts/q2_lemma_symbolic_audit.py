#!/usr/bin/env python3
"""Symbolic audit of the cell-coefficient lemma (exact polynomial identities, no numerics).

Claim. Let F be a smooth map into R^3 with N = F_s x F_t != 0 at the cell centre x. With corners
p_ab = F(x + ((2a-1)h/2, (2b-1)h/2)), the paired-cell chordal area
    G = (1/2)|(p10-p00) x (p11-p00)| + (1/2)|(p11-p00) x (p01-p00)|
satisfies  G = h^2 ( q0 + q2 h^2 + O(h^4) )  with
    q0 = |N|,
    q2 = (R.N)/(48|N|) + (F_st.N)^2 |F_s+F_t|^2 / (8|N|^3),
    R  = (F_s-F_t) x (d_s+d_t)^3 F + (d_s-d_t)^3 F x (F_s+F_t).

Method. F is replaced by its generic Taylor polynomial of degree 4 at x, whose coefficients are 14
independent symbolic vectors (42 scalar symbols). Then
    w1 := (p10-p00) x (p11-p00) / h^2,   w2 := (p11-p00) x (p01-p00) / h^2
are exact polynomials in h:  w = N + h a + h^2 b + O(h^3).  For any such w,
    |w| = |N| + h (N.a)/|N| + h^2 [ (a.a + 2 N.b)/(2|N|) - (N.a)^2/(2|N|^3) ] + O(h^3).
The audit verifies, as identities between polynomials with integer coefficients in the 42 symbols:
  (I0)  w1(0) = w2(0) = N
  (I1)  N.a1 + N.a2 = 0                                   (no h^3 term in G: evenness)
  (I2)  |N|^2 * sum_i [(a_i.a_i + 2 N.b_i)] / 4 - sum_i (N.a_i)^2 / 4
          =  (R.N) |N|^2 / 48 + (F_st.N)^2 |F_s+F_t|^2 / 8      (i.e. q2 |N|^3 on both sides)
  (I3)  the degree-4 Taylor coefficients of F do not enter w up to h^2.
Requires sympy.
"""
import itertools, time
import sympy as sp

t0 = time.time()
h = sp.Symbol("h")
idx = [(i, j) for d in range(1, 5) for i in range(d, -1, -1) for j in [d - i]]
name = lambda i, j: "F" + "s" * i + "t" * j
C = {(i, j): sp.Matrix(sp.symbols(f"{name(i, j)}_x {name(i, j)}_y {name(i, j)}_z")) for (i, j) in idx}
allsyms = [c for v in C.values() for c in v]


def Ft(xi, eta):
    """Taylor polynomial of F - F(x) at displacement (xi, eta)."""
    out = sp.zeros(3, 1)
    for (i, j), v in C.items():
        out += v * (xi ** i * eta ** j / (sp.factorial(i) * sp.factorial(j)))
    return out


k = h / 2
p00, p10, p11, p01 = Ft(-k, -k), Ft(k, -k), Ft(k, k), Ft(-k, k)


def series_vec(w, order):
    """Coefficients of h^0..h^order of the vector polynomial w/h^2."""
    cols = []
    for comp in w:
        P = sp.Poly(sp.expand(comp), h)
        cols.append([P.coeff_monomial(h ** (m + 2)) for m in range(order + 1)])
        assert all(P.coeff_monomial(h ** m) == 0 for m in (0, 1))
    return [sp.Matrix([cols[c][m] for c in range(3)]) for m in range(order + 1)]


w1 = series_vec((p10 - p00).cross(p11 - p00), 2)
w2 = series_vec((p11 - p00).cross(p01 - p00), 2)
Fs, Ftt_, Fst = C[(1, 0)], C[(0, 1)], C[(1, 1)]
N = Fs.cross(Ftt_)
zero = lambda e: sp.Poly(sp.expand(e), *allsyms).is_zero

print("(I0) w1(0) = N:", all(zero(e) for e in (w1[0] - N)), "  w2(0) = N:", all(zero(e) for e in (w2[0] - N)))
print("(I1) N.a1 + N.a2 = 0:", zero(N.dot(w1[1]) + N.dot(w2[1])))

# third directional derivatives from the generic coefficients
D1c = C[(3, 0)] + 3 * C[(2, 1)] + 3 * C[(1, 2)] + C[(0, 3)]      # (d_s + d_t)^3 F
D2c = C[(3, 0)] - 3 * C[(2, 1)] + 3 * C[(1, 2)] - C[(0, 3)]      # (d_s - d_t)^3 F
R = (Fs - Ftt_).cross(D1c) + D2c.cross(Fs + Ftt_)
n2 = N.dot(N)
lhs = n2 * sum(w[1].dot(w[1]) + 2 * N.dot(w[2]) for w in (w1, w2)) / 4 \
    - sum(N.dot(w[1]) ** 2 for w in (w1, w2)) / 4
rhs = R.dot(N) * n2 / 48 + Fst.dot(N) ** 2 * (Fs + Ftt_).dot(Fs + Ftt_) / 8
diff = sp.Poly(sp.expand(lhs - rhs), *allsyms)
print("(I2) q2 |N|^3 identity holds:", diff.is_zero,
      f"  [lhs has {len(sp.Poly(sp.expand(lhs), *allsyms).terms())} monomials]")
deg4 = [c for (i, j), v in C.items() if i + j == 4 for c in v]
used = set().union(*[e.free_symbols for w in (w1, w2) for vec in w for e in vec])
print("(I3) degree-4 Taylor coefficients absent through h^2:", not (used & set(deg4)))
print(f"elapsed {time.time() - t0:.1f} s")
