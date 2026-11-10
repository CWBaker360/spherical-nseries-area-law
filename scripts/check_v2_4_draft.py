# Sanity checks for statements added or carried into the v2.4 draft.
from fractions import Fraction as F
import mpmath as mp, sys
sys.path.insert(0, "/tmp/cwb/spherical-nseries-area-law/scripts")
import spherical_nseries_area_suite as S
mp.mp.dps = 50

# 1. Jacobian of the radial projection: area = int_sigma |det[A,B,C]| / |P|^3 du dv  (should equal beta)
for bdeg in (15, 30, 60, 90):
    b = mp.radians(bdeg)
    A, B, C = mp.matrix([0,0,1]), mp.matrix([1,0,0]), mp.matrix([mp.cos(b), mp.sin(b), 0])
    det = abs(mp.det(mp.matrix([list(A), list(B), list(C)])))
    f = lambda u, v: det / mp.norm((1-u-v)*A + u*B + v*C)**3
    val = mp.quad(lambda u: mp.quad(lambda v: f(u, v), [0, 1-u]), [0, 1])
    print(f"beta={bdeg:3d}: integral - beta = {mp.nstr(val - b, 5)}")

# 2. Small-N ladder from the archived chordal_triangle routine (octant, beta = 90 deg)
b = mp.pi/2
a = {N: S.right_triangle(b, N) for N in (4, 8, 16, 32, 64, 128)}
n2 = lambda x, y: y + (y - x)/3
n3 = lambda x, y, z: x/45 - mp.mpf(4)*y/9 + mp.mpf(64)*z/45
n4 = lambda x, y, z, w: -x/2835 + mp.mpf(4)*y/135 - mp.mpf(64)*z/135 + mp.mpf(4096)*w/2835
def orders(N):
    e = lambda v: abs(v - b)
    r = [(a[N], a[2*N]), (n2(a[N], a[2*N]), n2(a[2*N], a[4*N])),
         (n3(a[N], a[2*N], a[4*N]), n3(a[2*N], a[4*N], a[8*N])),
         (n4(a[N], a[2*N], a[4*N], a[8*N]), n4(a[2*N], a[4*N], a[8*N], a[16*N]))]
    return [mp.nstr(mp.log(e(x)/e(y), 2), 6) for x, y in r]
print("octant observed orders at N=4:", orders(4), " N=8:", orders(8))
print("octant raw errors:", [mp.nstr(abs(a[N]-b), 3) for N in (4, 8, 16, 32)])

# 3. Exact rational checks of weights, cubic residuals and moments
def weights(P):
    m = len(P); M = mp.matrix(m+1, m+1); rhs = mp.matrix(m+1, 1); rhs[0] = 1
    import sympy as sp
    A = sp.Matrix([[1]*(m+1)] + [[sp.Rational(1, 2**(j*p)) for j in range(m+1)] for p in P])
    return list(A.LUsolve(sp.Matrix([1] + [0]*m)))
import sympy as sp
mom = lambda w, p: sum(wj*sp.Rational(1, 2**(j*p)) for j, wj in enumerate(w))
for P in ([2], [2,4], [2,4,6]):
    w = weights(P); print("even", P, w, " cubic residual:", mom(w, 3))
for P, nxt in (([2,3], 4), ([2,3,4], 5), ([2,3,4,5], 6)):
    w = weights(P); print("mixed", P, w, f" M_{nxt} =", mom(w, nxt), " sum|w| =", float(sum(abs(x) for x in w)))
