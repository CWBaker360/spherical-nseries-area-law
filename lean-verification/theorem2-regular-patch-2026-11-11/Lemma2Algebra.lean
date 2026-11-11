import Mathlib

/-!
# Baker spherical N-series, v2.4 — Lemma 2 (algebraic core)

Review snapshot: 67a4590dfb1fee6d23dc011be1b9ece1503c2824

This file attempts the *polynomial* part of Lemma 2, not the analytic
Taylor expansion of the Euclidean norm or its remainder bound.

The seven vector arguments represent, respectively,
F_s, F_t, F_st, F_sss, F_sst, F_stt, F_ttt.

Important: this version has not yet been compiled by a Lean kernel.
Run `lake env lean Lemma2Algebra.lean` in a mathlib project before claiming
formal verification.
-/

namespace BakerSpherical.Lemma2

noncomputable section

structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

private def add (u v : V3) : V3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
private def sub (u v : V3) : V3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
private def smul (a : ℝ) (u : V3) : V3 := ⟨a*u.x, a*u.y, a*u.z⟩
private def dot (u v : V3) : ℝ := u.x*v.x + u.y*v.y + u.z*v.z
private def cross (u v : V3) : V3 :=
  ⟨u.y*v.z - u.z*v.y, u.z*v.x - u.x*v.z, u.x*v.y - u.y*v.x⟩

-- Constant terms of the two orientation-compatible cross products.
theorem leading_first (fs ft : V3) :
    cross fs (add fs ft) = cross fs ft := by
  cases fs with
  | mk sx sy sz =>
    cases ft with
    | mk tx ty tz =>
      change V3.mk _ _ _ = V3.mk _ _ _
      congr 1 <;> simp [cross, add] <;> ring

theorem leading_second (fs ft : V3) :
    cross (add fs ft) ft = cross fs ft := by
  cases fs with
  | mk sx sy sz =>
    cases ft with
    | mk tx ty tz =>
      change V3.mk _ _ _ = V3.mk _ _ _
      congr 1 <;> simp [cross, add] <;> ring

-- Third directional derivatives D_+^3 F and D_-^3 F.
private def dplus (sss sst stt ttt : V3) : V3 :=
  add (add sss (smul 3 sst)) (add (smul 3 stt) ttt)
private def dminus (sss sst stt ttt : V3) : V3 :=
  add (sub sss (smul 3 sst)) (sub (smul 3 stt) ttt)

private def n (fs ft : V3) : V3 := cross fs ft
private def a1 (fs ft fst : V3) : V3 :=
  smul (-(1/2 : ℝ)) (cross fst (add fs ft))
private def a2 (fs ft fst : V3) : V3 :=
  smul ((1/2 : ℝ)) (cross fst (add fs ft))

-- Coefficients of h^2 in w1 and w2, where w_i is the
-- triangle cross product divided by h^2.
private def b1 (fs ft sss sst stt ttt : V3) : V3 :=
  add
    (cross (add (smul (1/24 : ℝ) sss) (smul (1/8 : ℝ) stt)) (add fs ft))
    (smul (1/24 : ℝ) (cross fs (dplus sss sst stt ttt)))
private def b2 (fs ft sss sst stt ttt : V3) : V3 :=
  add
    (smul (1/24 : ℝ) (cross (dplus sss sst stt ttt) ft))
    (cross (add fs ft) (add (smul (1/24 : ℝ) ttt) (smul (1/8 : ℝ) sst)))

private def r (fs ft sss sst stt ttt : V3) : V3 :=
  add
    (cross (sub fs ft) (dplus sss sst stt ttt))
    (cross (dminus sss sst stt ttt) (add fs ft))

-- Paired triangle h^3 terms cancel *exactly*.
theorem odd_coefficient_cancels (fs ft fst : V3) :
    dot (n fs ft) (a1 fs ft fst) +
    dot (n fs ft) (a2 fs ft fst) = 0 := by
  simp [dot, n, a1, a2, smul, cross, add]
  ring

/-!
The identity below is obtained by multiplying the q₂ formula by ||N||³,
so the result is polynomial (no square roots or division by ||N||).

LHS is the sum of h^4 coefficients of the triangle norms after
standard Euclidean norm differentiation. RHS is the claimed closed form.
-/
set_option maxHeartbeats 0 in
theorem q2_polynomial_identity
    (fs ft fst sss sst stt ttt : V3) :
    let normal := n fs ft
    let normSq := dot normal normal
    let u := a1 fs ft fst
    let v := a2 fs ft fst
    let p := b1 fs ft sss sst stt ttt
    let q := b2 fs ft sss sst stt ttt
    normSq * ((dot u u + 2 * dot normal p +
               dot v v + 2 * dot normal q) / 4) -
      ((dot normal u)^2 + (dot normal v)^2) / 4 =
    dot (r fs ft sss sst stt ttt) normal * normSq / 48 +
      (dot fst normal)^2 * dot (add fs ft) (add fs ft) / 8 := by
  dsimp
  rcases fs with ⟨sx, sy, sz⟩
  rcases ft with ⟨tx, ty, tz⟩
  rcases fst with ⟨ex, ey, ez⟩
  rcases sss with ⟨ax, ay, az⟩
  rcases sst with ⟨bx, bY, bz⟩
  rcases stt with ⟨cx, cy, cz⟩
  rcases ttt with ⟨dx, dy, dz⟩
  simp only [dot, n, a1, a2, b1, b2, r, dplus, dminus,
    add, sub, smul, cross]
  ring

#print axioms BakerSpherical.Lemma2.leading_first
#print axioms BakerSpherical.Lemma2.leading_second
#print axioms BakerSpherical.Lemma2.odd_coefficient_cancels
#print axioms BakerSpherical.Lemma2.q2_polynomial_identity

end

end BakerSpherical.Lemma2
