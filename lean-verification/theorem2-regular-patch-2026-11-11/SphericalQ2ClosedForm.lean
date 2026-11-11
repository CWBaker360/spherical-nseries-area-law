import Mathlib
import Batteries.Tactic.OpenPrivate
import Lemma2Algebra
import SphericalQ2Coefficient

/-!
# Spherical N-Series v2.4 — closed form of `q₂` (Lemma 2)

Connects the analytic second derivative of `SphericalQ2Coefficient.lean` to the verified
polynomial identity `BakerSpherical.Lemma2.q2_polynomial_identity`.

* `toV3`                    : coordinates of a Euclidean vector as a `Lemma2.V3`;
* `cross_q2_polynomial`     : the identity `‖N‖³ q₂ = ⟪r, N⟫ ‖N‖² / 48 + ⟪F_st, N⟫² ‖F_s + F_t‖² / 8`
                              for `crossE`, obtained from `q2_polynomial_identity`;
* `cross_q2_closed_form`    : `q₂ = ⟪r, N⟫ / (48 ‖N‖) + ⟪F_st, N⟫² ‖F_s + F_t‖² / (8 ‖N‖³)`;
* `cross_normArea_d2_closed`: for `F` of class `C⁴` at a regular point,
    `d²/dh² normArea crossE F ((s,t), h) |_{h=0} = 2 * (that closed form)`.

Here `N = F_s × F_t` and `r = (F_s - F_t) × D₊³F + D₋³F × (F_s + F_t)`.

Scope: as in `SphericalQ2Coefficient.lean`. This is the value of the second derivative at
`h = 0`; it is not a Taylor expansion with remainder. `Fst`, `DP3`, `DM3` are defined through
the diagonal curves and are not yet identified with mixed partial derivatives.
-/

namespace BakerSpherical.Q2

open scoped Matrix
open BakerSpherical.SmoothExtension BakerSpherical.CrossContinuous BakerSpherical.Lemma2

open private add sub smul dot cross dplus dminus n a1 a2 b1 b2 r from Lemma2Algebra

/-- Coordinates of a Euclidean vector, as the `V3` structure of `Lemma2Algebra.lean`. -/
def toV3 (u : E3) : V3 := ⟨u 0, u 1, u 2⟩

theorem crossE_c0 (u v : E3) : crossE u v 0 = u 1 * v 2 - u 2 * v 1 := by
  have h : crossE u v = WithLp.toLp 2 (u.ofLp ⨯₃ v.ofLp) := rfl
  rw [h, cross_apply]; rfl

theorem crossE_c1 (u v : E3) : crossE u v 1 = u 2 * v 0 - u 0 * v 2 := by
  have h : crossE u v = WithLp.toLp 2 (u.ofLp ⨯₃ v.ofLp) := rfl
  rw [h, cross_apply]; rfl

theorem crossE_c2 (u v : E3) : crossE u v 2 = u 0 * v 1 - u 1 * v 0 := by
  have h : crossE u v = WithLp.toLp 2 (u.ofLp ⨯₃ v.ofLp) := rfl
  rw [h, cross_apply]; rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- The Lemma 2 identity for the Euclidean cross product, from `q2_polynomial_identity`. -/
theorem cross_q2_polynomial (fs ft fst dp dm : E3) :
    ‖crossE fs ft‖ ^ 2 *
        ((‖uVec crossE fs ft fst‖ ^ 2 + 2 * inner ℝ (crossE fs ft) (pVec crossE fs ft dp dm) +
          ‖vVec crossE fs ft fst‖ ^ 2 +
            2 * inner ℝ (crossE fs ft) (qVec crossE fs ft dp dm)) / 4) -
        ((inner ℝ (crossE fs ft) (uVec crossE fs ft fst)) ^ 2 +
          (inner ℝ (crossE fs ft) (vVec crossE fs ft fst)) ^ 2) / 4 =
      inner ℝ (crossE (fs - ft) dp + crossE dm (fs + ft)) (crossE fs ft) *
          ‖crossE fs ft‖ ^ 2 / 48 +
        (inner ℝ fst (crossE fs ft)) ^ 2 * ‖fs + ft‖ ^ 2 / 8 := by
  have key := q2_polynomial_identity (toV3 fs) (toV3 ft) (toV3 fst)
    (toV3 ((1 / 2 : ℝ) • (dp + dm))) ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ (toV3 ((1 / 2 : ℝ) • (dp - dm)))
  simp only [dot, n, a1, a2, b1, b2, r, dplus, dminus, add, sub, smul, cross, toV3,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at key
  simp only [uVec, vVec, pVec, qVec, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, crossE_c0, crossE_c1,
    crossE_c2]
  linear_combination key

/-- **Closed form of `q₂`** (Lemma 2), for the Euclidean cross product. -/
theorem cross_q2_closed_form (fs ft fst dp dm : E3) (hN : crossE fs ft ≠ 0) :
    q2Coeff (crossE fs ft) (uVec crossE fs ft fst) (vVec crossE fs ft fst)
        (pVec crossE fs ft dp dm) (qVec crossE fs ft dp dm) =
      inner ℝ (crossE (fs - ft) dp + crossE dm (fs + ft)) (crossE fs ft) /
          (48 * ‖crossE fs ft‖) +
        (inner ℝ fst (crossE fs ft)) ^ 2 * ‖fs + ft‖ ^ 2 / (8 * ‖crossE fs ft‖ ^ 3) := by
  have hn : ‖crossE fs ft‖ ≠ 0 := norm_ne_zero_iff.mpr hN
  have h1 := q2Coeff_mul_norm_cube hN (uVec crossE fs ft fst) (vVec crossE fs ft fst)
    (pVec crossE fs ft dp dm) (qVec crossE fs ft dp dm)
  rw [cross_q2_polynomial] at h1
  have h3 : ‖crossE fs ft‖ ^ 3 ≠ 0 := pow_ne_zero 3 hn
  rw [← mul_right_inj' h3, h1]
  field_simp

/-- **Lemma 2, analytic form.** For `F : ℝ² → ℝ³` of class `C⁴`, at a point where
`F_s × F_t ≠ 0`, the second `h`-derivative at `h = 0` of the normalized paired chordal area
is `2 q₂`, with `q₂` in closed form. -/
theorem cross_normArea_d2_closed (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 4 F) (s t : ℝ)
    (hreg : crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) ≠ 0) :
    deriv (deriv (fun h => normArea crossE F ((s, t), h))) 0 =
      2 * (inner ℝ
            (crossE (fderiv ℝ F (s, t) (1, 0) - fderiv ℝ F (s, t) (0, 1)) (DP3 F s t) +
              crossE (DM3 F s t) (fderiv ℝ F (s, t) (1, 0) + fderiv ℝ F (s, t) (0, 1)))
            (crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1))) /
          (48 * ‖crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1))‖) +
        (inner ℝ (Fst F s t)
            (crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)))) ^ 2 *
          ‖fderiv ℝ F (s, t) (1, 0) + fderiv ℝ F (s, t) (0, 1)‖ ^ 2 /
            (8 * ‖crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1))‖ ^ 3)) := by
  rw [cross_normArea_d2 F hF s t hreg, cross_q2_closed_form _ _ _ _ _ hreg]

end BakerSpherical.Q2

#print axioms BakerSpherical.Q2.cross_q2_polynomial
#print axioms BakerSpherical.Q2.cross_q2_closed_form
#print axioms BakerSpherical.Q2.cross_normArea_d2_closed
