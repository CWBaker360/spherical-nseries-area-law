import Mathlib
import MidpointQuadrature2D
import SphericalMixedPartials
import SphericalCellSum

/-!
# Spherical N-Series v2.4 — Theorem 2: the global area expansion on a regular patch

For `F : ℝ² → ℝ³` of class `C⁵` with `F_s × F_t ≠ 0` on the closed unit square, and the
`N × N` midpoint grid with lower-left to upper-right diagonals:

* `jac_contDiffAt`     : the area density `J = ‖F_s × F_t‖` is `C⁴` at every point of the square;
* `q2_contDiffAt`      : the Lemma 2 coefficient `q₂` is `C²` at every point of the square;
* `spherical_area_law` : there are `H > 0` and `C ≥ 0` such that for all `N ≥ 1`, `1/N ≤ H`,

    `|A_N - (A + C₂ / N²)| ≤ C / N⁴`,

  where `A = areaIntegral F = ∬ J` is the surface area of the patch and
  `C₂ = areaC2 F = -(1/24) (∬ J_ss + ∬ J_tt) + ∬ q₂`;
* `richardson_fourth_order` : the Richardson combination `R_N = (4 A_{2N} - A_N) / 3`
  satisfies `|R_N - A| ≤ (5/12) C / N⁴`.

No quadrature estimate is assumed: both hypotheses of `area_law_of_midpoint_rules` are
discharged by `MidpointQuadrature2D.lean`.

## Scope: what is NOT proved here

* The patch is the closed unit square with `F_s × F_t ≠ 0` on all of it. A parametrization
  with a coordinate pole in the square is excluded; the whole sphere is not covered.
* `H` and `C` exist; no numerical values are given. The Arb-certified values of `C₂(0)` and
  `C₂'(0)` in the paper are not derived here.
* `A` and `C₂` are iterated integrals `∫ s in 0..1, ∫ t in 0..1, …`. Their identification
  with a surface measure, or with a boundary form of the correction, is not proved.
* Only the first expansion term is established, so only the fourth-order Richardson result.
  The sixth- and eighth-order results need higher-order expansions.
-/

namespace BakerSpherical.AreaLaw

open BakerSpherical.SmoothExtension BakerSpherical.CrossContinuous BakerSpherical.LocalTaylor
  BakerSpherical.Q2 BakerSpherical.GlobalSum BakerSpherical.Midpoint

/-! ### Smoothness of the density and of `q₂` -/

theorem dirD_contDiff {G : ℝ × ℝ → E3} {n m : ℕ} (hG : ContDiff ℝ n G) (hm : m + 1 ≤ n)
    (v : ℝ × ℝ) : ContDiff ℝ m (dirD v G) :=
  (hG.fderiv_right (m := m) (by exact_mod_cast hm)).clm_apply contDiff_const

/-- The normal field `y ↦ F_s(y) × F_t(y)`. -/
noncomputable def normalField (F : ℝ × ℝ → E3) (y : ℝ × ℝ) : E3 :=
  crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))

theorem normalField_contDiff (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F) :
    ContDiff ℝ 4 (normalField F) :=
  (crossE.contDiff.comp (dirD_contDiff hF (by norm_num) (1, 0))).clm_apply
    (dirD_contDiff hF (by norm_num) (0, 1))

/-- The area density is `C⁴` wherever the normal does not vanish. -/
theorem jac_contDiffAt (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F) (y : ℝ × ℝ)
    (hreg : crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0) :
    ContDiffAt ℝ 4 (jac F) y :=
  (normalField_contDiff F hF).contDiffAt.norm ℝ hreg

/-- `q₂` written with iterated partial derivatives only. -/
theorem q2_eq (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F) :
    q2 F = fun y =>
      inner ℝ
          (crossE (dirD (1, 0) F y - dirD (0, 1) F y)
              (dirD (1, 0) (dirD (1, 0) (dirD (1, 0) F)) y +
                (3 : ℝ) • dirD (1, 0) (dirD (1, 0) (dirD (0, 1) F)) y +
                (3 : ℝ) • dirD (1, 0) (dirD (0, 1) (dirD (0, 1) F)) y +
                dirD (0, 1) (dirD (0, 1) (dirD (0, 1) F)) y) +
            crossE
              (dirD (1, 0) (dirD (1, 0) (dirD (1, 0) F)) y -
                (3 : ℝ) • dirD (1, 0) (dirD (1, 0) (dirD (0, 1) F)) y +
                (3 : ℝ) • dirD (1, 0) (dirD (0, 1) (dirD (0, 1) F)) y -
                dirD (0, 1) (dirD (0, 1) (dirD (0, 1) F)) y)
              (dirD (1, 0) F y + dirD (0, 1) F y))
          (normalField F y) / (48 * ‖normalField F y‖) +
        (inner ℝ (dirD (1, 0) (dirD (0, 1) F) y) (normalField F y)) ^ 2 *
            ‖dirD (1, 0) F y + dirD (0, 1) F y‖ ^ 2 / (8 * ‖normalField F y‖ ^ 3) := by
  funext y
  obtain ⟨s, t⟩ := y
  have h3 : ContDiff ℝ 3 F := hF.of_le (by norm_num)
  have h2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  simp only [q2, DP3_eq F s t h3, DM3_eq F s t h3, Fst_eq F s t h2]
  rfl

/-- `q₂` is `C²` wherever the normal does not vanish. -/
theorem q2_contDiffAt (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F) (y : ℝ × ℝ)
    (hreg : crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0) :
    ContDiffAt ℝ 2 (q2 F) y := by
  have hN : ContDiffAt ℝ 2 (normalField F) y :=
    ((normalField_contDiff F hF).of_le (by norm_num)).contDiffAt
  have hNn : ContDiffAt ℝ 2 (fun y => ‖normalField F y‖) y := hN.norm ℝ hreg
  have hne : ‖normalField F y‖ ≠ 0 := norm_ne_zero_iff.mpr hreg
  have d1 : ∀ v, ContDiffAt ℝ 2 (dirD v F) y := fun v =>
    (dirD_contDiff (n := 5) (m := 2) hF (by norm_num) v).contDiffAt
  have d2 : ∀ v w, ContDiffAt ℝ 2 (dirD v (dirD w F)) y := fun v w =>
    (dirD_contDiff (n := 4) (m := 2) (dirD_contDiff (n := 5) (m := 4) hF (by norm_num) w)
      (by norm_num) v).contDiffAt
  have d3 : ∀ u v w, ContDiffAt ℝ 2 (dirD u (dirD v (dirD w F))) y := fun u v w =>
    (dirD_contDiff (n := 3) (m := 2) (dirD_contDiff (n := 4) (m := 3)
      (dirD_contDiff (n := 5) (m := 4) hF (by norm_num) w) (by norm_num) v)
      (by norm_num) u).contDiffAt
  have hcross : ∀ {a b : ℝ × ℝ → E3}, ContDiffAt ℝ 2 a y → ContDiffAt ℝ 2 b y →
      ContDiffAt ℝ 2 (fun y => crossE (a y) (b y)) y := fun ha hb =>
    (crossE.contDiff.contDiffAt.comp y ha).clm_apply hb
  rw [q2_eq F hF]
  have hP := (((d3 (1, 0) (1, 0) (1, 0)).add ((d3 (1, 0) (1, 0) (0, 1)).const_smul (3 : ℝ))).add
    ((d3 (1, 0) (0, 1) (0, 1)).const_smul (3 : ℝ))).add (d3 (0, 1) (0, 1) (0, 1))
  have hM := (((d3 (1, 0) (1, 0) (1, 0)).sub ((d3 (1, 0) (1, 0) (0, 1)).const_smul (3 : ℝ))).add
    ((d3 (1, 0) (0, 1) (0, 1)).const_smul (3 : ℝ))).sub (d3 (0, 1) (0, 1) (0, 1))
  have hr := (hcross ((d1 (1, 0)).sub (d1 (0, 1))) hP).add
    (hcross hM ((d1 (1, 0)).add (d1 (0, 1))))
  have t1 := (hr.inner ℝ hN).div ((contDiffAt_const (c := (48 : ℝ))).mul hNn)
    (mul_ne_zero (by norm_num : (48 : ℝ) ≠ 0) hne)
  have t2 := ((((d2 (1, 0) (0, 1)).inner ℝ hN).pow 2).mul
    (((d1 (1, 0)).add (d1 (0, 1))).norm_sq ℝ)).div
    ((contDiffAt_const (c := (8 : ℝ))).mul (hNn.pow 3))
    (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero 3 hne))
  exact t1.add t2

/-! ### The area law -/

/-- The surface area of the patch, as an iterated integral of the density. -/
noncomputable def areaIntegral (F : ℝ × ℝ → E3) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, jac F (s, t)

/-- The coefficient of `N⁻²` in the area expansion. -/
noncomputable def areaC2 (F : ℝ × ℝ → E3) : ℝ :=
  -(1 / 24) * ((∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, ps 2 (jac F) (s, t)) +
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, pt 2 (jac F) (s, t)) +
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, q2 F (s, t)

/-- **Theorem 2 on a regular patch.** `A_N = A + C₂ N⁻² + O(N⁻⁴)`. -/
theorem spherical_area_law (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F)
    (hreg : ∀ y ∈ unitSquare, crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0) :
    ∃ H C : ℝ, 0 < H ∧ 0 ≤ C ∧ ∀ N : ℕ, 0 < N → (1 : ℝ) / N ≤ H →
      |chordalArea F N - (areaIntegral F + areaC2 F * (1 / (N : ℝ)) ^ 2)| ≤
        C * (1 / (N : ℝ)) ^ 4 := by
  obtain ⟨K1, hK1, hJ⟩ := midpoint2D_fourth (jac F) (fun y hy =>
    jac_contDiffAt F hF y (hreg y hy))
  obtain ⟨K2, hK2, hq⟩ := midpoint2D_second (q2 F) (fun y hy =>
    q2_contDiffAt F hF y (hreg y hy))
  obtain ⟨H, M, hH, hM, hlaw⟩ := area_law_of_midpoint_rules F hF hreg (areaIntegral F)
    (-(1 / 24) * ((∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, ps 2 (jac F) (s, t)) +
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, pt 2 (jac F) (s, t)))
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, q2 F (s, t)) K1 K2
    (fun N hN => by
      have := hJ N hN
      have e : ∀ A D h : ℝ, A + -(1 / 24) * D * h ^ 2 = A - h ^ 2 / 24 * D := fun A D h => by
        ring
      rw [e]
      exact this)
    hq
  exact ⟨H, M / 24 + K1 + K2, hH, by positivity, hlaw⟩

/-- **Fourth-order Richardson extrapolation.** `(4 A_{2N} - A_N) / 3 = A + O(N⁻⁴)`. -/
theorem richardson_fourth_order (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F)
    (hreg : ∀ y ∈ unitSquare, crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0) :
    ∃ H C : ℝ, 0 < H ∧ 0 ≤ C ∧ ∀ N : ℕ, 0 < N → (1 : ℝ) / N ≤ H →
      |(4 * chordalArea F (2 * N) - chordalArea F N) / 3 - areaIntegral F| ≤
        C * (1 / (N : ℝ)) ^ 4 := by
  obtain ⟨H, C, hH, hC, hlaw⟩ := spherical_area_law F hF hreg
  refine ⟨H, 5 / 12 * C, hH, by positivity, ?_⟩
  intro N hN hNH
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := hlaw N hN hNH
  have h2N : (1 : ℝ) / ((2 * N : ℕ) : ℝ) ≤ H := by
    refine le_trans ?_ hNH
    push_cast
    apply one_div_le_one_div_of_le hNpos
    linarith
  have h2 := hlaw (2 * N) (by omega) h2N
  have e2 : (1 : ℝ) / ((2 * N : ℕ) : ℝ) = (1 / (N : ℝ)) / 2 := by push_cast; field_simp
  rw [e2] at h2
  set h : ℝ := 1 / (N : ℝ) with hdef
  set A := areaIntegral F
  set c := areaC2 F
  set a1 := chordalArea F N
  set a2 := chordalArea F (2 * N)
  have e : (4 * a2 - a1) / 3 - A =
      (4 * (a2 - (A + c * (h / 2) ^ 2)) - (a1 - (A + c * h ^ 2))) / 3 := by ring
  rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have t := abs_sub (4 * (a2 - (A + c * (h / 2) ^ 2))) (a1 - (A + c * h ^ 2))
  have t4 : |4 * (a2 - (A + c * (h / 2) ^ 2))| ≤ 4 * (C * (h / 2) ^ 4) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have e3 : 5 / 12 * C * h ^ 4 = (4 * (C * (h / 2) ^ 4) + C * h ^ 4) / 3 := by ring
  rw [e3]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

end BakerSpherical.AreaLaw

#print axioms BakerSpherical.AreaLaw.jac_contDiffAt
#print axioms BakerSpherical.AreaLaw.q2_eq
#print axioms BakerSpherical.AreaLaw.q2_contDiffAt
#print axioms BakerSpherical.AreaLaw.spherical_area_law
#print axioms BakerSpherical.AreaLaw.richardson_fourth_order
