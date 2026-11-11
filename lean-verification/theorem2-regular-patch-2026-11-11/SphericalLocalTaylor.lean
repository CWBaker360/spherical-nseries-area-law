import Mathlib
import SphericalFourthDerivative
import SphericalSliceFourthBound
import TaylorEvenPolynomial
import TaylorSecondDerivativeBridge
import SphericalQ2ClosedForm

/-!
# Spherical N-Series v2.4 — the local Taylor expansion of the normalized paired area

Assembly of the verified components into one statement.

For `F : ℝ² → ℝ³` of class `C⁵` and a nonempty compact set `K` of parameters on which
`F_s × F_t ≠ 0`, there are `H > 0` and `M ≥ 0` such that for every `y ∈ K` and `|h| ≤ H`

  `|sliceArea F y h - (‖F_s × F_t‖ + q2 F y * h²)| ≤ M * h⁴ / 24`,

where `sliceArea F y h = normArea crossE F (y, h)` is the paired chordal area of the cell of
width `h` centred at `y`, divided by `h²`, and `q2 F y` is the closed form of Lemma 2.

* `even_taylor_remainder_local` : the even fourth-order Taylor estimate for one function on
  one interval `[0, h]`, with hypotheses only on that interval;
* `q2`                          : the closed-form `h²` coefficient;
* `sliceArea_second_deriv`      : `iteratedDeriv 2 (sliceArea F y) 0 = 2 * q2 F y`;
* `spherical_local_taylor`      : the statement above;
* `spherical_local_pairedArea`  : the same for the un-normalized paired area,
  `|pairedArea - (‖F_s × F_t‖ h² + q2 h⁴)| ≤ M h⁶ / 24`.

## Scope: what is NOT proved here

* This is the expansion for a single cell, uniform over cell centres in `K`. There is no
  summation over cells and no statement about total area.
* `M` and `H` are shown to exist; no numerical value is given for either.
* The parameter domain must be a compact set on which `F_s × F_t ≠ 0`. A coordinate pole of
  a spherical parametrization is excluded by that hypothesis.
-/

namespace BakerSpherical.LocalTaylor

open BakerSpherical.SmoothExtension BakerSpherical.CrossContinuous BakerSpherical.UniformTaylor
  BakerSpherical.Q2

/-- Membership in `uIcc 0 h` bounds the absolute value. -/
theorem abs_le_of_mem_uIcc {u h : ℝ} (hu : u ∈ Set.uIcc 0 h) : |u| ≤ |h| := by
  rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-- The even fourth-order Taylor estimate with the sharp constant `1/24`, for one function
on one interval. All hypotheses concern only the interval between `0` and `h`. -/
theorem even_taylor_remainder_local (g : ℝ → ℝ) (M h : ℝ) (hh : h ≠ 0)
    (hsmooth : ∀ u ∈ Set.uIcc 0 h, ContDiffAt ℝ 4 g u)
    (hbound : ∀ ξ ∈ Set.uIcc 0 h, |iteratedDeriv 4 g ξ| ≤ M)
    (heven : ∀ u : ℝ, g (-u) = g u) :
    |g h - (g 0 + iteratedDeriv 2 g 0 * h ^ 2 / 2)| ≤ M * h ^ 4 / 24 := by
  have hz : (0 : ℝ) ∈ Set.uIcc 0 h := by simp
  have hpoly := even_taylor_polynomial g (Set.uIcc 0 h) h (uniqueDiffOn_uIcc hh.symm) hz
    (hsmooth 0 hz) heven
  have hon : ContDiffOn ℝ ((3 : ℕ) + 1 : ℕ) g (Set.uIcc 0 h) := fun u hu =>
    (hsmooth u hu).contDiffWithinAt
  obtain ⟨ξ, hξ, hEq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := g) (x := h)
    (x₀ := 0) (n := 3) hh.symm (by exact_mod_cast hon)
  have hξ' : ξ ∈ Set.uIcc 0 h := Set.Ioo_subset_Icc_self hξ
  have hfour : 0 ≤ h ^ 4 := by positivity
  have hb := hbound ξ hξ'
  rw [← hpoly, hEq]
  have hfact : ((3 + 1).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfact, sub_zero, abs_div, abs_mul, abs_of_nonneg hfour,
    abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hfour) (by norm_num)

/-- The closed-form `h²` coefficient of Lemma 2, at the cell centre `y`:
`q₂ = ⟪r, N⟫ / (48 ‖N‖) + ⟪F_st, N⟫² ‖F_s + F_t‖² / (8 ‖N‖³)` with `N = F_s × F_t` and
`r = (F_s - F_t) × D₊³F + D₋³F × (F_s + F_t)`. -/
noncomputable def q2 (F : ℝ × ℝ → E3) (y : ℝ × ℝ) : ℝ :=
  inner ℝ
      (crossE (fderiv ℝ F y (1, 0) - fderiv ℝ F y (0, 1)) (DP3 F y.1 y.2) +
        crossE (DM3 F y.1 y.2) (fderiv ℝ F y (1, 0) + fderiv ℝ F y (0, 1)))
      (crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))) /
    (48 * ‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖) +
  (inner ℝ (Fst F y.1 y.2) (crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)))) ^ 2 *
      ‖fderiv ℝ F y (1, 0) + fderiv ℝ F y (0, 1)‖ ^ 2 /
    (8 * ‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖ ^ 3)

/-- The second derivative of the area slice at `h = 0` is `2 q₂`. -/
theorem sliceArea_second_deriv (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 4 F) (y : ℝ × ℝ)
    (hreg : crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0) :
    iteratedDeriv 2 (sliceArea F y) 0 = 2 * q2 F y := by
  obtain ⟨s, t⟩ := y
  rw [second_iterated_derivative]
  exact cross_normArea_d2_closed F hF s t hreg

/-- **Local Taylor expansion of the normalized paired area.** -/
theorem spherical_local_taylor (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (hreg : ∀ y ∈ K, crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0) :
    ∃ H M : ℝ, 0 < H ∧ 0 ≤ M ∧ ∀ y ∈ K, ∀ h : ℝ, |h| ≤ H →
      |sliceArea F y h -
          (‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖ + q2 F y * h ^ 2)| ≤
        M * h ^ 4 / 24 := by
  obtain ⟨H1, hH1, hregular⟩ := spherical_uniform_contDiffAt F hF K hK hreg
  obtain ⟨H2, M, hH2, hM0, hMbound⟩ :=
    spherical_fourth_derivative_uniform_bound F hF K hK hne hreg
  refine ⟨min H1 H2, M, lt_min hH1 hH2, hM0, ?_⟩
  intro y hy h hh
  by_cases h0 : h = 0
  · subst h0
    rw [sliceArea_zero]
    simp
  · have hcd : ∀ u ∈ Set.uIcc 0 h, ContDiffAt ℝ 4 (normArea crossE F) (y, u) := fun u hu =>
      hregular y hy u (((abs_le_of_mem_uIcc hu).trans hh).trans (min_le_left _ _))
    have key := even_taylor_remainder_local (sliceArea F y) M h h0
      (fun u hu => slice_contDiffAt (normArea crossE F) y u (hcd u hu))
      (fun ξ hξ => slice_fourth_le_uniform (normArea crossE F) y ξ M (hcd ξ hξ)
        (hMbound y hy ξ (((abs_le_of_mem_uIcc hξ).trans hh).trans (min_le_right _ _))))
      (fun u => sliceArea_even F (hF.of_le (by norm_num)) y u)
    rw [sliceArea_second_deriv F (hF.of_le (by norm_num)) y (hreg y hy), sliceArea_zero] at key
    have e : ‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖ + 2 * q2 F y * h ^ 2 / 2 =
        ‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖ + q2 F y * h ^ 2 := by ring
    rw [e] at key
    exact key

/-- **Local expansion of the paired chordal area itself** (not divided by `h²`). -/
theorem spherical_local_pairedArea (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (hreg : ∀ y ∈ K, crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0) :
    ∃ H M : ℝ, 0 < H ∧ 0 ≤ M ∧ ∀ y ∈ K, ∀ h : ℝ, |h| ≤ H →
      |pairedArea crossE F y.1 y.2 h -
          (‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖ * h ^ 2 + q2 F y * h ^ 4)| ≤
        M * h ^ 6 / 24 := by
  obtain ⟨H, M, hH, hM, hloc⟩ := spherical_local_taylor F hF K hK hne hreg
  refine ⟨H, M, hH, hM, ?_⟩
  intro y hy h hh
  have key := hloc y hy h hh
  have hpa : pairedArea crossE F y.1 y.2 h = h ^ 2 * sliceArea F y h :=
    pairedArea_eq crossE F (hF.of_le (by norm_num)) y.1 y.2 h
  have e : pairedArea crossE F y.1 y.2 h -
      (‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖ * h ^ 2 + q2 F y * h ^ 4) =
      h ^ 2 * (sliceArea F y h -
        (‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖ + q2 F y * h ^ 2)) := by
    rw [hpa]; ring
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg h)]
  calc h ^ 2 * |sliceArea F y h -
          (‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖ + q2 F y * h ^ 2)|
      ≤ h ^ 2 * (M * h ^ 4 / 24) := mul_le_mul_of_nonneg_left key (sq_nonneg h)
    _ = M * h ^ 6 / 24 := by ring

end BakerSpherical.LocalTaylor

#print axioms BakerSpherical.LocalTaylor.even_taylor_remainder_local
#print axioms BakerSpherical.LocalTaylor.sliceArea_second_deriv
#print axioms BakerSpherical.LocalTaylor.spherical_local_taylor
#print axioms BakerSpherical.LocalTaylor.spherical_local_pairedArea
