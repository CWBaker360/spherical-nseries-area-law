import Mathlib
import SphericalLocalTaylor

/-!
# Midpoint quadrature in one variable, with the `h²` correction term

For `φ : ℝ → ℝ` and `N ≥ 1`, `h = 1/N`, midpoints `b_j = (j + 1/2) h`:

* `composite_second` : if `φ` is `C²` on `[0,1]` with `|φ''| ≤ B` there, then
    `|∫₀¹ φ - h Σ φ(b_j)| ≤ B h² / 8`;
* `composite_fourth` : if `φ` is `C⁴` on `[0,1]` with `|φ⁗| ≤ B` there, then
    `|∫₀¹ φ - (h Σ φ(b_j) + (h²/24) ∫₀¹ φ'')| ≤ B h⁴ / 128`.

"`C^k` on `[0,1]`" means `ContDiffAt ℝ k φ x` at every `x ∈ [0,1]`; derivatives are ordinary
derivatives (`iteratedDeriv`). The constants `1/8` and `1/128` are not sharp.

The single-cell versions are `cell_second`, `cell_fourth` and `cell_fourth_corrected`. The
proof symmetrizes about the cell centre, `e(u) = φ(c+u) + φ(c-u)`, which is even, and applies
the even Taylor estimates.
-/

namespace BakerSpherical.Midpoint

open BakerSpherical.UniformTaylor BakerSpherical.CrossContinuous BakerSpherical.LocalTaylor
open intervalIntegral Finset

/-! ### Derivatives of shifted and reflected functions -/

theorem iteratedDeriv_shift_add (φ : ℝ → ℝ) (c u : ℝ) {n k : ℕ} (hk : k ≤ n)
    (hφ : ContDiffAt ℝ n φ (c + u)) :
    iteratedDeriv k (fun u => φ (c + u)) u = iteratedDeriv k φ (c + u) := by
  have h := iteratedDeriv_comp_line (f := φ) (a := fun u : ℝ => c + u) (v := 1)
    (fun u => by simpa using (hasDerivAt_id' u).const_add c) k hk u hφ
  rw [h, iteratedDeriv_eq_iteratedFDeriv]

theorem iteratedDeriv_shift_sub (φ : ℝ → ℝ) (c u : ℝ) {n k : ℕ} (hk : k ≤ n)
    (hφ : ContDiffAt ℝ n φ (c - u)) :
    iteratedDeriv k (fun u => φ (c - u)) u = (-1) ^ k * iteratedDeriv k φ (c - u) := by
  have h := iteratedDeriv_comp_line (f := φ) (a := fun u : ℝ => c - u) (v := -1)
    (fun u => by simpa using (hasDerivAt_id' u).const_sub c) k hk u hφ
  have h2 := (iteratedFDeriv ℝ k φ (c - u)).map_smul_univ (fun _ : Fin k => (-1 : ℝ))
    (fun _ : Fin k => (1 : ℝ))
  rw [h, iteratedDeriv_eq_iteratedFDeriv]
  simpa using h2

/-- Symmetrization of `φ` about `c`. -/
def sym (φ : ℝ → ℝ) (c u : ℝ) : ℝ := φ (c + u) + φ (c - u)

theorem sym_even (φ : ℝ → ℝ) (c u : ℝ) : sym φ c (-u) = sym φ c u := by
  simp [sym, sub_eq_add_neg, add_comm]

theorem sym_zero (φ : ℝ → ℝ) (c : ℝ) : sym φ c 0 = 2 * φ c := by
  simp [sym]; ring

theorem sym_contDiffAt (φ : ℝ → ℝ) (c u : ℝ) {n : ℕ} (hp : ContDiffAt ℝ n φ (c + u))
    (hm : ContDiffAt ℝ n φ (c - u)) : ContDiffAt ℝ n (sym φ c) u :=
  (ContDiffAt.comp u hp (contDiffAt_const.add contDiffAt_id)).add
    (ContDiffAt.comp u hm (contDiffAt_const.sub contDiffAt_id))

theorem sym_iteratedDeriv (φ : ℝ → ℝ) (c u : ℝ) {n k : ℕ} (hk : k ≤ n)
    (hp : ContDiffAt ℝ n φ (c + u)) (hm : ContDiffAt ℝ n φ (c - u)) :
    iteratedDeriv k (sym φ c) u =
      iteratedDeriv k φ (c + u) + (-1) ^ k * iteratedDeriv k φ (c - u) := by
  have hk' : (k : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  have h1 : ContDiffAt ℝ k (fun u => φ (c + u)) u :=
    ContDiffAt.comp u (hp.of_le hk') (contDiffAt_const.add contDiffAt_id)
  have h2 : ContDiffAt ℝ k (fun u => φ (c - u)) u :=
    ContDiffAt.comp u (hm.of_le hk') (contDiffAt_const.sub contDiffAt_id)
  have := iteratedDeriv_fun_add h1 h2
  rw [iteratedDeriv_shift_add φ c u hk hp, iteratedDeriv_shift_sub φ c u hk hm] at this
  exact this

/-- Points `c ± u` with `0 ≤ u ≤ h/2` lie in the cell. -/
theorem cell_mem {c h u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ h / 2) :
    c + u ∈ Set.Icc (c - h / 2) (c + h / 2) ∧ c - u ∈ Set.Icc (c - h / 2) (c + h / 2) :=
  ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem mem_of_uIcc {w u : ℝ} (hw : 0 ≤ w) (hu : u ∈ Set.uIcc 0 w) : 0 ≤ u ∧ u ≤ w := by
  rwa [Set.uIcc_of_le hw] at hu

/-! ### Even Taylor estimate of order two -/

/-- For an even function, `C²` between `0` and `u`, with `|g''| ≤ M` there:
`|g u - g 0| ≤ M u² / 2`. -/
theorem even_taylor2_local (g : ℝ → ℝ) (M u : ℝ)
    (hsmooth : ∀ x ∈ Set.uIcc 0 u, ContDiffAt ℝ 2 g x)
    (hbound : ∀ ξ ∈ Set.uIcc 0 u, |iteratedDeriv 2 g ξ| ≤ M)
    (heven : ∀ x : ℝ, g (-x) = g x) :
    |g u - g 0| ≤ M * u ^ 2 / 2 := by
  by_cases hu : u = 0
  · subst hu; simp
  have hz : (0 : ℝ) ∈ Set.uIcc 0 u := by simp
  have hon : ContDiffOn ℝ ((1 : ℕ) + 1 : ℕ) g (Set.uIcc 0 u) := fun x hx =>
    (hsmooth x hx).contDiffWithinAt
  obtain ⟨ξ, hξ, hEq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := g) (x := u)
    (x₀ := 0) (n := 1) (Ne.symm hu) (by exact_mod_cast hon)
  have hξ' : ξ ∈ Set.uIcc 0 u := Set.Ioo_subset_Icc_self hξ
  have h1 : iteratedDerivWithin 1 g (Set.uIcc 0 u) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hu))
      ((hsmooth 0 hz).of_le (by norm_num)) hz]
    exact (even_odd_derivatives_zero g heven).1
  have hpoly : taylorWithinEval g 1 (Set.uIcc 0 u) 0 u = g 0 := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, h1, iteratedDerivWithin_zero]
  rw [hpoly] at hEq
  have hsq : 0 ≤ u ^ 2 := sq_nonneg u
  rw [hEq]
  have hfact : ((1 + 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hfact, sub_zero, abs_div, abs_mul, abs_of_nonneg hsq,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound ξ hξ') hsq) (by norm_num)

/-! ### One cell -/

/-- The integral over a cell is the integral of the symmetrization over a half cell. -/
theorem cell_integral_sym (φ : ℝ → ℝ) (c h : ℝ) (hh : 0 < h)
    (hφ : ContinuousOn φ (Set.Icc (c - h / 2) (c + h / 2))) :
    ∫ x in (c - h / 2)..(c + h / 2), φ x = ∫ u in (0 : ℝ)..(h / 2), sym φ c u := by
  have hI1 : IntervalIntegrable φ MeasureTheory.volume (c - h / 2) c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact hφ.mono (Set.Icc_subset_Icc_right (by linarith))
  have hI2 : IntervalIntegrable φ MeasureTheory.volume c (c + h / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact hφ.mono (Set.Icc_subset_Icc_left (by linarith))
  have hc1 : ContinuousOn (fun u => φ (c + u)) (Set.uIcc 0 (h / 2)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hφ.comp (continuous_const.add continuous_id).continuousOn
      (fun u hu => (cell_mem hu.1 hu.2).1)
  have hc2 : ContinuousOn (fun u => φ (c - u)) (Set.uIcc 0 (h / 2)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hφ.comp (continuous_const.sub continuous_id).continuousOn
      (fun u hu => (cell_mem hu.1 hu.2).2)
  have e1 : ∫ u in (0 : ℝ)..(h / 2), φ (c + u) = ∫ x in c..(c + h / 2), φ x := by
    rw [integral_comp_add_left]; simp
  have e2 : ∫ u in (0 : ℝ)..(h / 2), φ (c - u) = ∫ x in (c - h / 2)..c, φ x := by
    rw [integral_comp_sub_left]; simp
  unfold sym
  rw [integral_add hc1.intervalIntegrable hc2.intervalIntegrable, e1, e2,
    ← integral_add_adjacent_intervals hI1 hI2]
  ring

/-- One cell, order two: `|∫_cell ψ - h ψ(c)| ≤ B h³ / 8`. -/
theorem cell_second (ψ : ℝ → ℝ) (c h B : ℝ) (hh : 0 < h)
    (hψ : ∀ x ∈ Set.Icc (c - h / 2) (c + h / 2), ContDiffAt ℝ 2 ψ x)
    (hB : ∀ x ∈ Set.Icc (c - h / 2) (c + h / 2), |iteratedDeriv 2 ψ x| ≤ B) :
    |(∫ x in (c - h / 2)..(c + h / 2), ψ x) - h * ψ c| ≤ B * h ^ 3 / 8 := by
  have hcont : ContinuousOn ψ (Set.Icc (c - h / 2) (c + h / 2)) := fun x hx =>
    (hψ x hx).continuousAt.continuousWithinAt
  have hh2 : (0 : ℝ) ≤ h / 2 := by linarith
  have hsymcd : ∀ u, 0 ≤ u → u ≤ h / 2 → ContDiffAt ℝ 2 (sym ψ c) u := fun u h0 h1 =>
    sym_contDiffAt ψ c u (n := 2) (hψ _ (cell_mem h0 h1).1) (hψ _ (cell_mem h0 h1).2)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB c ⟨by linarith, by linarith⟩)
  have hpt : ∀ u ∈ Set.uIoc (0 : ℝ) (h / 2), ‖sym ψ c u - sym ψ c 0‖ ≤ B * (h / 2) ^ 2 := by
    intro u hu
    rw [Set.uIoc_of_le hh2] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have key := even_taylor2_local (sym ψ c) (2 * B) u
      (fun x hx => by
        obtain ⟨a, b⟩ := mem_of_uIcc hu0 hx
        exact hsymcd x a (b.trans hu.2))
      (fun ξ hξ => by
        obtain ⟨a, b⟩ := mem_of_uIcc hu0 hξ
        have m := cell_mem (c := c) a (b.trans hu.2)
        rw [sym_iteratedDeriv ψ c ξ (n := 2) le_rfl (hψ _ m.1) (hψ _ m.2)]
        calc |iteratedDeriv 2 ψ (c + ξ) + (-1) ^ 2 * iteratedDeriv 2 ψ (c - ξ)|
            ≤ |iteratedDeriv 2 ψ (c + ξ)| + |(-1) ^ 2 * iteratedDeriv 2 ψ (c - ξ)| :=
              abs_add_le _ _
          _ ≤ B + B := by
              refine add_le_add (hB _ m.1) ?_
              rw [abs_mul]; simpa using hB _ m.2
          _ = 2 * B := by ring)
      (sym_even ψ c)
    rw [Real.norm_eq_abs]
    calc |sym ψ c u - sym ψ c 0| ≤ 2 * B * u ^ 2 / 2 := key
      _ = B * u ^ 2 := by ring
      _ ≤ B * (h / 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hB0
          exact pow_le_pow_left₀ hu0 hu.2 2
  have hsymcont : ContinuousOn (sym ψ c) (Set.uIcc 0 (h / 2)) := by
    rw [Set.uIcc_of_le hh2]
    exact fun u hu => (hsymcd u hu.1 hu.2).continuousAt.continuousWithinAt
  have hint := norm_integral_le_of_norm_le_const hpt
  rw [integral_sub hsymcont.intervalIntegrable intervalIntegrable_const, integral_const,
    Real.norm_eq_abs, sym_zero, sub_zero, abs_of_nonneg hh2] at hint
  rw [cell_integral_sym ψ c h hh hcont]
  have e : (h / 2) • (2 * ψ c) = h * ψ c := by simp; ring
  rw [e] at hint
  calc |(∫ u in (0 : ℝ)..(h / 2), sym ψ c u) - h * ψ c| ≤ B * (h / 2) ^ 2 * (h / 2) := hint
    _ = B * h ^ 3 / 8 := by ring

/-- One cell, order four: `|∫_cell φ - (h φ(c) + (h³/24) φ''(c))| ≤ B h⁵ / 384`. -/
theorem cell_fourth (φ : ℝ → ℝ) (c h B : ℝ) (hh : 0 < h)
    (hφ : ∀ x ∈ Set.Icc (c - h / 2) (c + h / 2), ContDiffAt ℝ 4 φ x)
    (hB : ∀ x ∈ Set.Icc (c - h / 2) (c + h / 2), |iteratedDeriv 4 φ x| ≤ B) :
    |(∫ x in (c - h / 2)..(c + h / 2), φ x) - (h * φ c + h ^ 3 / 24 * iteratedDeriv 2 φ c)| ≤
      B * h ^ 5 / 384 := by
  have hcont : ContinuousOn φ (Set.Icc (c - h / 2) (c + h / 2)) := fun x hx =>
    (hφ x hx).continuousAt.continuousWithinAt
  have hh2 : (0 : ℝ) ≤ h / 2 := by linarith
  have hcc : c ∈ Set.Icc (c - h / 2) (c + h / 2) := ⟨by linarith, by linarith⟩
  have hsymcd : ∀ u, 0 ≤ u → u ≤ h / 2 → ContDiffAt ℝ 4 (sym φ c) u := fun u h0 h1 =>
    sym_contDiffAt φ c u (n := 4) (hφ _ (cell_mem h0 h1).1) (hφ _ (cell_mem h0 h1).2)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB c hcc)
  have hd2 : iteratedDeriv 2 (sym φ c) 0 = 2 * iteratedDeriv 2 φ c := by
    have := sym_iteratedDeriv φ c 0 (n := 4) (k := 2) (by norm_num)
      (by simpa using hφ c hcc) (by simpa using hφ c hcc)
    rw [this]; simp; ring
  have hpt : ∀ u ∈ Set.uIoc (0 : ℝ) (h / 2),
      ‖sym φ c u - (2 * φ c + iteratedDeriv 2 φ c * u ^ 2)‖ ≤ B * (h / 2) ^ 4 / 12 := by
    intro u hu
    rw [Set.uIoc_of_le hh2] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have key := even_taylor_remainder_local (sym φ c) (2 * B) u (ne_of_gt hu.1)
      (fun x hx => by
        obtain ⟨a, b⟩ := mem_of_uIcc hu0 hx
        exact hsymcd x a (b.trans hu.2))
      (fun ξ hξ => by
        obtain ⟨a, b⟩ := mem_of_uIcc hu0 hξ
        have m := cell_mem (c := c) a (b.trans hu.2)
        rw [sym_iteratedDeriv φ c ξ (n := 4) le_rfl (hφ _ m.1) (hφ _ m.2)]
        calc |iteratedDeriv 4 φ (c + ξ) + (-1) ^ 4 * iteratedDeriv 4 φ (c - ξ)|
            ≤ |iteratedDeriv 4 φ (c + ξ)| + |(-1) ^ 4 * iteratedDeriv 4 φ (c - ξ)| :=
              abs_add_le _ _
          _ ≤ B + B := by
              refine add_le_add (hB _ m.1) ?_
              rw [abs_mul]; simpa using hB _ m.2
          _ = 2 * B := by ring)
      (sym_even φ c)
    rw [hd2, sym_zero] at key
    rw [Real.norm_eq_abs]
    have e : 2 * φ c + 2 * iteratedDeriv 2 φ c * u ^ 2 / 2 =
        2 * φ c + iteratedDeriv 2 φ c * u ^ 2 := by ring
    rw [e] at key
    calc |sym φ c u - (2 * φ c + iteratedDeriv 2 φ c * u ^ 2)| ≤ 2 * B * u ^ 4 / 24 := key
      _ = B * u ^ 4 / 12 := by ring
      _ ≤ B * (h / 2) ^ 4 / 12 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hu.2 4) hB0
  have hsymcont : ContinuousOn (sym φ c) (Set.uIcc 0 (h / 2)) := by
    rw [Set.uIcc_of_le hh2]
    exact fun u hu => (hsymcd u hu.1 hu.2).continuousAt.continuousWithinAt
  have hpolyint : IntervalIntegrable (fun u : ℝ => 2 * φ c + iteratedDeriv 2 φ c * u ^ 2)
      MeasureTheory.volume 0 (h / 2) := (by fun_prop : Continuous fun u : ℝ =>
        2 * φ c + iteratedDeriv 2 φ c * u ^ 2).intervalIntegrable _ _
  have hint := norm_integral_le_of_norm_le_const hpt
  have hpolyval : ∫ u in (0 : ℝ)..(h / 2), (2 * φ c + iteratedDeriv 2 φ c * u ^ 2) =
      h * φ c + h ^ 3 / 24 * iteratedDeriv 2 φ c := by
    rw [integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun u : ℝ => iteratedDeriv 2 φ c * u ^ 2).intervalIntegrable _ _),
      integral_const, integral_const_mul, integral_pow]
    simp; ring
  rw [integral_sub hsymcont.intervalIntegrable hpolyint, hpolyval, Real.norm_eq_abs, sub_zero,
    abs_of_nonneg hh2] at hint
  rw [cell_integral_sym φ c h hh hcont]
  calc |(∫ u in (0 : ℝ)..(h / 2), sym φ c u) - (h * φ c + h ^ 3 / 24 * iteratedDeriv 2 φ c)|
      ≤ B * (h / 2) ^ 4 / 12 * (h / 2) := hint
    _ = B * h ^ 5 / 384 := by ring

/-- The second derivative of a `C⁴` function is `C²`. -/
theorem contDiffAt_iteratedDeriv_two (φ : ℝ → ℝ) (x : ℝ) (hφ : ContDiffAt ℝ 4 φ x) :
    ContDiffAt ℝ 2 (iteratedDeriv 2 φ) x := by
  have h1 : ContDiffAt ℝ 2 (iteratedFDeriv ℝ 2 φ) x :=
    hφ.iteratedFDeriv_right (m := 2) (i := 2) (by norm_num)
  have h2 : iteratedDeriv 2 φ = fun x => iteratedFDeriv ℝ 2 φ x (fun _ : Fin 2 => (1 : ℝ)) :=
    funext fun x => iteratedDeriv_eq_iteratedFDeriv
  rw [h2]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ) ℝ
    (fun _ : Fin 2 => (1 : ℝ))).contDiff.contDiffAt.comp x h1

theorem iteratedDeriv_two_two (φ : ℝ → ℝ) :
    iteratedDeriv 2 (iteratedDeriv 2 φ) = iteratedDeriv 4 φ := by
  simp only [iteratedDeriv_eq_iterate]; rfl

/-- One cell, order four, with the correction written as an integral:
`|∫_cell φ - (h φ(c) + (h²/24) ∫_cell φ'')| ≤ B h⁵ / 128`. -/
theorem cell_fourth_corrected (φ : ℝ → ℝ) (c h B : ℝ) (hh : 0 < h)
    (hφ : ∀ x ∈ Set.Icc (c - h / 2) (c + h / 2), ContDiffAt ℝ 4 φ x)
    (hB : ∀ x ∈ Set.Icc (c - h / 2) (c + h / 2), |iteratedDeriv 4 φ x| ≤ B) :
    |(∫ x in (c - h / 2)..(c + h / 2), φ x) -
        (h * φ c + h ^ 2 / 24 * ∫ x in (c - h / 2)..(c + h / 2), iteratedDeriv 2 φ x)| ≤
      B * h ^ 5 / 128 := by
  have h4 := cell_fourth φ c h B hh hφ hB
  have h2 := cell_second (iteratedDeriv 2 φ) c h B hh
    (fun x hx => contDiffAt_iteratedDeriv_two φ x (hφ x hx))
    (fun x hx => by rw [iteratedDeriv_two_two]; exact hB x hx)
  have hk : (0 : ℝ) ≤ h ^ 2 / 24 := by positivity
  have e : (∫ x in (c - h / 2)..(c + h / 2), φ x) -
      (h * φ c + h ^ 2 / 24 * ∫ x in (c - h / 2)..(c + h / 2), iteratedDeriv 2 φ x) =
      ((∫ x in (c - h / 2)..(c + h / 2), φ x) -
          (h * φ c + h ^ 3 / 24 * iteratedDeriv 2 φ c)) -
        h ^ 2 / 24 * ((∫ x in (c - h / 2)..(c + h / 2), iteratedDeriv 2 φ x) -
          h * iteratedDeriv 2 φ c) := by ring
  rw [e]
  calc |((∫ x in (c - h / 2)..(c + h / 2), φ x) -
            (h * φ c + h ^ 3 / 24 * iteratedDeriv 2 φ c)) -
          h ^ 2 / 24 * ((∫ x in (c - h / 2)..(c + h / 2), iteratedDeriv 2 φ x) -
            h * iteratedDeriv 2 φ c)|
      ≤ |(∫ x in (c - h / 2)..(c + h / 2), φ x) -
            (h * φ c + h ^ 3 / 24 * iteratedDeriv 2 φ c)| +
          |h ^ 2 / 24 * ((∫ x in (c - h / 2)..(c + h / 2), iteratedDeriv 2 φ x) -
            h * iteratedDeriv 2 φ c)| := abs_sub _ _
    _ ≤ B * h ^ 5 / 384 + h ^ 2 / 24 * (B * h ^ 3 / 8) := by
        rw [abs_mul, abs_of_nonneg hk]
        exact add_le_add h4 (mul_le_mul_of_nonneg_left h2 hk)
    _ = B * h ^ 5 / 128 := by ring

/-! ### The composite rule on `[0, 1]` -/

/-- Grid facts: the cell `j` of the uniform grid with `N` cells. -/
theorem grid_cell {N j : ℕ} (hN : 0 < N) (hj : j < N) :
    ((j : ℝ) + 1 / 2) / N - 1 / (N : ℝ) / 2 = (j : ℝ) / N ∧
      ((j : ℝ) + 1 / 2) / N + 1 / (N : ℝ) / 2 = ((j + 1 : ℕ) : ℝ) / N ∧
      Set.Icc ((j : ℝ) / N) (((j + 1 : ℕ) : ℝ) / N) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hj' : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
  refine ⟨by field_simp; ring, by push_cast; field_simp; ring, ?_⟩
  intro x hx
  exact ⟨le_trans (by positivity) hx.1, hx.2.trans ((div_le_one hNpos).mpr hj')⟩

/-- Additivity of the integral over the uniform grid. -/
theorem sum_cells (g : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∑ j ∈ range N, ∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), g x = ∫ x in (0 : ℝ)..1, g x := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key := sum_integral_adjacent_intervals (f := g) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ) / N) (n := N) (fun k hk => by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by gcongr; exact_mod_cast Nat.le_succ k)]
      exact hg.mono (grid_cell hN hk).2.2)
  simpa [div_self (ne_of_gt hNpos)] using key

/-- From a per-cell estimate to an estimate on `[0, 1]`. -/
theorem composite_of_cells (g : ℝ → ℝ) (T : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (E : ℝ)
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hcell : ∀ j < N, |(∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), g x) - T j| ≤ E) :
    |(∫ x in (0 : ℝ)..1, g x) - ∑ j ∈ range N, T j| ≤ N * E := by
  rw [← sum_cells g hN hg, ← sum_sub_distrib]
  calc |∑ j ∈ range N, ((∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), g x) - T j)|
      ≤ ∑ j ∈ range N, |(∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), g x) - T j| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range N, E := sum_le_sum fun j hj => hcell j (mem_range.mp hj)
    _ = N * E := by simp

/-- **Composite midpoint rule, order two.** -/
theorem composite_second (ψ : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (B : ℝ)
    (hψ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 ψ x)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 ψ x| ≤ B) :
    |(∫ x in (0 : ℝ)..1, ψ x) - 1 / (N : ℝ) * ∑ j ∈ range N, ψ (((j : ℝ) + 1 / 2) / N)| ≤
      B * (1 / (N : ℝ)) ^ 2 / 8 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcont : ContinuousOn ψ (Set.Icc 0 1) := fun x hx =>
    (hψ x hx).continuousAt.continuousWithinAt
  have key := composite_of_cells ψ (fun j => 1 / (N : ℝ) * ψ (((j : ℝ) + 1 / 2) / N)) hN
    (B * (1 / (N : ℝ)) ^ 3 / 8) hcont (fun j hj => by
      obtain ⟨e1, e2, hsub⟩ := grid_cell hN hj
      have := cell_second ψ (((j : ℝ) + 1 / 2) / N) (1 / (N : ℝ)) B (by positivity)
        (fun x hx => hψ x (hsub (by rwa [e1, e2] at hx)))
        (fun x hx => hB x (hsub (by rwa [e1, e2] at hx)))
      rwa [e1, e2] at this)
  rw [← mul_sum] at key
  calc _ ≤ (N : ℝ) * (B * (1 / (N : ℝ)) ^ 3 / 8) := key
    _ = B * (1 / (N : ℝ)) ^ 2 / 8 := by field_simp

/-- **Composite midpoint rule, order four, with the `h²` correction.** -/
theorem composite_fourth (φ : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (B : ℝ)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 4 φ x)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 4 φ x| ≤ B) :
    |(∫ x in (0 : ℝ)..1, φ x) -
        (1 / (N : ℝ) * ∑ j ∈ range N, φ (((j : ℝ) + 1 / 2) / N) +
          (1 / (N : ℝ)) ^ 2 / 24 * ∫ x in (0 : ℝ)..1, iteratedDeriv 2 φ x)| ≤
      B * (1 / (N : ℝ)) ^ 4 / 128 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcont : ContinuousOn φ (Set.Icc 0 1) := fun x hx =>
    (hφ x hx).continuousAt.continuousWithinAt
  have hcont2 : ContinuousOn (iteratedDeriv 2 φ) (Set.Icc 0 1) := fun x hx =>
    (contDiffAt_iteratedDeriv_two φ x (hφ x hx)).continuousAt.continuousWithinAt
  have key := composite_of_cells φ (fun j => 1 / (N : ℝ) * φ (((j : ℝ) + 1 / 2) / N) +
      (1 / (N : ℝ)) ^ 2 / 24 *
        ∫ x in ((j : ℝ) / N)..(((j + 1 : ℕ) : ℝ) / N), iteratedDeriv 2 φ x) hN
    (B * (1 / (N : ℝ)) ^ 5 / 128) hcont (fun j hj => by
      obtain ⟨e1, e2, hsub⟩ := grid_cell hN hj
      have := cell_fourth_corrected φ (((j : ℝ) + 1 / 2) / N) (1 / (N : ℝ)) B (by positivity)
        (fun x hx => hφ x (hsub (by rwa [e1, e2] at hx)))
        (fun x hx => hB x (hsub (by rwa [e1, e2] at hx)))
      rwa [e1, e2] at this)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_cells _ hN hcont2] at key
  calc _ ≤ (N : ℝ) * (B * (1 / (N : ℝ)) ^ 5 / 128) := key
    _ = B * (1 / (N : ℝ)) ^ 4 / 128 := by field_simp

end BakerSpherical.Midpoint

#print axioms BakerSpherical.Midpoint.even_taylor2_local
#print axioms BakerSpherical.Midpoint.cell_integral_sym
#print axioms BakerSpherical.Midpoint.cell_second
#print axioms BakerSpherical.Midpoint.cell_fourth
#print axioms BakerSpherical.Midpoint.cell_fourth_corrected
#print axioms BakerSpherical.Midpoint.composite_second
#print axioms BakerSpherical.Midpoint.composite_fourth
