import Mathlib
import MidpointQuadrature1D
import SphericalCellSum

/-!
# Midpoint quadrature on the unit square, with the `h²` correction term

For `f : ℝ × ℝ → ℝ`, `N ≥ 1`, `h = 1/N` and the midpoint centres `x_ij` of `SphericalCellSum`:

* `midpoint2D_second` : if `f` is `C²` on the closed unit square, there is `K ≥ 0` with
    `|h² Σ_ij f(x_ij) - ∬ f| ≤ K h²`  for all `N ≥ 1`;
* `midpoint2D_fourth` : if `f` is `C⁴` on the closed unit square, there is `K ≥ 0` with
    `|h² Σ_ij f(x_ij) - (∬ f - (h²/24) (∬ f_ss + ∬ f_tt))| ≤ K h⁴`  for all `N ≥ 1`.

Conventions: "`C^k` on the square" means `ContDiffAt ℝ k f p` at every point `p` of the closed
square; `∬ g` is the iterated integral `∫ s in 0..1, ∫ t in 0..1, g (s, t)`; and
`ps k f`, `pt k f` are the `k`-th pure partial derivatives in `s` and `t`, written as
`iteratedFDeriv ℝ k f p` applied to `(1,0)` resp. `(0,1)` `k` times.

No quadrature estimate is assumed anywhere; `K` is produced from compactness.
-/

namespace BakerSpherical.Midpoint

open BakerSpherical.UniformTaylor BakerSpherical.GlobalSum
open intervalIntegral Finset

/-- `k`-th pure partial derivative in the first variable. -/
noncomputable def ps (k : ℕ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDeriv ℝ k f p (fun _ : Fin k => ((1 : ℝ), (0 : ℝ)))

/-- `k`-th pure partial derivative in the second variable. -/
noncomputable def pt (k : ℕ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  iteratedFDeriv ℝ k f p (fun _ : Fin k => ((0 : ℝ), (1 : ℝ)))

theorem ps_contDiffAt {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {n m k : ℕ} (hf : ContDiffAt ℝ n f p)
    (hmk : m + k ≤ n) : ContDiffAt ℝ m (ps k f) p :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × ℝ) ℝ
    (fun _ : Fin k => ((1 : ℝ), (0 : ℝ)))).contDiff.contDiffAt.comp p
    (hf.iteratedFDeriv_right (m := m) (i := k) (by exact_mod_cast hmk))

theorem pt_contDiffAt {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {n m k : ℕ} (hf : ContDiffAt ℝ n f p)
    (hmk : m + k ≤ n) : ContDiffAt ℝ m (pt k f) p :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × ℝ) ℝ
    (fun _ : Fin k => ((0 : ℝ), (1 : ℝ)))).contDiff.contDiffAt.comp p
    (hf.iteratedFDeriv_right (m := m) (i := k) (by exact_mod_cast hmk))

/-- Derivatives of the `t`-slice are the `t`-partials. -/
theorem slice_t (f : ℝ × ℝ → ℝ) (s t : ℝ) {n k : ℕ} (hk : k ≤ n)
    (hf : ContDiffAt ℝ n f (s, t)) :
    iteratedDeriv k (fun t => f (s, t)) t = pt k f (s, t) :=
  slice_iteratedDeriv f s t hk hf

/-- Derivatives of the `s`-slice are the `s`-partials. -/
theorem slice_s (f : ℝ × ℝ → ℝ) (s t : ℝ) {n k : ℕ} (hk : k ≤ n)
    (hf : ContDiffAt ℝ n f (s, t)) :
    iteratedDeriv k (fun s => f (s, t)) s = ps k f (s, t) :=
  iteratedDeriv_comp_line (a := fun u : ℝ => (u, t))
    (fun u => HasDerivAt.prodMk (hasDerivAt_id' u) (hasDerivAt_const u t)) k hk s hf

theorem slice_t_contDiffAt (f : ℝ × ℝ → ℝ) (s t : ℝ) {n : ℕ} (hf : ContDiffAt ℝ n f (s, t)) :
    ContDiffAt ℝ n (fun t => f (s, t)) t :=
  ContDiffAt.comp t hf (contDiffAt_const.prodMk contDiffAt_id)

theorem slice_s_contDiffAt (f : ℝ × ℝ → ℝ) (s t : ℝ) {n : ℕ} (hf : ContDiffAt ℝ n f (s, t)) :
    ContDiffAt ℝ n (fun s => f (s, t)) s :=
  ContDiffAt.comp s hf (contDiffAt_id.prodMk contDiffAt_const)

/-! ### Continuity and integration helpers on the unit square -/

theorem mem_sq {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (s, t) ∈ unitSquare := ⟨hs, ht⟩

/-- A function continuous on the compact unit square is bounded there. -/
theorem exists_bound_sq (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g unitSquare) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ unitSquare, |g p| ≤ B := by
  obtain ⟨B, hB0, hB⟩ :=
    compact_uniform_norm_bound unitSquare unitSquare_compact unitSquare_nonempty g hg
  exact ⟨B, hB0, fun p hp => by simpa using hB p hp⟩

theorem slice_t_continuousOn {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g unitSquare) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : ContinuousOn (fun t => g (s, t)) (Set.Icc 0 1) :=
  hg.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => mem_sq hs ht)

theorem slice_s_continuousOn {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g unitSquare) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ContinuousOn (fun s => g (s, t)) (Set.Icc 0 1) :=
  hg.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => mem_sq hs ht)

/-- Clamp to `[0, 1]`. -/
noncomputable def clamp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clamp_mem (x : ℝ) : clamp x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clamp_eq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : clamp x = x := by
  unfold clamp; rw [min_eq_right hx.2, max_eq_right hx.1]

/-- The inner integral of a function continuous on the square is continuous on `[0, 1]`. -/
theorem param_continuousOn {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g unitSquare) :
    ContinuousOn (fun s => ∫ t in (0 : ℝ)..1, g (s, t)) (Set.Icc 0 1) := by
  have hclamp : Continuous clamp := by unfold clamp; fun_prop
  have hgt : Continuous (fun p : ℝ × ℝ => g (clamp p.1, clamp p.2)) :=
    hg.comp_continuous ((hclamp.comp continuous_fst).prodMk (hclamp.comp continuous_snd))
      (fun p => mem_sq (clamp_mem _) (clamp_mem _))
  have hc : Continuous (fun s => ∫ t in (0 : ℝ)..1, g (clamp s, clamp t)) :=
    continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s t => g (clamp s, clamp t)) hgt 0 1
  refine hc.continuousOn.congr fun s hs => ?_
  refine integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only [clamp_eq hs, clamp_eq ht]

theorem intervalIntegrable_of_continuousOn {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Icc 0 1)) :
    IntervalIntegrable u MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rwa [Set.uIcc_of_le zero_le_one]

/-- Integrating a pointwise estimate `|u s - h Σ_j w_j s| ≤ K` over `[0, 1]`. -/
theorem outer_integrate (u : ℝ → ℝ) (w : ℕ → ℝ → ℝ) (N : ℕ) (h K : ℝ)
    (hu : ContinuousOn u (Set.Icc 0 1)) (hw : ∀ j < N, ContinuousOn (w j) (Set.Icc 0 1))
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, |u s - h * ∑ j ∈ range N, w j s| ≤ K) :
    |(∫ s in (0 : ℝ)..1, u s) - h * ∑ j ∈ range N, ∫ s in (0 : ℝ)..1, w j s| ≤ K := by
  have hsum : ContinuousOn (fun s => h * ∑ j ∈ range N, w j s) (Set.Icc 0 1) :=
    continuousOn_const.mul (continuousOn_finsetSum _ fun j hj => hw j (mem_range.mp hj))
  have e : ∫ s in (0 : ℝ)..1, (h * ∑ j ∈ range N, w j s) =
      h * ∑ j ∈ range N, ∫ s in (0 : ℝ)..1, w j s := by
    rw [integral_const_mul, integral_finsetSum]
    exact fun j hj => intervalIntegrable_of_continuousOn (hw j (mem_range.mp hj))
  rw [← e, ← integral_sub (intervalIntegrable_of_continuousOn hu)
    (intervalIntegrable_of_continuousOn hsum)]
  have := norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := K)
    (f := fun s => u s - h * ∑ j ∈ range N, w j s) (fun s hs => by
      rw [Set.uIoc_of_le zero_le_one] at hs
      exact hK s ⟨hs.1.le, hs.2⟩)
  simpa using this

theorem coordN_mem {N j : ℕ} (hj : j < N) : ((j : ℝ) + 1 / 2) / N ∈ Set.Icc (0 : ℝ) 1 :=
  coord_mem hj

/-! ### The four one-directional steps -/

/-- Order two in `t`, integrated over `s`. -/
theorem step_t2 (g : ℝ × ℝ → ℝ) (hg : ∀ p ∈ unitSquare, ContDiffAt ℝ 2 g p) (B : ℝ)
    (hB : ∀ p ∈ unitSquare, |pt 2 g p| ≤ B) {N : ℕ} (hN : 0 < N) :
    |(∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, g (s, t)) -
        1 / (N : ℝ) * ∑ j ∈ range N, ∫ s in (0 : ℝ)..1, g (s, ((j : ℝ) + 1 / 2) / N)| ≤
      B * (1 / (N : ℝ)) ^ 2 / 8 := by
  have hgc : ContinuousOn g unitSquare := fun p hp => (hg p hp).continuousAt.continuousWithinAt
  exact outer_integrate (fun s => ∫ t in (0 : ℝ)..1, g (s, t))
    (fun j s => g (s, ((j : ℝ) + 1 / 2) / N)) N (1 / (N : ℝ)) (B * (1 / (N : ℝ)) ^ 2 / 8)
    (param_continuousOn hgc) (fun j hj => slice_s_continuousOn hgc (coordN_mem hj))
    (fun s hs => composite_second (fun t => g (s, t)) hN B
      (fun x hx => slice_t_contDiffAt g s x (hg _ (mem_sq hs hx)))
      (fun x hx => by
        rw [slice_t g s x (n := 2) le_rfl (hg _ (mem_sq hs hx))]
        exact hB _ (mem_sq hs hx)))

/-- Order two in `s` along the lines `t = b_j`, summed over `j`. -/
theorem step_s2 (g : ℝ × ℝ → ℝ) (hg : ∀ p ∈ unitSquare, ContDiffAt ℝ 2 g p) (B : ℝ)
    (hB : ∀ p ∈ unitSquare, |ps 2 g p| ≤ B) {N : ℕ} (hN : 0 < N) :
    |(∑ j ∈ range N, ∫ s in (0 : ℝ)..1, g (s, ((j : ℝ) + 1 / 2) / N)) -
        1 / (N : ℝ) * ∑ i ∈ range N, ∑ j ∈ range N, g (center N i j)| ≤
      (N : ℝ) * (B * (1 / (N : ℝ)) ^ 2 / 8) := by
  have hcell : ∀ j ∈ range N, |(∫ s in (0 : ℝ)..1, g (s, ((j : ℝ) + 1 / 2) / N)) -
      1 / (N : ℝ) * ∑ i ∈ range N, g (center N i j)| ≤ B * (1 / (N : ℝ)) ^ 2 / 8 :=
    fun j hj => composite_second (fun s => g (s, ((j : ℝ) + 1 / 2) / N)) hN B
      (fun x hx => slice_s_contDiffAt g x _ (hg _ (mem_sq hx (coordN_mem (mem_range.mp hj)))))
      (fun x hx => by
        rw [slice_s g x _ (n := 2) le_rfl (hg _ (mem_sq hx (coordN_mem (mem_range.mp hj))))]
        exact hB _ (mem_sq hx (coordN_mem (mem_range.mp hj))))
  have hsum := (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hcell).trans (by simp :
    ∑ _j ∈ range N, B * (1 / (N : ℝ)) ^ 2 / 8 ≤ (N : ℝ) * (B * (1 / (N : ℝ)) ^ 2 / 8)))
  rw [sum_sub_distrib, ← mul_sum, sum_comm] at hsum
  exact hsum

/-- Order four in `t`, integrated over `s`. -/
theorem step_t4 (f : ℝ × ℝ → ℝ) (hf : ∀ p ∈ unitSquare, ContDiffAt ℝ 4 f p) (B : ℝ)
    (hB : ∀ p ∈ unitSquare, |pt 4 f p| ≤ B) {N : ℕ} (hN : 0 < N) :
    |(∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f (s, t)) -
        (1 / (N : ℝ)) ^ 2 / 24 * (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, pt 2 f (s, t)) -
        1 / (N : ℝ) * ∑ j ∈ range N, ∫ s in (0 : ℝ)..1, f (s, ((j : ℝ) + 1 / 2) / N)| ≤
      B * (1 / (N : ℝ)) ^ 4 / 128 := by
  have hfc : ContinuousOn f unitSquare := fun p hp => (hf p hp).continuousAt.continuousWithinAt
  have hpt2c : ContinuousOn (pt 2 f) unitSquare := fun p hp =>
    (pt_contDiffAt (m := 0) (k := 2) (hf p hp) (by norm_num)).continuousAt.continuousWithinAt
  have hΦ : ContinuousOn (fun s => ∫ t in (0 : ℝ)..1, f (s, t)) (Set.Icc 0 1) :=
    param_continuousOn hfc
  have hΨ : ContinuousOn (fun s => ∫ t in (0 : ℝ)..1, pt 2 f (s, t)) (Set.Icc 0 1) :=
    param_continuousOn hpt2c
  have hc2 : ContinuousOn (fun s => (1 / (N : ℝ)) ^ 2 / 24 * ∫ t in (0 : ℝ)..1, pt 2 f (s, t))
      (Set.Icc 0 1) := ContinuousOn.mul continuousOn_const hΨ
  have hu : ContinuousOn (fun s => (∫ t in (0 : ℝ)..1, f (s, t)) -
      (1 / (N : ℝ)) ^ 2 / 24 * ∫ t in (0 : ℝ)..1, pt 2 f (s, t)) (Set.Icc 0 1) :=
    ContinuousOn.sub hΦ hc2
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |((∫ t in (0 : ℝ)..1, f (s, t)) -
          (1 / (N : ℝ)) ^ 2 / 24 * ∫ t in (0 : ℝ)..1, pt 2 f (s, t)) -
        1 / (N : ℝ) * ∑ j ∈ range N, f (s, ((j : ℝ) + 1 / 2) / N)| ≤
      B * (1 / (N : ℝ)) ^ 4 / 128 := by
    intro s hs
    have key := composite_fourth (fun t => f (s, t)) hN B
      (fun x hx => slice_t_contDiffAt f s x (hf _ (mem_sq hs hx)))
      (fun x hx => by
        rw [slice_t f s x (n := 4) le_rfl (hf _ (mem_sq hs hx))]
        exact hB _ (mem_sq hs hx))
    have e2 : ∫ x in (0 : ℝ)..1, iteratedDeriv 2 (fun t => f (s, t)) x =
        ∫ t in (0 : ℝ)..1, pt 2 f (s, t) := integral_congr fun x hx => by
      rw [Set.uIcc_of_le zero_le_one] at hx
      exact slice_t f s x (n := 4) (by norm_num) (hf _ (mem_sq hs hx))
    rw [e2] at key
    have e : ∀ a b c : ℝ, a - b - c = a - (c + b) := fun a b c => by ring
    rw [e]
    exact key
  have h1 := outer_integrate
    (fun s => (∫ t in (0 : ℝ)..1, f (s, t)) -
      (1 / (N : ℝ)) ^ 2 / 24 * ∫ t in (0 : ℝ)..1, pt 2 f (s, t))
    (fun j s => f (s, ((j : ℝ) + 1 / 2) / N)) N (1 / (N : ℝ)) (B * (1 / (N : ℝ)) ^ 4 / 128)
    hu (fun j hj => slice_s_continuousOn hfc (coordN_mem hj)) hpt
  have eint : ∫ s in (0 : ℝ)..1, ((∫ t in (0 : ℝ)..1, f (s, t)) -
      (1 / (N : ℝ)) ^ 2 / 24 * ∫ t in (0 : ℝ)..1, pt 2 f (s, t)) =
      (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f (s, t)) -
        (1 / (N : ℝ)) ^ 2 / 24 * ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, pt 2 f (s, t) := by
    rw [integral_sub (intervalIntegrable_of_continuousOn hΦ)
      (intervalIntegrable_of_continuousOn hc2), integral_const_mul]
  rw [eint] at h1
  exact h1

/-- Order four in `s` along the lines `t = b_j`, summed over `j`. -/
theorem step_s4 (f : ℝ × ℝ → ℝ) (hf : ∀ p ∈ unitSquare, ContDiffAt ℝ 4 f p) (B : ℝ)
    (hB : ∀ p ∈ unitSquare, |ps 4 f p| ≤ B) {N : ℕ} (hN : 0 < N) :
    |(∑ j ∈ range N, ∫ s in (0 : ℝ)..1, f (s, ((j : ℝ) + 1 / 2) / N)) -
        (1 / (N : ℝ) * (∑ i ∈ range N, ∑ j ∈ range N, f (center N i j)) +
          (1 / (N : ℝ)) ^ 2 / 24 *
            ∑ j ∈ range N, ∫ s in (0 : ℝ)..1, ps 2 f (s, ((j : ℝ) + 1 / 2) / N))| ≤
      (N : ℝ) * (B * (1 / (N : ℝ)) ^ 4 / 128) := by
  have hcell : ∀ j ∈ range N, |(∫ s in (0 : ℝ)..1, f (s, ((j : ℝ) + 1 / 2) / N)) -
      (1 / (N : ℝ) * ∑ i ∈ range N, f (center N i j) +
        (1 / (N : ℝ)) ^ 2 / 24 * ∫ s in (0 : ℝ)..1, ps 2 f (s, ((j : ℝ) + 1 / 2) / N))| ≤
      B * (1 / (N : ℝ)) ^ 4 / 128 := fun j hj => by
    have hb := coordN_mem (mem_range.mp hj)
    have key := composite_fourth (fun s => f (s, ((j : ℝ) + 1 / 2) / N)) hN B
      (fun x hx => slice_s_contDiffAt f x _ (hf _ (mem_sq hx hb)))
      (fun x hx => by
        rw [slice_s f x _ (n := 4) le_rfl (hf _ (mem_sq hx hb))]
        exact hB _ (mem_sq hx hb))
    have e2 : ∫ x in (0 : ℝ)..1, iteratedDeriv 2 (fun s => f (s, ((j : ℝ) + 1 / 2) / N)) x =
        ∫ s in (0 : ℝ)..1, ps 2 f (s, ((j : ℝ) + 1 / 2) / N) := integral_congr fun x hx => by
      rw [Set.uIcc_of_le zero_le_one] at hx
      exact slice_s f x _ (n := 4) (by norm_num) (hf _ (mem_sq hx hb))
    rw [e2] at key
    exact key
  have hsum := (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hcell).trans (by simp :
    ∑ _j ∈ range N, B * (1 / (N : ℝ)) ^ 4 / 128 ≤ (N : ℝ) * (B * (1 / (N : ℝ)) ^ 4 / 128)))
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_comm] at hsum
  exact hsum

/-! ### Combining the steps (pure real arithmetic) -/

theorem combine2 (A SX SF h n Bt Bs : ℝ) (hh0 : 0 ≤ h) (hNh : n * h = 1)
    (h1 : |A - h * SX| ≤ Bt * h ^ 2 / 8) (h2 : |SX - h * SF| ≤ n * (Bs * h ^ 2 / 8)) :
    |h ^ 2 * SF - A| ≤ (Bt + Bs) / 8 * h ^ 2 := by
  have e : h ^ 2 * SF - A = -(A - h * SX) - h * (SX - h * SF) := by ring
  rw [e]
  have t2 := abs_sub (-(A - h * SX)) (h * (SX - h * SF))
  have t3 : |-(A - h * SX)| ≤ Bt * h ^ 2 / 8 := by rwa [abs_neg]
  have t4 : |h * (SX - h * SF)| ≤ h * (n * (Bs * h ^ 2 / 8)) := by
    rw [abs_mul, abs_of_nonneg hh0]; exact mul_le_mul_of_nonneg_left h2 hh0
  have t6 : h * (n * (Bs * h ^ 2 / 8)) = Bs * h ^ 2 / 8 := by
    have : h * (n * (Bs * h ^ 2 / 8)) = (n * h) * (Bs * h ^ 2 / 8) := by ring
    rw [this, hNh, one_mul]
  have t7 : (Bt + Bs) / 8 * h ^ 2 = Bt * h ^ 2 / 8 + Bs * h ^ 2 / 8 := by ring
  rw [t7]
  linarith

theorem combine4 (A Dt Ds SX SY SF h n B1 B2 B3 : ℝ) (hh0 : 0 ≤ h) (hNh : n * h = 1)
    (h1 : |A - h ^ 2 / 24 * Dt - h * SX| ≤ B1 * h ^ 4 / 128)
    (h2 : |SX - (h * SF + h ^ 2 / 24 * SY)| ≤ n * (B2 * h ^ 4 / 128))
    (h3 : |Ds - h * SY| ≤ B3 * h ^ 2 / 8) :
    |h ^ 2 * SF - (A - h ^ 2 / 24 * (Ds + Dt))| ≤ (B1 / 128 + B2 / 128 + B3 / 192) * h ^ 4 := by
  have hk : (0 : ℝ) ≤ h ^ 2 / 24 := by positivity
  have e : h ^ 2 * SF - (A - h ^ 2 / 24 * (Ds + Dt)) =
      -(A - h ^ 2 / 24 * Dt - h * SX) - h * (SX - (h * SF + h ^ 2 / 24 * SY)) +
        h ^ 2 / 24 * (Ds - h * SY) := by ring
  rw [e]
  have t1 := abs_add_le (-(A - h ^ 2 / 24 * Dt - h * SX) -
    h * (SX - (h * SF + h ^ 2 / 24 * SY))) (h ^ 2 / 24 * (Ds - h * SY))
  have t2 := abs_sub (-(A - h ^ 2 / 24 * Dt - h * SX)) (h * (SX - (h * SF + h ^ 2 / 24 * SY)))
  have t3 : |-(A - h ^ 2 / 24 * Dt - h * SX)| ≤ B1 * h ^ 4 / 128 := by rwa [abs_neg]
  have t4 : |h * (SX - (h * SF + h ^ 2 / 24 * SY))| ≤ h * (n * (B2 * h ^ 4 / 128)) := by
    rw [abs_mul, abs_of_nonneg hh0]; exact mul_le_mul_of_nonneg_left h2 hh0
  have t5 : |h ^ 2 / 24 * (Ds - h * SY)| ≤ h ^ 2 / 24 * (B3 * h ^ 2 / 8) := by
    rw [abs_mul, abs_of_nonneg hk]; exact mul_le_mul_of_nonneg_left h3 hk
  have t6 : h * (n * (B2 * h ^ 4 / 128)) = B2 * h ^ 4 / 128 := by
    have : h * (n * (B2 * h ^ 4 / 128)) = (n * h) * (B2 * h ^ 4 / 128) := by ring
    rw [this, hNh, one_mul]
  have t7 : (B1 / 128 + B2 / 128 + B3 / 192) * h ^ 4 =
      B1 * h ^ 4 / 128 + B2 * h ^ 4 / 128 + h ^ 2 / 24 * (B3 * h ^ 2 / 8) := by ring
  rw [t7]
  linarith

/-! ### The two theorems -/

/-- **Midpoint rule on the unit square, order two.** -/
theorem midpoint2D_second (q : ℝ × ℝ → ℝ) (hq : ∀ p ∈ unitSquare, ContDiffAt ℝ 2 q p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 0 < N →
      |(1 / (N : ℝ)) ^ 2 * ∑ i ∈ range N, ∑ j ∈ range N, q (center N i j) -
          ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, q (s, t)| ≤ K * (1 / (N : ℝ)) ^ 2 := by
  obtain ⟨Bt, hBt0, hBt⟩ := exists_bound_sq (pt 2 q) (fun p hp =>
    (pt_contDiffAt (m := 0) (k := 2) (hq p hp) (by norm_num)).continuousAt.continuousWithinAt)
  obtain ⟨Bs, hBs0, hBs⟩ := exists_bound_sq (ps 2 q) (fun p hp =>
    (ps_contDiffAt (m := 0) (k := 2) (hq p hp) (by norm_num)).continuousAt.continuousWithinAt)
  refine ⟨(Bt + Bs) / 8, by positivity, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact combine2 _ _ _ (1 / (N : ℝ)) N Bt Bs (by positivity) (by field_simp)
    (step_t2 q hq Bt hBt hN) (step_s2 q hq Bs hBs hN)

/-- **Midpoint rule on the unit square, order four, with the `h²` correction.** -/
theorem midpoint2D_fourth (f : ℝ × ℝ → ℝ) (hf : ∀ p ∈ unitSquare, ContDiffAt ℝ 4 f p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 0 < N →
      |(1 / (N : ℝ)) ^ 2 * ∑ i ∈ range N, ∑ j ∈ range N, f (center N i j) -
          ((∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, f (s, t)) -
            (1 / (N : ℝ)) ^ 2 / 24 *
              ((∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, ps 2 f (s, t)) +
                ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, pt 2 f (s, t)))| ≤
        K * (1 / (N : ℝ)) ^ 4 := by
  have hps2 : ∀ p ∈ unitSquare, ContDiffAt ℝ 2 (ps 2 f) p := fun p hp =>
    ps_contDiffAt (m := 2) (k := 2) (hf p hp) (by norm_num)
  obtain ⟨B1, hB10, hB1⟩ := exists_bound_sq (pt 4 f) (fun p hp =>
    (pt_contDiffAt (m := 0) (k := 4) (hf p hp) (by norm_num)).continuousAt.continuousWithinAt)
  obtain ⟨B2, hB20, hB2⟩ := exists_bound_sq (ps 4 f) (fun p hp =>
    (ps_contDiffAt (m := 0) (k := 4) (hf p hp) (by norm_num)).continuousAt.continuousWithinAt)
  obtain ⟨B3, hB30, hB3⟩ := exists_bound_sq (pt 2 (ps 2 f)) (fun p hp =>
    (pt_contDiffAt (m := 0) (k := 2) (hps2 p hp)
      (by norm_num)).continuousAt.continuousWithinAt)
  refine ⟨B1 / 128 + B2 / 128 + B3 / 192, by positivity, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact combine4 _ _ _ _ _ _ (1 / (N : ℝ)) N B1 B2 B3 (by positivity) (by field_simp)
    (step_t4 f hf B1 hB1 hN) (step_s4 f hf B2 hB2 hN) (step_t2 (ps 2 f) hps2 B3 hB3 hN)

end BakerSpherical.Midpoint

#print axioms BakerSpherical.Midpoint.param_continuousOn
#print axioms BakerSpherical.Midpoint.outer_integrate
#print axioms BakerSpherical.Midpoint.step_t2
#print axioms BakerSpherical.Midpoint.step_s2
#print axioms BakerSpherical.Midpoint.step_t4
#print axioms BakerSpherical.Midpoint.step_s4
#print axioms BakerSpherical.Midpoint.midpoint2D_second
#print axioms BakerSpherical.Midpoint.midpoint2D_fourth
