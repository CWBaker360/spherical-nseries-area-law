import Mathlib

/-!
# Spherical N-Series v2.4 — the affine chain-rule identity for slices

For a map `f : E → F` and a curve `a : ℝ → E` with constant derivative `v` (an affine line),
the `k`-th ordinary derivative of `f ∘ a` is the `k`-th Fréchet derivative of `f` evaluated on
`(v, …, v)`. Only *local* regularity is assumed: `f` is `C^n` at the single point `a u₀`.

* `iteratedDeriv_comp_line`  : the general statement, for `k ≤ n`;
* `slice_iteratedDeriv`      : the vertical slice `u ↦ G (y, u)`, any order `k ≤ n`;
* `slice_fourth_identity`    : the case `k = 4`, i.e. the hypothesis `hidentity` of
  `slice_fourth_bound_of_identity`.

Scope: this is the identity only. The bound on the slice derivative and the Taylor
remainder are in other files.
-/

namespace BakerSpherical.UniformTaylor

open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Along a curve `a` with constant derivative `v`, the `k`-th derivative of `f ∘ a` is the
`k`-th Fréchet derivative of `f` applied to `(v, …, v)`, wherever `f` is `C^n` with `k ≤ n`. -/
theorem iteratedDeriv_comp_line {f : E → F} {a : ℝ → E} {v : E}
    (ha : ∀ u, HasDerivAt a v u) {n : ℕ} :
    ∀ (k : ℕ), k ≤ n → ∀ (u₀ : ℝ), ContDiffAt ℝ n f (a u₀) →
      iteratedDeriv k (fun u => f (a u)) u₀ =
        iteratedFDeriv ℝ k f (a u₀) (fun _ : Fin k => v) := by
  intro k
  induction k with
  | zero =>
    intro _ u₀ _
    simp
  | succ k ih =>
    intro hk u₀ hf
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have hev : ∀ᶠ u in 𝓝 u₀, ContDiffAt ℝ n f (a u) :=
      (ha u₀).continuousAt.eventually (hf.eventually (by simp))
    have heq : iteratedDeriv k (fun u => f (a u)) =ᶠ[𝓝 u₀]
        fun u => iteratedFDeriv ℝ k f (a u) (fun _ : Fin k => v) :=
      hev.mono fun u hu => ih hk' u hu
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd : HasFDerivAt (iteratedFDeriv ℝ k f)
        (fderiv ℝ (iteratedFDeriv ℝ k f) (a u₀)) (a u₀) :=
      (hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_of_succ_le hk)).hasFDerivAt
    have h1 : HasDerivAt (fun u => iteratedFDeriv ℝ k f (a u))
        (fderiv ℝ (iteratedFDeriv ℝ k f) (a u₀) v) u₀ := hd.comp_hasDerivAt u₀ (ha u₀)
    have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) F
      (fun _ : Fin k => v)).hasFDerivAt.comp_hasDerivAt u₀ h1
    rw [iteratedFDeriv_succ_apply_left]
    exact h2.deriv

/-- The vertical slice of a map on `X × ℝ`: its `k`-th derivative in the last variable is the
`k`-th Fréchet derivative applied to the vertical direction `(0, 1)`. -/
theorem slice_iteratedDeriv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (G : X × ℝ → F) (y : X) (h : ℝ) {n k : ℕ} (hk : k ≤ n)
    (hG : ContDiffAt ℝ n G (y, h)) :
    iteratedDeriv k (fun u : ℝ => G (y, u)) h =
      iteratedFDeriv ℝ k G (y, h) (fun _ : Fin k => ((0 : X), (1 : ℝ))) :=
  iteratedDeriv_comp_line (a := fun u : ℝ => (y, u))
    (fun u => HasDerivAt.prodMk (hasDerivAt_const u y) (hasDerivAt_id' u)) k hk h hG

/-- **The fourth-order slice identity**, from local `C⁴` regularity at `(y, h)` only. -/
theorem slice_fourth_identity (G : (ℝ × ℝ) × ℝ → ℝ) (y : ℝ × ℝ) (h : ℝ)
    (hG : ContDiffAt ℝ 4 G (y, h)) :
    iteratedDeriv 4 (fun u : ℝ => G (y, u)) h =
      iteratedFDeriv ℝ 4 G (y, h) (fun _ : Fin 4 => ((0 : ℝ × ℝ), (1 : ℝ))) :=
  slice_iteratedDeriv G y h (n := 4) (k := 4) le_rfl (by exact_mod_cast hG)

/-- Second-order version, for matching the `h²` coefficient. -/
theorem slice_second_identity (G : (ℝ × ℝ) × ℝ → ℝ) (y : ℝ × ℝ) (h : ℝ)
    (hG : ContDiffAt ℝ 4 G (y, h)) :
    iteratedDeriv 2 (fun u : ℝ => G (y, u)) h =
      iteratedFDeriv ℝ 2 G (y, h) (fun _ : Fin 2 => ((0 : ℝ × ℝ), (1 : ℝ))) :=
  slice_iteratedDeriv G y h (n := 4) (k := 2) (by norm_num) (by exact_mod_cast hG)

/-- The slice is `C⁴` near `h` as a function of one variable, so one-variable Taylor theorems
apply to it. -/
theorem slice_contDiffAt (G : (ℝ × ℝ) × ℝ → ℝ) (y : ℝ × ℝ) (h : ℝ)
    (hG : ContDiffAt ℝ 4 G (y, h)) :
    ContDiffAt ℝ 4 (fun u : ℝ => G (y, u)) h :=
  ContDiffAt.comp h hG (contDiffAt_const.prodMk contDiffAt_id)

end BakerSpherical.UniformTaylor

#print axioms BakerSpherical.UniformTaylor.iteratedDeriv_comp_line
#print axioms BakerSpherical.UniformTaylor.slice_iteratedDeriv
#print axioms BakerSpherical.UniformTaylor.slice_fourth_identity
#print axioms BakerSpherical.UniformTaylor.slice_second_identity
#print axioms BakerSpherical.UniformTaylor.slice_contDiffAt
