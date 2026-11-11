import Mathlib

/-!
# Spherical N-Series v2.4 — smooth extension through h = 0 (Step 2 of Theorem 2)

This file formalizes, for one cell, the local part of Step 2 of the proof of Theorem 2:
"each difference of corners is `h` times a jointly smooth vector function", the resulting
`h^2` factorization of the paired chordal area, its evenness in `h`, its value at `h = 0`,
and its smoothness near `h = 0` at regular points.

## Part 1: normalized chords

For `F : H → E` between real normed spaces, a base point `y`, a direction `v` and a signed
step `h`, the *normalized chord*

  `chordQuot F v y h = ∫ τ in -1/2..1/2, (fderiv ℝ F (y + (τ * h) • v)) v`

is defined by an integral, so it makes sense at `h = 0`.

* `chordQuot_zero`        : its value at `h = 0` is the directional derivative;
* `central_difference`    : `F (y + (h/2)•v) - F (y - (h/2)•v) = h • chordQuot F v y h`;
* `chordQuot_eq_inv_smul` : for `h ≠ 0` it is the usual central difference quotient;
* `chordQuot_neg`         : it is even in `h`;
* `chordQuot_contDiff`    : it is `C^n` jointly in `(y, h)` when `F` is `C^(n+1)`;
* `chordQuot_continuous`, `chordQuot_contDiff_infty` : the cases `n = 0` and `n = ∞`;
* `edge_s`, `edge_diag`, `edge_t` and their `_contDiff` versions: the three corner
  differences of a cell centred at `(s, t)`.

## Part 2: the normalized paired area

`B : E →L[ℝ] E →L[ℝ] G` is a continuous bilinear map standing for the cross product; only
bilinearity and `B u u = 0` are used, and `G` is a real inner product space.

* `pairedArea_eq`       : `pairedArea = h^2 * normArea` for every real `h`;
* `pairedArea_neg`, `normArea_neg` : both are even in `h`;
* `normArea_zero`       : `normArea` at `h = 0` equals `‖B F_s F_t‖`;
* `w1_contDiff`, `w2_contDiff` : the normalized products are `C^n` across `h = 0`;
* `normArea_contDiffAt` : `normArea` is `C^n` at `((s, t), 0)` wherever `B F_s F_t ≠ 0`.

## Scope: what is NOT proved here

* `B` is abstract. The cross product on Euclidean 3-space has not been plugged in.
* Regularity is pointwise at `h = 0`. No neighbourhood size, no bound uniform over the
  parameter square, and nothing uniform in a displacement parameter.
* No Taylor expansion or remainder estimate, no identification of the `h^2` coefficient
  `q₂`, and no midpoint (Euler--Maclaurin) summation.

So this is the local regularity input to Theorem 2, not Theorem 2.

## Compile status (November 10, 2026)

Compiled with exit code 0, 36 theorems, no errors, no warnings and no `sorry`, under Lean
v4.36.0-rc2 with Mathlib master of that date, using the imports
`Mathlib.Analysis.Calculus.ParametricIntervalIntegral`,
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`,
`Mathlib.Analysis.InnerProductSpace.Calculus`, `Mathlib.Tactic.Ring`,
`Mathlib.Tactic.NormNum`, `Mathlib.Tactic.Abel` in place of `import Mathlib`.
It has NOT been compiled against the full `import Mathlib` in that run; a few proofs end in
`simp`, whose behaviour can depend on the imported lemma set. Check with
`lake env lean NormalizedChordSmoothExtension.lean` in a Mathlib project.
-/

open MeasureTheory intervalIntegral

namespace BakerSpherical.SmoothExtension

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The normalized chord of `F` at `y` in direction `v` with signed step `h`,
defined by an integral so that it is meaningful at `h = 0`. -/
noncomputable def chordQuot (F : H → E) (v y : H) (h : ℝ) : E :=
  ∫ τ in (-(1 / 2 : ℝ))..(1 / 2), fderiv ℝ F (y + (τ * h) • v) v

/-- At `h = 0` the normalized chord is the directional derivative. -/
theorem chordQuot_zero (F : H → E) (v y : H) :
    chordQuot F v y 0 = fderiv ℝ F y v := by
  simp only [chordQuot, mul_zero, zero_smul, add_zero, intervalIntegral.integral_const]
  norm_num

omit [CompleteSpace E] in
/-- Derivative of `F` along the affine path `τ ↦ y + (τ * h) • v`. -/
theorem hasDerivAt_path (F : H → E) (hF : Differentiable ℝ F) (v y : H) (h τ : ℝ) :
    HasDerivAt (fun τ : ℝ => F (y + (τ * h) • v))
      (h • fderiv ℝ F (y + (τ * h) • v) v) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => τ * h) h τ := by
    simpa using (hasDerivAt_id τ).mul_const h
  have hpath : HasDerivAt (fun τ : ℝ => y + (τ * h) • v) (h • v) τ :=
    (h1.smul_const v).const_add y
  have hcomp := (hF (y + (τ * h) • v)).hasFDerivAt.comp_hasDerivAt τ hpath
  simpa [Function.comp_def] using hcomp

/-- The central difference is exactly `h` times the normalized chord (all real `h`). -/
theorem central_difference (F : H → E) (hF : ContDiff ℝ 1 F) (v y : H) (h : ℝ) :
    F (y + (h / 2) • v) - F (y - (h / 2) • v) = h • chordQuot F v y h := by
  have hd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hcont : Continuous (fun τ : ℝ => h • fderiv ℝ F (y + (τ * h) • v) v) := by
    have h1 : Continuous (fun τ : ℝ => fderiv ℝ F (y + (τ * h) • v)) :=
      (hF.continuous_fderiv one_ne_zero).comp (by fun_prop)
    exact (h1.clm_apply continuous_const).const_smul h
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ : ℝ => F (y + (τ * h) • v))
    (f' := fun τ : ℝ => h • fderiv ℝ F (y + (τ * h) • v) v)
    (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (fun τ _ => hasDerivAt_path F hd v y h τ) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_smul] at key
  have e1 : y + ((1 / 2 : ℝ) * h) • v = y + (h / 2) • v := by
    congr 2; ring
  have e2 : y + (-(1 / 2 : ℝ) * h) • v = y - (h / 2) • v := by
    rw [show (-(1 / 2 : ℝ) * h) = -(h / 2) by ring, neg_smul, sub_eq_add_neg]
  rw [e1, e2] at key
  exact key.symm

/-- For `h ≠ 0` the normalized chord is the ordinary central difference quotient. -/
theorem chordQuot_eq_inv_smul (F : H → E) (hF : ContDiff ℝ 1 F) (v y : H) {h : ℝ}
    (hh : h ≠ 0) :
    chordQuot F v y h = h⁻¹ • (F (y + (h / 2) • v) - F (y - (h / 2) • v)) := by
  rw [central_difference F hF v y h, smul_smul, inv_mul_cancel₀ hh, one_smul]

omit [CompleteSpace E] in
/-- The normalized chord is even in the signed step. -/
theorem chordQuot_neg (F : H → E) (v y : H) (h : ℝ) :
    chordQuot F v y (-h) = chordQuot F v y h := by
  unfold chordQuot
  have key := intervalIntegral.integral_comp_neg (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (fun τ : ℝ => fderiv ℝ F (y + (τ * h) • v) v)
  simpa [neg_mul, mul_neg] using key

omit [CompleteSpace E] in
/-- Joint smoothness: if `F` is `C^(n+1)` then `(y, h) ↦ chordQuot F v y h` is `C^n`,
including across `h = 0`. -/
theorem chordQuot_contDiff (F : H → E) (v : H) {n : ℕ∞}
    (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun p : H × ℝ => chordQuot F v p.1 p.2) := by
  have hfd : ContDiff ℝ n (fderiv ℝ F) := hF.fderiv_right le_rfl
  have hpath : ContDiff ℝ n
      (fun q : (H × ℝ) × ℝ => q.1.1 + (q.2 * q.1.2) • v) := by fun_prop
  have hf : ContDiff ℝ n
      (fun q : (H × ℝ) × ℝ => fderiv ℝ F (q.1.1 + (q.2 * q.1.2) • v) v) :=
    (hfd.comp hpath).clm_apply contDiff_const
  exact hf.parametric_intervalIntegral

omit [CompleteSpace E] in
/-- Joint continuity for a `C^1` map. -/
theorem chordQuot_continuous (F : H → E) (v : H) (hF : ContDiff ℝ 1 F) :
    Continuous (fun p : H × ℝ => chordQuot F v p.1 p.2) := by
  have h := chordQuot_contDiff F v (n := 0) (by simpa using hF)
  exact h.continuous

omit [CompleteSpace E] in
/-- Joint `C^∞` smoothness for a `C^∞` map. -/
theorem chordQuot_contDiff_infty (F : H → E) (v : H) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : H × ℝ => chordQuot F v p.1 p.2) :=
  chordQuot_contDiff F v (n := ⊤) (hF.of_le (by simp))

section Cell

/-! ### The three corner differences of a cell centred at `(s, t)`

With `p_ab = F (s ± h/2, t ± h/2)`, the two chordal triangles of the paper use the
differences `p10 - p00`, `p11 - p00` and `p01 - p00`. Each is `h` times a normalized chord. -/

variable (F : ℝ × ℝ → E)

/-- `p10 - p00 = h • (normalized chord in the s-direction)`. -/
theorem edge_s (hF : ContDiff ℝ 1 F) (s t h : ℝ) :
    F (s + h / 2, t - h / 2) - F (s - h / 2, t - h / 2) =
      h • chordQuot F (1, 0) (s, t - h / 2) h := by
  have key := central_difference F hF (1, 0) (s, t - h / 2) h
  simpa using key

/-- `p11 - p00 = h • (normalized chord along the diagonal)`. -/
theorem edge_diag (hF : ContDiff ℝ 1 F) (s t h : ℝ) :
    F (s + h / 2, t + h / 2) - F (s - h / 2, t - h / 2) =
      h • chordQuot F (1, 1) (s, t) h := by
  have key := central_difference F hF (1, 1) (s, t) h
  simpa using key

/-- `p01 - p00 = h • (normalized chord in the t-direction)`. -/
theorem edge_t (hF : ContDiff ℝ 1 F) (s t h : ℝ) :
    F (s - h / 2, t + h / 2) - F (s - h / 2, t - h / 2) =
      h • chordQuot F (0, 1) (s - h / 2, t) h := by
  have key := central_difference F hF (0, 1) (s - h / 2, t) h
  simpa using key

omit [CompleteSpace E] in
/-- The normalized s-edge is `C^n` in `(s, t, h)` jointly, across `h = 0`. -/
theorem edge_s_contDiff {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ =>
      chordQuot F (1, 0) (p.1.1, p.1.2 - p.2 / 2) p.2) := by
  have hg : ContDiff ℝ n
      (fun p : (ℝ × ℝ) × ℝ => (((p.1.1, p.1.2 - p.2 / 2) : ℝ × ℝ), p.2)) := by fun_prop
  have key : ContDiff ℝ n ((fun q : (ℝ × ℝ) × ℝ => chordQuot F (1, 0) q.1 q.2) ∘
      (fun p : (ℝ × ℝ) × ℝ => (((p.1.1, p.1.2 - p.2 / 2) : ℝ × ℝ), p.2))) :=
    (chordQuot_contDiff F (1, 0) hF).comp hg
  exact key

omit [CompleteSpace E] in
/-- The normalized diagonal is `C^n` in `(s, t, h)` jointly, across `h = 0`. -/
theorem edge_diag_contDiff {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ => chordQuot F (1, 1) p.1 p.2) :=
  chordQuot_contDiff F (1, 1) hF

omit [CompleteSpace E] in
/-- The normalized t-edge is `C^n` in `(s, t, h)` jointly, across `h = 0`. -/
theorem edge_t_contDiff {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ =>
      chordQuot F (0, 1) (p.1.1 - p.2 / 2, p.1.2) p.2) := by
  have hg : ContDiff ℝ n
      (fun p : (ℝ × ℝ) × ℝ => (((p.1.1 - p.2 / 2, p.1.2) : ℝ × ℝ), p.2)) := by fun_prop
  have key : ContDiff ℝ n ((fun q : (ℝ × ℝ) × ℝ => chordQuot F (0, 1) q.1 q.2) ∘
      (fun p : (ℝ × ℝ) × ℝ => (((p.1.1 - p.2 / 2, p.1.2) : ℝ × ℝ), p.2))) :=
    (chordQuot_contDiff F (0, 1) hF).comp hg
  exact key

/-- At `h = 0` the normalized edges are the partial derivatives `F_s`, `F_s + F_t`, `F_t`
(as directional derivatives of `F` at the cell centre). -/
theorem edges_at_zero (s t : ℝ) :
    chordQuot F (1, 0) (s, t - (0 : ℝ) / 2) 0 = fderiv ℝ F (s, t) (1, 0) ∧
    chordQuot F (1, 1) (s, t) 0 = fderiv ℝ F (s, t) (1, 1) ∧
    chordQuot F (0, 1) (s - (0 : ℝ) / 2, t) 0 = fderiv ℝ F (s, t) (0, 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [chordQuot_zero]

end Cell

section Area

/-! ### The normalized paired area near `h = 0`

`B` is a continuous bilinear map standing for the cross product (the cross product on
Euclidean 3-space is one instance; only bilinearity and `B u u = 0` are used). With corners
`p_ab = F (s ± h/2, t ± h/2)`, the paired chordal "area" is

  `pairedArea = (‖B (p10 - p00) (p11 - p00)‖ + ‖B (p11 - p00) (p01 - p00)‖) / 2`.

We show `pairedArea = h^2 * normArea`, where `normArea` is built from normalized chords and
is therefore defined at `h = 0`; that `normArea` is even in `h`; that its value at `h = 0` is
`‖B F_s F_t‖`; and that it is `C^n` near `h = 0` wherever `B F_s F_t ≠ 0`. -/

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable (B : E →L[ℝ] E →L[ℝ] G) (F : ℝ × ℝ → E)

/-- Normalized `p10 - p00`, as a function of `((s, t), h)`. -/
noncomputable def eS (p : (ℝ × ℝ) × ℝ) : E :=
  chordQuot F (1, 0) (p.1.1, p.1.2 - p.2 / 2) p.2

/-- Normalized `p11 - p00`. -/
noncomputable def eD (p : (ℝ × ℝ) × ℝ) : E := chordQuot F (1, 1) p.1 p.2

/-- Normalized `p01 - p00`. -/
noncomputable def eT (p : (ℝ × ℝ) × ℝ) : E :=
  chordQuot F (0, 1) (p.1.1 - p.2 / 2, p.1.2) p.2

/-- Normalized product for the first triangle. -/
noncomputable def w1 (p : (ℝ × ℝ) × ℝ) : G := B (eS F p) (eD F p)

/-- Normalized product for the second triangle. -/
noncomputable def w2 (p : (ℝ × ℝ) × ℝ) : G := B (eD F p) (eT F p)

/-- The normalized paired area; defined for every `h`, including `h = 0`. -/
noncomputable def normArea (p : (ℝ × ℝ) × ℝ) : ℝ := (‖w1 B F p‖ + ‖w2 B F p‖) / 2

/-- Cell corners. -/
noncomputable def p00 (s t h : ℝ) : E := F (s - h / 2, t - h / 2)
noncomputable def p10 (s t h : ℝ) : E := F (s + h / 2, t - h / 2)
noncomputable def p11 (s t h : ℝ) : E := F (s + h / 2, t + h / 2)
noncomputable def p01 (s t h : ℝ) : E := F (s - h / 2, t + h / 2)

/-- The paired chordal area of the cell, with `B` in place of the cross product. -/
noncomputable def pairedArea (s t h : ℝ) : ℝ :=
  (‖B (p10 F s t h - p00 F s t h) (p11 F s t h - p00 F s t h)‖ +
    ‖B (p11 F s t h - p00 F s t h) (p01 F s t h - p00 F s t h)‖) / 2

omit [CompleteSpace E] in
theorem smul_smul_apply (a b : E) (h : ℝ) : B (h • a) (h • b) = h ^ 2 • B a b := by
  simp [smul_smul, sq]

theorem cross_first (hF : ContDiff ℝ 1 F) (s t h : ℝ) :
    B (p10 F s t h - p00 F s t h) (p11 F s t h - p00 F s t h) =
      h ^ 2 • w1 B F ((s, t), h) := by
  simp only [p10, p00, p11, w1, eS, eD]
  rw [edge_s F hF, edge_diag F hF, smul_smul_apply]

theorem cross_second (hF : ContDiff ℝ 1 F) (s t h : ℝ) :
    B (p11 F s t h - p00 F s t h) (p01 F s t h - p00 F s t h) =
      h ^ 2 • w2 B F ((s, t), h) := by
  simp only [p11, p00, p01, w2, eD, eT]
  rw [edge_diag F hF, edge_t F hF, smul_smul_apply]

/-- Exact `h^2` factorization of the paired area, valid for every real `h`. -/
theorem pairedArea_eq (hF : ContDiff ℝ 1 F) (s t h : ℝ) :
    pairedArea B F s t h = h ^ 2 * normArea B F ((s, t), h) := by
  unfold pairedArea normArea
  rw [cross_first B F hF, cross_second B F hF, norm_smul, norm_smul,
    Real.norm_of_nonneg (sq_nonneg h)]
  ring

omit [CompleteSpace E] in
theorem eS_contDiff {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (eS F) :=
  show ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ =>
    chordQuot F (1, 0) (p.1.1, p.1.2 - p.2 / 2) p.2) from edge_s_contDiff F hF

omit [CompleteSpace E] in
theorem eD_contDiff {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (eD F) :=
  show ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ => chordQuot F (1, 1) p.1 p.2) from
    edge_diag_contDiff F hF

omit [CompleteSpace E] in
theorem eT_contDiff {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (eT F) :=
  show ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ =>
    chordQuot F (0, 1) (p.1.1 - p.2 / 2, p.1.2) p.2) from edge_t_contDiff F hF

omit [CompleteSpace E] in
/-- The normalized products are `C^n` jointly in `(s, t, h)`, across `h = 0`. -/
theorem w1_contDiff {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (w1 B F) := by
  have h1 : ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ => B (eS F p)) :=
    B.contDiff.comp (eS_contDiff F hF)
  exact h1.clm_apply (eD_contDiff F hF)

omit [CompleteSpace E] in
theorem w2_contDiff {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (w2 B F) := by
  have h1 : ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ => B (eD F p)) :=
    B.contDiff.comp (eD_contDiff F hF)
  exact h1.clm_apply (eT_contDiff F hF)

theorem eS_zero (s t : ℝ) : eS F ((s, t), 0) = fderiv ℝ F (s, t) (1, 0) := by
  simp [eS, chordQuot_zero]

theorem eD_zero (s t : ℝ) : eD F ((s, t), 0) = fderiv ℝ F (s, t) (1, 1) := by
  simp [eD, chordQuot_zero]

theorem eT_zero (s t : ℝ) : eT F ((s, t), 0) = fderiv ℝ F (s, t) (0, 1) := by
  simp [eT, chordQuot_zero]

omit [CompleteSpace E] in
theorem fderiv_diag (s t : ℝ) :
    fderiv ℝ F (s, t) (1, 1) = fderiv ℝ F (s, t) (1, 0) + fderiv ℝ F (s, t) (0, 1) := by
  rw [← map_add]
  simp

omit [CompleteSpace E] in
/-- An alternating bilinear map is antisymmetric. -/
theorem anti (hB : ∀ u, B u u = 0) (u v : E) : B u v = -B v u := by
  have h := hB (u + v)
  rw [B.map_add₂, map_add, map_add, hB u, hB v, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- At `h = 0` both normalized products equal `B F_s F_t`. -/
theorem w1_zero (hB : ∀ u, B u u = 0) (s t : ℝ) :
    w1 B F ((s, t), 0) = B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) := by
  simp only [w1, eS_zero, eD_zero, fderiv_diag, map_add, hB, zero_add]

theorem w2_zero (hB : ∀ u, B u u = 0) (s t : ℝ) :
    w2 B F ((s, t), 0) = B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) := by
  simp only [w2, eD_zero, eT_zero, fderiv_diag, ContinuousLinearMap.map_add₂, hB, add_zero]

/-- The leading coefficient: `normArea` at `h = 0` is `‖B F_s F_t‖`. -/
theorem normArea_zero (hB : ∀ u, B u u = 0) (s t : ℝ) :
    normArea B F ((s, t), 0) =
      ‖B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1))‖ := by
  simp only [normArea, w1_zero B F hB, w2_zero B F hB]
  ring

/-- Regularity: at a point where `B F_s F_t ≠ 0`, the normalized paired area is `C^n`
jointly in `(s, t, h)` at `h = 0`. -/
theorem normArea_contDiffAt {n : ℕ∞} (hF : ContDiff ℝ (n + 1) F)
    (hB : ∀ u, B u u = 0) (s t : ℝ)
    (hreg : B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) ≠ 0) :
    ContDiffAt ℝ n (normArea B F) ((s, t), 0) := by
  have h1 : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × ℝ => ‖w1 B F p‖) ((s, t), 0) :=
    (w1_contDiff B F hF).contDiffAt.norm ℝ (by rw [w1_zero B F hB]; exact hreg)
  have h2 : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × ℝ => ‖w2 B F p‖) ((s, t), 0) :=
    (w2_contDiff B F hF).contDiffAt.norm ℝ (by rw [w2_zero B F hB]; exact hreg)
  exact (h1.add h2).div_const 2

omit [CompleteSpace E] in
/-- Cyclic invariance of the triangle product for an alternating bilinear map. -/
theorem tri_cyclic (hB : ∀ u, B u u = 0) (a b c : E) :
    B (c - b) (a - b) = B (b - a) (c - a) := by
  rw [B.map_sub₂, B.map_sub₂, map_sub, map_sub, map_sub, map_sub, hB b, hB a,
    anti B hB c a, anti B hB c b]
  abel

omit [CompleteSpace E] in
/-- Reversing the signed cell size exchanges the two triangles: the paired area is even. -/
theorem pairedArea_neg (hB : ∀ u, B u u = 0) (s t h : ℝ) :
    pairedArea B F s t (-h) = pairedArea B F s t h := by
  have e00 : p00 F s t (-h) = p11 F s t h := by
    simp only [p00, p11]; congr 2 <;> ring
  have e10 : p10 F s t (-h) = p01 F s t h := by
    simp only [p10, p01]; congr 2 <;> ring
  have e11 : p11 F s t (-h) = p00 F s t h := by
    simp only [p11, p00]; congr 2 <;> ring
  have e01 : p01 F s t (-h) = p10 F s t h := by
    simp only [p01, p10]; congr 2 <;> ring
  unfold pairedArea
  rw [e00, e10, e11, e01]
  rw [tri_cyclic B hB (p00 F s t h) (p11 F s t h) (p01 F s t h),
    tri_cyclic B hB (p10 F s t h) (p11 F s t h) (p00 F s t h),
    tri_cyclic B hB (p00 F s t h) (p10 F s t h) (p11 F s t h)]
  ring

/-- The normalized paired area is even in `h` (including at `h = 0`). -/
theorem normArea_neg (hF : ContDiff ℝ 1 F) (hB : ∀ u, B u u = 0) (s t h : ℝ) :
    normArea B F ((s, t), -h) = normArea B F ((s, t), h) := by
  by_cases hh : h = 0
  · subst hh; simp
  · have h1 := pairedArea_eq B F hF s t h
    have h2 := pairedArea_eq B F hF s t (-h)
    rw [pairedArea_neg B F hB, h1, neg_sq] at h2
    exact (mul_left_cancel₀ (pow_ne_zero 2 hh) h2).symm

end Area

#print axioms BakerSpherical.SmoothExtension.chordQuot_zero
#print axioms BakerSpherical.SmoothExtension.hasDerivAt_path
#print axioms BakerSpherical.SmoothExtension.central_difference
#print axioms BakerSpherical.SmoothExtension.chordQuot_eq_inv_smul
#print axioms BakerSpherical.SmoothExtension.chordQuot_neg
#print axioms BakerSpherical.SmoothExtension.chordQuot_contDiff
#print axioms BakerSpherical.SmoothExtension.chordQuot_continuous
#print axioms BakerSpherical.SmoothExtension.chordQuot_contDiff_infty
#print axioms BakerSpherical.SmoothExtension.edge_s
#print axioms BakerSpherical.SmoothExtension.edge_diag
#print axioms BakerSpherical.SmoothExtension.edge_t
#print axioms BakerSpherical.SmoothExtension.edge_s_contDiff
#print axioms BakerSpherical.SmoothExtension.edge_diag_contDiff
#print axioms BakerSpherical.SmoothExtension.edge_t_contDiff
#print axioms BakerSpherical.SmoothExtension.edges_at_zero
#print axioms BakerSpherical.SmoothExtension.smul_smul_apply
#print axioms BakerSpherical.SmoothExtension.cross_first
#print axioms BakerSpherical.SmoothExtension.cross_second
#print axioms BakerSpherical.SmoothExtension.pairedArea_eq
#print axioms BakerSpherical.SmoothExtension.w1_contDiff
#print axioms BakerSpherical.SmoothExtension.w2_contDiff
#print axioms BakerSpherical.SmoothExtension.w1_zero
#print axioms BakerSpherical.SmoothExtension.w2_zero
#print axioms BakerSpherical.SmoothExtension.normArea_zero
#print axioms BakerSpherical.SmoothExtension.normArea_contDiffAt
#print axioms BakerSpherical.SmoothExtension.tri_cyclic
#print axioms BakerSpherical.SmoothExtension.pairedArea_neg
#print axioms BakerSpherical.SmoothExtension.normArea_neg

#print axioms BakerSpherical.SmoothExtension.eS_contDiff
#print axioms BakerSpherical.SmoothExtension.eD_contDiff
#print axioms BakerSpherical.SmoothExtension.eT_contDiff
#print axioms BakerSpherical.SmoothExtension.eS_zero
#print axioms BakerSpherical.SmoothExtension.eD_zero
#print axioms BakerSpherical.SmoothExtension.eT_zero
#print axioms BakerSpherical.SmoothExtension.fderiv_diag
#print axioms BakerSpherical.SmoothExtension.anti
end BakerSpherical.SmoothExtension
