import Mathlib
import SphericalQ2Coefficient

/-!
# Spherical N-Series v2.4 — identifying `Fst`, `DP3`, `DM3` with partial derivatives

`SphericalQ2Coefficient.lean` defines `Fst`, `DP3`, `DM3` through the two diagonal curves
through the cell centre. This file identifies them with iterated partial derivatives of `F`.

Notation: `dirD v G` is the directional derivative `p ↦ DG(p)·v`; `(1, 0)` is the
`s`-direction and `(0, 1)` the `t`-direction. With

  `F_st  = ∂s ∂t F`,  `F_sss = ∂s ∂s ∂s F`,  `F_sst = ∂s ∂s ∂t F`,
  `F_stt = ∂s ∂t ∂t F`,  `F_ttt = ∂t ∂t ∂t F`

the results are

* `dirD_comm`  : directional derivatives of a `C²` map commute;
* `Fst_eq`     : `Fst = F_st`                                   (`F` of class `C²`);
* `DP3_eq`     : `DP3 = F_sss + 3 F_sst + 3 F_stt + F_ttt`       (`F` of class `C³`);
* `DM3_eq`     : `DM3 = F_sss - 3 F_sst + 3 F_stt - F_ttt`       (`F` of class `C³`).

These match `dplus` and `dminus` of `Lemma2Algebra.lean`.
-/

namespace BakerSpherical.Q2

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Directional derivative of `G` in the direction `v`, as a function of the base point. -/
noncomputable def dirD (v : ℝ × ℝ) (G : ℝ × ℝ → E) : ℝ × ℝ → E := fun p => fderiv ℝ G p v

theorem dirD_cd2 {G : ℝ × ℝ → E} (hG : ContDiff ℝ 3 G) (v : ℝ × ℝ) :
    ContDiff ℝ 2 (dirD v G) :=
  (hG.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

theorem dirD_cd1 {G : ℝ × ℝ → E} (hG : ContDiff ℝ 2 G) (v : ℝ × ℝ) :
    ContDiff ℝ 1 (dirD v G) :=
  (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem dirD_diff {G : ℝ × ℝ → E} (hG : ContDiff ℝ 2 G) (v : ℝ × ℝ) :
    Differentiable ℝ (dirD v G) :=
  (dirD_cd1 hG v).differentiable (by norm_num)

theorem dirD_add_dir (a b : ℝ × ℝ) (G : ℝ × ℝ → E) :
    dirD (a + b) G = fun p => dirD a G p + dirD b G p := by
  funext p; simp [dirD]

theorem dirD_neg_dir (b : ℝ × ℝ) (G : ℝ × ℝ → E) :
    dirD (-b) G = fun p => -dirD b G p := by
  funext p; simp [dirD]

theorem dirD_neg_fun (v : ℝ × ℝ) (G : ℝ × ℝ → E) :
    dirD v (fun p => -G p) = fun p => -dirD v G p := by
  funext p
  show fderiv ℝ (-G) p v = -(fderiv ℝ G p v)
  rw [fderiv_neg]; rfl

theorem dirD_add_fun {A B : ℝ × ℝ → E} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (v : ℝ × ℝ) : dirD v (fun p => A p + B p) = fun p => dirD v A p + dirD v B p := by
  funext p
  have : (fun p => A p + B p) = A + B := rfl
  simp [dirD, this, fderiv_add (hA p) (hB p)]

/-- Directional derivatives of a `C²` map commute. -/
theorem dirD_comm {G : ℝ × ℝ → E} (hG : ContDiff ℝ 2 G) (a b : ℝ × ℝ) :
    dirD a (dirD b G) = dirD b (dirD a G) := by
  have key : ∀ (u w : ℝ × ℝ) (p : ℝ × ℝ),
      dirD u (dirD w G) p = fderiv ℝ (fderiv ℝ G) p u w := by
    intro u w p
    have h2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) p) p :=
      ((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) p).hasFDerivAt
    have h3 := h2.clm_apply (hasFDerivAt_const w p)
    show fderiv ℝ (fun q => fderiv ℝ G q w) p u = _
    rw [h3.fderiv]; simp
  funext p
  rw [key, key]
  exact (hG.contDiffAt.isSymmSndFDerivAt (by simp)).eq a b

/-- Expansion of the second derivative in direction `a + b` (no commutation used). -/
theorem dirD2_expand {G : ℝ × ℝ → E} (hG : ContDiff ℝ 2 G) (a b : ℝ × ℝ) :
    dirD (a + b) (dirD (a + b) G) = fun p =>
      (dirD a (dirD a G) p + dirD a (dirD b G) p) +
        (dirD b (dirD a G) p + dirD b (dirD b G) p) := by
  rw [dirD_add_dir a b G, dirD_add_dir a b,
    dirD_add_fun (dirD_diff hG a) (dirD_diff hG b) a,
    dirD_add_fun (dirD_diff hG a) (dirD_diff hG b) b]

theorem dirD_add4 {A B C D : ℝ × ℝ → E} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hC : Differentiable ℝ C) (hD : Differentiable ℝ D) (v : ℝ × ℝ) :
    dirD v (fun p => (A p + B p) + (C p + D p)) =
      fun p => (dirD v A p + dirD v B p) + (dirD v C p + dirD v D p) := by
  rw [dirD_add_fun (A := fun p => A p + B p) (B := fun p => C p + D p) (hA.add hB) (hC.add hD),
    dirD_add_fun hA hB, dirD_add_fun hC hD]

/-- Expansion of the third derivative in direction `a + b` (no commutation used). -/
theorem dirD3_expand {G : ℝ × ℝ → E} (hG : ContDiff ℝ 3 G) (a b : ℝ × ℝ) :
    dirD (a + b) (dirD (a + b) (dirD (a + b) G)) = fun p =>
      ((dirD a (dirD a (dirD a G)) p + dirD a (dirD a (dirD b G)) p) +
          (dirD a (dirD b (dirD a G)) p + dirD a (dirD b (dirD b G)) p)) +
        ((dirD b (dirD a (dirD a G)) p + dirD b (dirD a (dirD b G)) p) +
          (dirD b (dirD b (dirD a G)) p + dirD b (dirD b (dirD b G)) p)) := by
  have hG2 : ContDiff ℝ 2 G := hG.of_le (by norm_num)
  have haa := dirD_diff (dirD_cd2 hG a) a
  have hab := dirD_diff (dirD_cd2 hG b) a
  have hba := dirD_diff (dirD_cd2 hG a) b
  have hbb := dirD_diff (dirD_cd2 hG b) b
  rw [dirD2_expand hG2 a b, dirD_add_dir a b, dirD_add4 haa hab hba hbb a,
    dirD_add4 haa hab hba hbb b]

/-- Derivative of `G` along a line is the directional derivative. -/
theorem deriv_line {G : ℝ × ℝ → E} (hG : Differentiable ℝ G) (p v : ℝ × ℝ) :
    deriv (fun x : ℝ => G (p + x • v)) = fun x => dirD v G (p + x • v) := by
  funext x
  have hl : HasDerivAt (fun x : ℝ => p + x • v) v x := by
    simpa using ((hasDerivAt_id' x).smul_const v).const_add p
  exact ((hG _).hasFDerivAt.comp_hasDerivAt x hl).deriv

theorem line_d2 {G : ℝ × ℝ → E} (hG : ContDiff ℝ 2 G) (p v : ℝ × ℝ) :
    deriv (deriv (fun x : ℝ => G (p + x • v))) 0 = dirD v (dirD v G) p := by
  rw [deriv_line (hG.differentiable (by norm_num)), deriv_line (dirD_diff hG v)]
  simp

theorem line_d3 {G : ℝ × ℝ → E} (hG : ContDiff ℝ 3 G) (p v : ℝ × ℝ) :
    deriv (deriv (deriv (fun x : ℝ => G (p + x • v)))) 0 = dirD v (dirD v (dirD v G)) p := by
  rw [deriv_line (hG.differentiable (by norm_num)),
    deriv_line (dirD_diff (hG.of_le (by norm_num)) v),
    deriv_line (dirD_diff (dirD_cd2 hG v) v)]
  simp

variable (F : ℝ × ℝ → E) (s t : ℝ)

theorem diag_eq : ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) := by ext <;> simp

theorem antidiag_eq : ((1 : ℝ), (-1 : ℝ)) = (1, 0) + -(0, 1) := by ext <;> simp

/-- `Fst` is the mixed partial derivative `∂s ∂t F`. -/
theorem Fst_eq (hF : ContDiff ℝ 2 F) :
    Fst F s t = dirD (1, 0) (dirD (0, 1) F) (s, t) := by
  have eP : gP F s t = fun x : ℝ => F ((s, t) + x • ((1 : ℝ), (1 : ℝ))) := rfl
  have eM : gM F s t = fun x : ℝ => F ((s, t) + x • ((1 : ℝ), (-1 : ℝ))) := rfl
  rw [Fst, eP, eM, line_d2 hF, line_d2 hF, diag_eq, antidiag_eq, dirD2_expand hF,
    dirD2_expand hF]
  simp only [dirD_neg_dir, dirD_neg_fun, neg_neg, dirD_comm hF (0, 1) (1, 0)]
  module

/-- `DP3 = F_sss + 3 F_sst + 3 F_stt + F_ttt`. -/
theorem DP3_eq (hF : ContDiff ℝ 3 F) :
    DP3 F s t =
      dirD (1, 0) (dirD (1, 0) (dirD (1, 0) F)) (s, t) +
        (3 : ℝ) • dirD (1, 0) (dirD (1, 0) (dirD (0, 1) F)) (s, t) +
        (3 : ℝ) • dirD (1, 0) (dirD (0, 1) (dirD (0, 1) F)) (s, t) +
        dirD (0, 1) (dirD (0, 1) (dirD (0, 1) F)) (s, t) := by
  have eP : gP F s t = fun x : ℝ => F ((s, t) + x • ((1 : ℝ), (1 : ℝ))) := rfl
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  rw [DP3, eP, line_d3 hF, diag_eq, dirD3_expand hF]
  simp only [dirD_comm hF2 (0, 1) (1, 0), dirD_comm (dirD_cd2 hF (1, 0)) (0, 1) (1, 0),
    dirD_comm (dirD_cd2 hF (0, 1)) (0, 1) (1, 0)]
  module

/-- `DM3 = F_sss - 3 F_sst + 3 F_stt - F_ttt`. -/
theorem DM3_eq (hF : ContDiff ℝ 3 F) :
    DM3 F s t =
      dirD (1, 0) (dirD (1, 0) (dirD (1, 0) F)) (s, t) -
        (3 : ℝ) • dirD (1, 0) (dirD (1, 0) (dirD (0, 1) F)) (s, t) +
        (3 : ℝ) • dirD (1, 0) (dirD (0, 1) (dirD (0, 1) F)) (s, t) -
        dirD (0, 1) (dirD (0, 1) (dirD (0, 1) F)) (s, t) := by
  have eM : gM F s t = fun x : ℝ => F ((s, t) + x • ((1 : ℝ), (-1 : ℝ))) := rfl
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  rw [DM3, eM, line_d3 hF, antidiag_eq, dirD3_expand hF]
  simp only [dirD_neg_dir, dirD_neg_fun, neg_neg, dirD_comm hF2 (0, 1) (1, 0),
    dirD_comm (dirD_cd2 hF (1, 0)) (0, 1) (1, 0), dirD_comm (dirD_cd2 hF (0, 1)) (0, 1) (1, 0)]
  module

end

end BakerSpherical.Q2

#print axioms BakerSpherical.Q2.dirD_comm
#print axioms BakerSpherical.Q2.dirD2_expand
#print axioms BakerSpherical.Q2.dirD3_expand
#print axioms BakerSpherical.Q2.line_d2
#print axioms BakerSpherical.Q2.line_d3
#print axioms BakerSpherical.Q2.Fst_eq
#print axioms BakerSpherical.Q2.DP3_eq
#print axioms BakerSpherical.Q2.DM3_eq
