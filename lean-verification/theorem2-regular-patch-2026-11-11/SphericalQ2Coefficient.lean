import Mathlib
import NormalizedChordSmoothExtension
import CrossProductBilinear

/-!
# Spherical N-Series v2.4 — the `h²` coefficient `q₂` of the normalized paired area

For a cell centred at `(s, t)`, this file computes the second derivative in `h`, at `h = 0`,
of `h ↦ normArea B F ((s, t), h)`, in terms of derivatives of `F` at `(s, t)`.

Everything is reduced to the two diagonal curves through the centre,

  `gP x = F ((s, t) + x • (1, 1))`,   `gM x = F ((s, t) + x • (1, -1))`,

because the three corner differences of the cell are
`gM (h/2) - gP (-h/2)`, `gP (h/2) - gP (-h/2)` and `gM (-h/2) - gP (-h/2)`.

Main results:

* `smul_id_derivs`     : if `ψ h = h • e h` then `ψ'' 0 = 2 e' 0` and `ψ''' 0 = 3 e'' 0`;
* `bilin_derivs`       : first and second derivative of `h ↦ B (a h) (b h)`;
* `norm_d2`, `half_sum_norm_d2` : second derivative of the norm of a curve;
* `cS_d1 … cT_d2`      : first and second `h`-derivatives of the three normalized chords;
* `normArea_d2`        : for an alternating `B`,
    `d²/dh² normArea B F ((s,t), h) |_{h=0} = 2 * q2Coeff …`;
* `cross_normArea_d2`  : the same for the Euclidean cross product `crossE`.

`q2Coeff N u v p q` is the `h²` coefficient of `(‖N + h u + h² p‖ + ‖N + h v + h² q‖) / 2`,
and `uVec, vVec, pVec, qVec` are the coefficient vectors `a1, a2, b1, b2` of
`Lemma2Algebra.lean`, written with `Fst`, `DP3`, `DM3`.

## Scope: what is NOT proved here

* This is a statement about the second derivative at `h = 0`. It is not a Taylor expansion
  with remainder; that is a separate file.
* `Fst` is defined as `(gP'' 0 - gM'' 0) / 4` and `DP3, DM3` as the third derivatives of the
  diagonal curves. Their identification with the mixed partial `F_st` and with
  `F_sss ± 3 F_sst + 3 F_stt ± F_ttt` (symmetry of higher derivatives) is not proved here.
* The closed form of `q₂` is in `SphericalQ2ClosedForm.lean`.
-/

namespace BakerSpherical.Q2

open BakerSpherical.SmoothExtension Filter Topology

/-! ### Part 1: one-variable calculus lemmas -/

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_deriv_of_contDiff {f : ℝ → E} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hn : n ≠ 0) (h : ℝ) : HasDerivAt f (deriv f h) h :=
  (hf.differentiable hn h).hasDerivAt

theorem contDiff_deriv_two {f : ℝ → E} (hf : ContDiff ℝ 3 f) : ContDiff ℝ 2 (deriv f) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (2 + 1) f by norm_num; exact hf)).2.2

theorem contDiff_deriv_one {f : ℝ → E} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f by norm_num; exact hf)).2.2

/-- Derivatives of `h ↦ a • g (c * h)`. -/
theorem deriv_smul_scaled (g : ℝ → E) (a c : ℝ) :
    deriv (fun h => a • g (c * h)) = fun h => (a * c) • deriv g (c * h) := by
  funext h
  rw [deriv_fun_const_smul_field, deriv_comp_mul_left, smul_smul]

theorem deriv_scaled (g : ℝ → E) (c : ℝ) :
    deriv (fun h => g (c * h)) = fun h => c • deriv g (c * h) := by
  funext h
  rw [deriv_comp_mul_left]

/-- Second and third derivatives of `h ↦ g (c * h)`. -/
theorem d2_scaled (g : ℝ → E) (c : ℝ) :
    deriv (deriv (fun h => g (c * h))) = fun h => (c * c) • deriv (deriv g) (c * h) := by
  rw [deriv_scaled, deriv_smul_scaled]

theorem d3_scaled (g : ℝ → E) (c : ℝ) :
    deriv (deriv (deriv (fun h => g (c * h)))) =
      fun h => (c * c * c) • deriv (deriv (deriv g)) (c * h) := by
  rw [d2_scaled, deriv_smul_scaled]

/-- Derivatives of a difference of two `C³` curves. -/
theorem d2_sub {a b : ℝ → E} (ha : ContDiff ℝ 3 a) (hb : ContDiff ℝ 3 b) :
    deriv (deriv (fun h => a h - b h)) = fun h => deriv (deriv a) h - deriv (deriv b) h := by
  have h1 : deriv (fun h => a h - b h) = fun h => deriv a h - deriv b h :=
    funext fun h => deriv_fun_sub (ha.differentiable (by norm_num) h)
      (hb.differentiable (by norm_num) h)
  rw [h1]
  exact funext fun h => deriv_fun_sub
    ((contDiff_deriv_two ha).differentiable (by norm_num) h)
    ((contDiff_deriv_two hb).differentiable (by norm_num) h)

theorem d3_sub {a b : ℝ → E} (ha : ContDiff ℝ 3 a) (hb : ContDiff ℝ 3 b) :
    deriv (deriv (deriv (fun h => a h - b h))) =
      fun h => deriv (deriv (deriv a)) h - deriv (deriv (deriv b)) h := by
  rw [d2_sub ha hb]
  exact funext fun h => deriv_fun_sub
    ((contDiff_deriv_one (contDiff_deriv_two ha)).differentiable (by norm_num) h)
    ((contDiff_deriv_one (contDiff_deriv_two hb)).differentiable (by norm_num) h)

/-- If `ψ h = h • e h` with `e` of class `C³`, then `ψ'' 0 = 2 e' 0` and `ψ''' 0 = 3 e'' 0`. -/
theorem smul_id_derivs {e ψ : ℝ → E} (he : ContDiff ℝ 3 e) (hψ : ∀ h, ψ h = h • e h) :
    deriv (deriv ψ) 0 = (2 : ℝ) • deriv e 0 ∧
      deriv (deriv (deriv ψ)) 0 = (3 : ℝ) • deriv (deriv e) 0 := by
  have he1 : ContDiff ℝ 2 (deriv e) := contDiff_deriv_two he
  have he2 : ContDiff ℝ 1 (deriv (deriv e)) := contDiff_deriv_one he1
  have e1 : ∀ h, HasDerivAt e (deriv e h) h := hasDerivAt_deriv_of_contDiff he (by norm_num)
  have e2 : ∀ h, HasDerivAt (deriv e) (deriv (deriv e) h) h :=
    hasDerivAt_deriv_of_contDiff he1 (by norm_num)
  have e3 : ∀ h, HasDerivAt (deriv (deriv e)) (deriv (deriv (deriv e)) h) h :=
    hasDerivAt_deriv_of_contDiff he2 (by norm_num)
  have hψ' : ψ = fun h => h • e h := funext hψ
  have s0 : ∀ h, HasDerivAt (fun h : ℝ => h • e h) (e h + h • deriv e h) h := by
    intro h
    exact ((hasDerivAt_id' h).smul (e1 h)).congr_deriv (by simp [add_comm])
  have s1 : ∀ h, HasDerivAt (fun h : ℝ => h • deriv e h)
      (deriv e h + h • deriv (deriv e) h) h := by
    intro h
    exact ((hasDerivAt_id' h).smul (e2 h)).congr_deriv (by simp [add_comm])
  have s2 : ∀ h, HasDerivAt (fun h : ℝ => h • deriv (deriv e) h)
      (deriv (deriv e) h + h • deriv (deriv (deriv e)) h) h := by
    intro h
    exact ((hasDerivAt_id' h).smul (e3 h)).congr_deriv (by simp [add_comm])
  have d1 : deriv ψ = fun h => e h + h • deriv e h := by
    rw [hψ']; exact funext fun h => (s0 h).deriv
  have d2 : deriv (deriv ψ) = fun h => deriv e h + (deriv e h + h • deriv (deriv e) h) := by
    rw [d1]; exact funext fun h => ((e1 h).add (s1 h)).deriv
  have d3 : deriv (deriv (deriv ψ)) 0 =
      deriv (deriv e) 0 + (deriv (deriv e) 0 + (deriv (deriv e) 0 +
        (0 : ℝ) • deriv (deriv (deriv e)) 0)) := by
    rw [d2]; exact ((e2 0).add ((e2 0).add (s2 0))).deriv
  constructor
  · rw [d2]; simp only [zero_smul, add_zero]; module
  · rw [d3]; module

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- First and second derivatives at `0` of `h ↦ B (a h) (b h)` for `C²` curves. -/
theorem bilin_derivs (B : E →L[ℝ] E →L[ℝ] G) {a b : ℝ → E}
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) :
    deriv (fun h => B (a h) (b h)) 0 = B (deriv a 0) (b 0) + B (a 0) (deriv b 0) ∧
      deriv (deriv (fun h => B (a h) (b h))) 0 =
        B (deriv (deriv a) 0) (b 0) + (2 : ℝ) • B (deriv a 0) (deriv b 0) +
          B (a 0) (deriv (deriv b) 0) := by
  have a1 : ∀ h, HasDerivAt a (deriv a h) h := hasDerivAt_deriv_of_contDiff ha (by norm_num)
  have b1 : ∀ h, HasDerivAt b (deriv b h) h := hasDerivAt_deriv_of_contDiff hb (by norm_num)
  have a2 : ∀ h, HasDerivAt (deriv a) (deriv (deriv a) h) h :=
    hasDerivAt_deriv_of_contDiff (contDiff_deriv_one ha) (by norm_num)
  have b2 : ∀ h, HasDerivAt (deriv b) (deriv (deriv b) h) h :=
    hasDerivAt_deriv_of_contDiff (contDiff_deriv_one hb) (by norm_num)
  have d1 : deriv (fun h => B (a h) (b h)) =
      fun h => B (a h) (deriv b h) + B (deriv a h) (b h) :=
    funext fun h => (B.hasDerivAt_of_bilinear (fun _ => a1 h) (fun _ => b1 h)).deriv
  constructor
  · rw [d1]; exact add_comm _ _
  · rw [d1]
    have key : HasDerivAt (fun h => B (a h) (deriv b h) + B (deriv a h) (b h))
        (B (a 0) (deriv (deriv b) 0) + B (deriv a 0) (deriv b 0) +
          (B (deriv a 0) (deriv b 0) + B (deriv (deriv a) 0) (b 0))) 0 :=
      (B.hasDerivAt_of_bilinear (u := a) (v := deriv b) (fun _ => a1 0)
        (fun _ => b2 0)).add
      (B.hasDerivAt_of_bilinear (u := deriv a) (v := b) (fun _ => a2 0) (fun _ => b1 0))
    rw [key.deriv]; module

end Calculus

section Norm

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Derivative of the norm of a differentiable curve at a point where it does not vanish. -/
theorem hasDerivAt_norm_curve {w : ℝ → G} {w' : G} {h : ℝ} (hw : HasDerivAt w w' h)
    (h0 : w h ≠ 0) : HasDerivAt (fun x => ‖w x‖) (inner ℝ (w h) w' / ‖w h‖) h := by
  have hn : ‖w h‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have h1 : HasDerivAt (fun x => Real.sqrt (‖w x‖ ^ 2))
      (2 * inner ℝ (w h) w' / (2 * Real.sqrt (‖w h‖ ^ 2))) h :=
    hw.norm_sq.sqrt (pow_ne_zero 2 hn)
  have h2 : (fun x => Real.sqrt (‖w x‖ ^ 2)) = fun x => ‖w x‖ :=
    funext fun x => Real.sqrt_sq (norm_nonneg _)
  rw [h2, Real.sqrt_sq (norm_nonneg _)] at h1
  convert h1 using 1
  field_simp

/-- For a `C²` curve `w` with `w 0 ≠ 0`, the norm `‖w h‖` has, near `0`, a derivative `g₁ h`
whose own derivative at `0` is the stated second-order expression. -/
theorem norm_d2 {w : ℝ → G} (hw : ContDiff ℝ 2 w) (h0 : w 0 ≠ 0) :
    ∃ g1 : ℝ → ℝ, (∀ᶠ h in 𝓝 (0 : ℝ), HasDerivAt (fun x => ‖w x‖) (g1 h) h) ∧
      HasDerivAt g1
        ((‖deriv w 0‖ ^ 2 + inner ℝ (w 0) (deriv (deriv w) 0)) / ‖w 0‖ -
          (inner ℝ (w 0) (deriv w 0)) ^ 2 / ‖w 0‖ ^ 3) 0 := by
  have w1 : ∀ h, HasDerivAt w (deriv w h) h := hasDerivAt_deriv_of_contDiff hw (by norm_num)
  have w2 : ∀ h, HasDerivAt (deriv w) (deriv (deriv w) h) h :=
    hasDerivAt_deriv_of_contDiff (contDiff_deriv_one hw) (by norm_num)
  have hn : ‖w 0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  refine ⟨fun h => inner ℝ (w h) (deriv w h) / ‖w h‖, ?_, ?_⟩
  · have hev : ∀ᶠ h in 𝓝 (0 : ℝ), w h ≠ 0 := hw.continuous.continuousAt.eventually_ne h0
    exact hev.mono fun h hh => hasDerivAt_norm_curve (w1 h) hh
  · have hnum : HasDerivAt (fun h => inner ℝ (w h) (deriv w h))
        (inner ℝ (w 0) (deriv (deriv w) 0) + inner ℝ (deriv w 0) (deriv w 0)) 0 :=
      (w1 0).inner ℝ (w2 0)
    have hden := hasDerivAt_norm_curve (w1 0) h0
    have := hnum.div hden hn
    convert this using 1
    rw [real_inner_self_eq_norm_sq]
    field_simp
    ring

/-- Second derivative at `0` of `h ↦ (‖w₁ h‖ + ‖w₂ h‖) / 2`. -/
theorem half_sum_norm_d2 {w1 w2 : ℝ → G} (hw1 : ContDiff ℝ 2 w1) (hw2 : ContDiff ℝ 2 w2)
    (h1 : w1 0 ≠ 0) (h2 : w2 0 ≠ 0) :
    deriv (deriv (fun h => (‖w1 h‖ + ‖w2 h‖) / 2)) 0 =
      (((‖deriv w1 0‖ ^ 2 + inner ℝ (w1 0) (deriv (deriv w1) 0)) / ‖w1 0‖ -
          (inner ℝ (w1 0) (deriv w1 0)) ^ 2 / ‖w1 0‖ ^ 3) +
        ((‖deriv w2 0‖ ^ 2 + inner ℝ (w2 0) (deriv (deriv w2) 0)) / ‖w2 0‖ -
          (inner ℝ (w2 0) (deriv w2 0)) ^ 2 / ‖w2 0‖ ^ 3)) / 2 := by
  obtain ⟨g1, hg1, hg1'⟩ := norm_d2 hw1 h1
  obtain ⟨g2, hg2, hg2'⟩ := norm_d2 hw2 h2
  have hev : deriv (fun h => (‖w1 h‖ + ‖w2 h‖) / 2) =ᶠ[𝓝 (0 : ℝ)]
      fun h => (g1 h + g2 h) / 2 := by
    filter_upwards [hg1, hg2] with h a b
    exact ((a.add b).div_const 2).deriv
  rw [hev.deriv_eq]
  exact ((hg1'.add hg2').div_const 2).deriv

end Norm

/-! ### Part 2: the diagonal curves and the normalized chords of a cell -/

section Cell

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (F : ℝ × ℝ → E) (s t : ℝ)

/-- The diagonal curve `x ↦ F ((s, t) + x • (1, 1))`. -/
def gP (x : ℝ) : E := F ((s, t) + x • ((1 : ℝ), (1 : ℝ)))

/-- The anti-diagonal curve `x ↦ F ((s, t) + x • (1, -1))`. -/
def gM (x : ℝ) : E := F ((s, t) + x • ((1 : ℝ), (-1 : ℝ)))

/-- The mixed second derivative, as `(gP'' 0 - gM'' 0) / 4`. -/
noncomputable def Fst : E :=
  (1 / 4 : ℝ) • (deriv (deriv (gP F s t)) 0 - deriv (deriv (gM F s t)) 0)

/-- Third derivative along the diagonal: `D₊³ F`. -/
noncomputable def DP3 : E := deriv (deriv (deriv (gP F s t))) 0

/-- Third derivative along the anti-diagonal: `D₋³ F`. -/
noncomputable def DM3 : E := deriv (deriv (deriv (gM F s t))) 0

/-- The three normalized chords as functions of `h` alone. -/
noncomputable def cS (h : ℝ) : E := eS F ((s, t), h)
noncomputable def cD (h : ℝ) : E := eD F ((s, t), h)
noncomputable def cT (h : ℝ) : E := eT F ((s, t), h)

omit [CompleteSpace E] in
theorem gP_contDiff {n : WithTop ℕ∞} (hF : ContDiff ℝ n F) : ContDiff ℝ n (gP F s t) :=
  hF.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

omit [CompleteSpace E] in
theorem gM_contDiff {n : WithTop ℕ∞} (hF : ContDiff ℝ n F) : ContDiff ℝ n (gM F s t) :=
  hF.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

omit [CompleteSpace E] in
theorem cS_contDiff (hF : ContDiff ℝ 4 F) : ContDiff ℝ 3 (cS F s t) :=
  (eS_contDiff F (n := 3) (by norm_num; exact hF)).comp (contDiff_const.prodMk contDiff_id)

omit [CompleteSpace E] in
theorem cD_contDiff (hF : ContDiff ℝ 4 F) : ContDiff ℝ 3 (cD F s t) :=
  (eD_contDiff F (n := 3) (by norm_num; exact hF)).comp (contDiff_const.prodMk contDiff_id)

omit [CompleteSpace E] in
theorem cT_contDiff (hF : ContDiff ℝ 4 F) : ContDiff ℝ 3 (cT F s t) :=
  (eT_contDiff F (n := 3) (by norm_num; exact hF)).comp (contDiff_const.prodMk contDiff_id)

/-- `h • cS h = gM (h/2) - gP (-h/2)`. -/
theorem cS_rel (hF : ContDiff ℝ 4 F) (h : ℝ) :
    gM F s t (2⁻¹ * h) - gP F s t (-2⁻¹ * h) = h • cS F s t h := by
  have key := edge_s F (hF.of_le (by norm_num)) s t h
  have e1 : gM F s t (2⁻¹ * h) = F (s + h / 2, t - h / 2) := by
    unfold gM; congr 1; ext <;> simp <;> ring
  have e2 : gP F s t (-2⁻¹ * h) = F (s - h / 2, t - h / 2) := by
    unfold gP; congr 1; ext <;> simp <;> ring
  rw [e1, e2, key]; rfl

/-- `h • cD h = gP (h/2) - gP (-h/2)`. -/
theorem cD_rel (hF : ContDiff ℝ 4 F) (h : ℝ) :
    gP F s t (2⁻¹ * h) - gP F s t (-2⁻¹ * h) = h • cD F s t h := by
  have key := edge_diag F (hF.of_le (by norm_num)) s t h
  have e1 : gP F s t (2⁻¹ * h) = F (s + h / 2, t + h / 2) := by
    unfold gP; congr 1; ext <;> simp <;> ring
  have e2 : gP F s t (-2⁻¹ * h) = F (s - h / 2, t - h / 2) := by
    unfold gP; congr 1; ext <;> simp <;> ring
  rw [e1, e2, key]; rfl

/-- `h • cT h = gM (-h/2) - gP (-h/2)`. -/
theorem cT_rel (hF : ContDiff ℝ 4 F) (h : ℝ) :
    gM F s t (-2⁻¹ * h) - gP F s t (-2⁻¹ * h) = h • cT F s t h := by
  have key := edge_t F (hF.of_le (by norm_num)) s t h
  have e1 : gM F s t (-2⁻¹ * h) = F (s - h / 2, t + h / 2) := by
    unfold gM; congr 1; ext <;> simp <;> ring
  have e2 : gP F s t (-2⁻¹ * h) = F (s - h / 2, t - h / 2) := by
    unfold gP; congr 1; ext <;> simp <;> ring
  rw [e1, e2, key]; rfl

omit [CompleteSpace E] in
/-- Generic computation: derivatives at `0` of `h ↦ a (c * h) - b (d * h)`. -/
theorem diff_scaled_derivs {a b : ℝ → E} (ha : ContDiff ℝ 3 a) (hb : ContDiff ℝ 3 b)
    (c d : ℝ) :
    deriv (deriv (fun h => a (c * h) - b (d * h))) 0 =
        (c * c) • deriv (deriv a) 0 - (d * d) • deriv (deriv b) 0 ∧
      deriv (deriv (deriv (fun h => a (c * h) - b (d * h)))) 0 =
        (c * c * c) • deriv (deriv (deriv a)) 0 - (d * d * d) • deriv (deriv (deriv b)) 0 := by
  have hA : ContDiff ℝ 3 (fun h => a (c * h)) := ha.comp (contDiff_const.mul contDiff_id)
  have hB : ContDiff ℝ 3 (fun h => b (d * h)) := hb.comp (contDiff_const.mul contDiff_id)
  constructor
  · rw [d2_sub hA hB, d2_scaled, d2_scaled]; simp
  · rw [d3_sub hA hB, d3_scaled, d3_scaled]; simp

theorem cS_d1 (hF : ContDiff ℝ 4 F) : deriv (cS F s t) 0 = (-(1 / 2) : ℝ) • Fst F s t := by
  have hg := gP_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have hm := gM_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have h1 := (smul_id_derivs (cS_contDiff F s t hF) (fun h => (cS_rel F s t hF h))).1
  rw [(diff_scaled_derivs hm hg 2⁻¹ (-2⁻¹)).1] at h1
  have : deriv (cS F s t) 0 = (1 / 2 : ℝ) • ((2 : ℝ) • deriv (cS F s t) 0) := by module
  rw [this, ← h1, Fst]; module

theorem cS_d2 (hF : ContDiff ℝ 4 F) :
    deriv (deriv (cS F s t)) 0 = (1 / 24 : ℝ) • (DP3 F s t + DM3 F s t) := by
  have hg := gP_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have hm := gM_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have h1 := (smul_id_derivs (cS_contDiff F s t hF) (fun h => (cS_rel F s t hF h))).2
  rw [(diff_scaled_derivs hm hg 2⁻¹ (-2⁻¹)).2] at h1
  have : deriv (deriv (cS F s t)) 0 = (1 / 3 : ℝ) • ((3 : ℝ) • deriv (deriv (cS F s t)) 0) := by
    module
  rw [this, ← h1, DP3, DM3]; module

theorem cD_d1 (hF : ContDiff ℝ 4 F) : deriv (cD F s t) 0 = 0 := by
  have hg := gP_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have h1 := (smul_id_derivs (cD_contDiff F s t hF) (fun h => (cD_rel F s t hF h))).1
  rw [(diff_scaled_derivs hg hg 2⁻¹ (-2⁻¹)).1] at h1
  have : deriv (cD F s t) 0 = (1 / 2 : ℝ) • ((2 : ℝ) • deriv (cD F s t) 0) := by module
  rw [this, ← h1]; module

theorem cD_d2 (hF : ContDiff ℝ 4 F) :
    deriv (deriv (cD F s t)) 0 = (1 / 12 : ℝ) • DP3 F s t := by
  have hg := gP_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have h1 := (smul_id_derivs (cD_contDiff F s t hF) (fun h => (cD_rel F s t hF h))).2
  rw [(diff_scaled_derivs hg hg 2⁻¹ (-2⁻¹)).2] at h1
  have : deriv (deriv (cD F s t)) 0 = (1 / 3 : ℝ) • ((3 : ℝ) • deriv (deriv (cD F s t)) 0) := by
    module
  rw [this, ← h1, DP3]; module

theorem cT_d1 (hF : ContDiff ℝ 4 F) : deriv (cT F s t) 0 = (-(1 / 2) : ℝ) • Fst F s t := by
  have hg := gP_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have hm := gM_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have h1 := (smul_id_derivs (cT_contDiff F s t hF) (fun h => (cT_rel F s t hF h))).1
  rw [(diff_scaled_derivs hm hg (-2⁻¹) (-2⁻¹)).1] at h1
  have : deriv (cT F s t) 0 = (1 / 2 : ℝ) • ((2 : ℝ) • deriv (cT F s t) 0) := by module
  rw [this, ← h1, Fst]; module

theorem cT_d2 (hF : ContDiff ℝ 4 F) :
    deriv (deriv (cT F s t)) 0 = (1 / 24 : ℝ) • (DP3 F s t - DM3 F s t) := by
  have hg := gP_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have hm := gM_contDiff F s t (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have h1 := (smul_id_derivs (cT_contDiff F s t hF) (fun h => (cT_rel F s t hF h))).2
  rw [(diff_scaled_derivs hm hg (-2⁻¹) (-2⁻¹)).2] at h1
  have : deriv (deriv (cT F s t)) 0 = (1 / 3 : ℝ) • ((3 : ℝ) • deriv (deriv (cT F s t)) 0) := by
    module
  rw [this, ← h1, DP3, DM3]; module

end Cell

/-! ### Part 3: the second derivative of the normalized paired area -/

section Area

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable (B : E →L[ℝ] E →L[ℝ] G)

/-- The `h²` coefficient of `(‖N + h u + h² p‖ + ‖N + h v + h² q‖) / 2`. -/
noncomputable def q2Coeff (N u v p q : G) : ℝ :=
  ((‖u‖ ^ 2 + 2 * inner ℝ N p) / (2 * ‖N‖) - (inner ℝ N u) ^ 2 / (2 * ‖N‖ ^ 3) +
    ((‖v‖ ^ 2 + 2 * inner ℝ N q) / (2 * ‖N‖) - (inner ℝ N v) ^ 2 / (2 * ‖N‖ ^ 3))) / 2

/-- `a1` of `Lemma2Algebra.lean`: the `h` coefficient of the first triangle product. -/
noncomputable def uVec (fs ft fst : E) : G := (-(1 / 2) : ℝ) • B fst (fs + ft)

/-- `a2` of `Lemma2Algebra.lean`: the `h` coefficient of the second triangle product. -/
noncomputable def vVec (fs ft fst : E) : G := (1 / 2 : ℝ) • B fst (fs + ft)

/-- `b1` of `Lemma2Algebra.lean`, written with `D₊³F`, `D₋³F`. -/
noncomputable def pVec (fs ft dp dm : E) : G :=
  B ((1 / 48 : ℝ) • (dp + dm)) (fs + ft) + (1 / 24 : ℝ) • B fs dp

/-- `b2` of `Lemma2Algebra.lean`, written with `D₊³F`, `D₋³F`. -/
noncomputable def qVec (fs ft dp dm : E) : G :=
  (1 / 24 : ℝ) • B dp ft + B (fs + ft) ((1 / 48 : ℝ) • (dp - dm))

omit [CompleteSpace E] in
/-- Clearing denominators: `‖N‖³ q₂` is the left-hand side of `q2_polynomial_identity`. -/
theorem q2Coeff_mul_norm_cube {N : G} (hN : N ≠ 0) (u v p q : G) :
    ‖N‖ ^ 3 * q2Coeff N u v p q =
      ‖N‖ ^ 2 * ((‖u‖ ^ 2 + 2 * inner ℝ N p + ‖v‖ ^ 2 + 2 * inner ℝ N q) / 4) -
        ((inner ℝ N u) ^ 2 + (inner ℝ N v) ^ 2) / 4 := by
  have hn : ‖N‖ ≠ 0 := norm_ne_zero_iff.mpr hN
  unfold q2Coeff
  field_simp
  ring

variable (F : ℝ × ℝ → E)

/-- **The `q₂` coefficient.** For an alternating `B` and `F` of class `C⁴`, at a point where
`B F_s F_t ≠ 0`, the second `h`-derivative of the normalized paired area at `h = 0` is
`2 * q2Coeff N u v p q` with `N = B F_s F_t` and `u, v, p, q` the Lemma 2 coefficients. -/
theorem normArea_d2 (hF : ContDiff ℝ 4 F) (hB : ∀ u, B u u = 0) (s t : ℝ)
    (hreg : B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) ≠ 0) :
    deriv (deriv (fun h => normArea B F ((s, t), h))) 0 =
      2 * q2Coeff (B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)))
        (uVec B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) (Fst F s t))
        (vVec B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) (Fst F s t))
        (pVec B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) (DP3 F s t) (DM3 F s t))
        (qVec B (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) (DP3 F s t)
          (DM3 F s t)) := by
  set fs := fderiv ℝ F (s, t) (1, 0) with hfs
  set ft := fderiv ℝ F (s, t) (0, 1) with hft
  have hS := cS_contDiff F s t hF
  have hD := cD_contDiff F s t hF
  have hT := cT_contDiff F s t hF
  have hS2 : ContDiff ℝ 2 (cS F s t) := hS.of_le (by norm_num)
  have hD2 : ContDiff ℝ 2 (cD F s t) := hD.of_le (by norm_num)
  have hT2 : ContDiff ℝ 2 (cT F s t) := hT.of_le (by norm_num)
  have S0 : cS F s t 0 = fs := eS_zero F s t
  have D0 : cD F s t 0 = fs + ft := by
    show eD F ((s, t), 0) = _
    rw [eD_zero, fderiv_diag]
  have T0 : cT F s t 0 = ft := eT_zero F s t
  -- the two triangle products as curves in `h`
  have hw1 : ContDiff ℝ 2 (fun h => B (cS F s t h) (cD F s t h)) :=
    (B.contDiff.comp hS2).clm_apply hD2
  have hw2 : ContDiff ℝ 2 (fun h => B (cD F s t h) (cT F s t h)) :=
    (B.contDiff.comp hD2).clm_apply hT2
  obtain ⟨w1d1, w1d2⟩ := bilin_derivs B hS2 hD2
  obtain ⟨w2d1, w2d2⟩ := bilin_derivs B hD2 hT2
  rw [cS_d1 F s t hF, cD_d1 F s t hF, S0, D0] at w1d1
  rw [cS_d2 F s t hF, cS_d1 F s t hF, cD_d1 F s t hF, cD_d2 F s t hF, S0, D0] at w1d2
  rw [cD_d1 F s t hF, cT_d1 F s t hF, D0, T0] at w2d1
  rw [cD_d2 F s t hF, cD_d1 F s t hF, cT_d1 F s t hF, cT_d2 F s t hF, D0, T0] at w2d2
  have N1 : B (cS F s t 0) (cD F s t 0) = B fs ft := by
    rw [S0, D0, map_add, hB, zero_add]
  have N2 : B (cD F s t 0) (cT F s t 0) = B fs ft := by
    rw [D0, T0, ContinuousLinearMap.map_add₂, hB, add_zero]
  have U : deriv (fun h => B (cS F s t h) (cD F s t h)) 0 = uVec B fs ft (Fst F s t) := by
    rw [w1d1, uVec]; simp only [map_smul, map_zero, smul_apply, add_zero]
  have V : deriv (fun h => B (cD F s t h) (cT F s t h)) 0 = vVec B fs ft (Fst F s t) := by
    rw [w2d1, vVec, anti B hB (fs + ft)]
    simp only [map_smul, map_zero, smul_apply, zero_apply, zero_add]
    module
  have P : deriv (deriv (fun h => B (cS F s t h) (cD F s t h))) 0 =
      (2 : ℝ) • pVec B fs ft (DP3 F s t) (DM3 F s t) := by
    rw [w1d2, pVec]
    simp only [map_smul, map_zero, smul_apply, smul_zero]
    module
  have Q : deriv (deriv (fun h => B (cD F s t h) (cT F s t h))) 0 =
      (2 : ℝ) • qVec B fs ft (DP3 F s t) (DM3 F s t) := by
    rw [w2d2, qVec]
    simp only [map_smul, map_zero, smul_apply, zero_apply, smul_zero]
    module
  have key := half_sum_norm_d2 hw1 hw2 (by rw [N1]; exact hreg) (by rw [N2]; exact hreg)
  rw [N1, N2, U, V, P, Q] at key
  have hfun : (fun h => normArea B F ((s, t), h)) =
      fun h => (‖B (cS F s t h) (cD F s t h)‖ + ‖B (cD F s t h) (cT F s t h)‖) / 2 := rfl
  rw [hfun, key, q2Coeff]
  simp only [inner_smul_right]
  ring

end Area

/-! ### Part 4: the Euclidean cross product -/

open BakerSpherical.CrossContinuous in
/-- **`q₂` for the real cross product.** For `F : ℝ² → ℝ³` of class `C⁴`, at a point where
`F_s × F_t ≠ 0`, the second `h`-derivative of the normalized paired chordal area at `h = 0`
is `2 * q₂`. -/
theorem cross_normArea_d2 (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 4 F) (s t : ℝ)
    (hreg : crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) ≠ 0) :
    deriv (deriv (fun h => normArea crossE F ((s, t), h))) 0 =
      2 * q2Coeff (crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)))
        (uVec crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) (Fst F s t))
        (vVec crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) (Fst F s t))
        (pVec crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) (DP3 F s t)
          (DM3 F s t))
        (qVec crossE (fderiv ℝ F (s, t) (1, 0)) (fderiv ℝ F (s, t) (0, 1)) (DP3 F s t)
          (DM3 F s t)) :=
  normArea_d2 crossE F hF crossE_self s t hreg

end BakerSpherical.Q2

#print axioms BakerSpherical.Q2.smul_id_derivs
#print axioms BakerSpherical.Q2.bilin_derivs
#print axioms BakerSpherical.Q2.norm_d2
#print axioms BakerSpherical.Q2.half_sum_norm_d2
#print axioms BakerSpherical.Q2.cS_d1
#print axioms BakerSpherical.Q2.cS_d2
#print axioms BakerSpherical.Q2.cD_d1
#print axioms BakerSpherical.Q2.cD_d2
#print axioms BakerSpherical.Q2.cT_d1
#print axioms BakerSpherical.Q2.cT_d2
#print axioms BakerSpherical.Q2.q2Coeff_mul_norm_cube
#print axioms BakerSpherical.Q2.normArea_d2
#print axioms BakerSpherical.Q2.cross_normArea_d2
