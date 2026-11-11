import Mathlib
import SphericalLocalTaylor

/-!
# Spherical N-Series v2.4 — summing the local expansion over the `N × N` grid

Grid of the v2.4 draft: the unit parameter square `[0,1]²` is cut into `N × N` squares of
side `h = 1/N`, with midpoint centres `x_ij = ((i + 1/2) h, (j + 1/2) h)`; each square is
split along its lower-left to upper-right diagonal into two chordal triangles.

* `center`, `center_mem`      : the midpoint centres, and that they lie in the unit square;
* `chordalArea F N`           : the total chordal area `A_N`, the sum over the grid of the
                                paired chordal areas of the cells;
* `chordalArea_cell_sum`      : there are `H > 0`, `M ≥ 0` with, for all `N ≥ 1`, `1/N ≤ H`,

    `|A_N - Σ_ij (J(x_ij) h² + q₂(x_ij) h⁴)| ≤ M h⁴ / 24`,   `J = ‖F_s × F_t‖`;

* `area_law_of_midpoint_rules`: **conditional** form of Theorem 2. If the midpoint sums of
  `J` and of `q₂` satisfy the quadrature estimates
    `|h² Σ J(x_ij) - (A + c h²)| ≤ K₁ h⁴`  and  `|h² Σ q₂(x_ij) - Q| ≤ K₂ h²`,
  then `|A_N - (A + (c + Q) h²)| ≤ (M/24 + K₁ + K₂) h⁴`.

## Scope: what is NOT proved here

* The two midpoint quadrature estimates are HYPOTHESES of `area_law_of_midpoint_rules`. They
  are not proved. In the paper they are the midpoint Euler--Maclaurin step, with
  `A = ∬ J`, `c = (1/24) ∬ ΔJ` and `Q = ∬ q₂`. So Theorem 2 is not yet a Lean theorem.
* The patch is the closed unit square with `F_s × F_t ≠ 0` on all of it; a coordinate pole
  is excluded by that hypothesis.
-/

namespace BakerSpherical.GlobalSum

open BakerSpherical.SmoothExtension BakerSpherical.CrossContinuous BakerSpherical.LocalTaylor
open Finset

/-- The closed unit parameter square. -/
def unitSquare : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

theorem unitSquare_compact : IsCompact unitSquare := isCompact_Icc.prod isCompact_Icc

theorem unitSquare_nonempty : unitSquare.Nonempty :=
  ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩⟩

/-- Midpoint centre of the cell `(i, j)` of the `N × N` grid. -/
noncomputable def center (N i j : ℕ) : ℝ × ℝ :=
  (((i : ℝ) + 1 / 2) / N, ((j : ℝ) + 1 / 2) / N)

theorem coord_mem {N i : ℕ} (hi : i < N) : ((i : ℝ) + 1 / 2) / N ∈ Set.Icc (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  constructor
  · positivity
  · rw [div_le_one hN]; linarith

theorem center_mem {N i j : ℕ} (hi : i < N) (hj : j < N) : center N i j ∈ unitSquare :=
  ⟨coord_mem hi, coord_mem hj⟩

/-- The total chordal area `A_N` of the `N × N` triangulated grid. -/
noncomputable def chordalArea (F : ℝ × ℝ → E3) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N,
    pairedArea crossE F (center N i j).1 (center N i j).2 (1 / N)

/-- The surface area density `J = ‖F_s × F_t‖`. -/
noncomputable def jac (F : ℝ × ℝ → E3) (y : ℝ × ℝ) : ℝ :=
  ‖crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1))‖

/-- **Summed local expansion.** The total chordal area differs from the grid sum of
`J h² + q₂ h⁴` by at most `M h⁴ / 24`, for every sufficiently fine grid. -/
theorem chordalArea_cell_sum (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F)
    (hreg : ∀ y ∈ unitSquare, crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0) :
    ∃ H M : ℝ, 0 < H ∧ 0 ≤ M ∧ ∀ N : ℕ, 0 < N → (1 : ℝ) / N ≤ H →
      |chordalArea F N -
          ∑ i ∈ range N, ∑ j ∈ range N,
            (jac F (center N i j) * (1 / (N : ℝ)) ^ 2 +
              q2 F (center N i j) * (1 / (N : ℝ)) ^ 4)| ≤
        M * (1 / (N : ℝ)) ^ 4 / 24 := by
  obtain ⟨H, M, hH, hM, hloc⟩ :=
    spherical_local_pairedArea F hF unitSquare unitSquare_compact unitSquare_nonempty hreg
  refine ⟨H, M, hH, hM, ?_⟩
  intro N hN hNH
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : |(1 : ℝ) / N| ≤ H := by rwa [abs_of_pos (by positivity)]
  unfold chordalArea
  rw [← sum_sub_distrib]
  calc |∑ i ∈ range N, (∑ j ∈ range N,
            pairedArea crossE F (center N i j).1 (center N i j).2 (1 / N) -
          ∑ j ∈ range N, (jac F (center N i j) * (1 / (N : ℝ)) ^ 2 +
            q2 F (center N i j) * (1 / (N : ℝ)) ^ 4))|
      ≤ ∑ i ∈ range N, ∑ _j ∈ range N, M * (1 / (N : ℝ)) ^ 6 / 24 := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
        exact hloc (center N i j) (center_mem (mem_range.mp hi) (mem_range.mp hj)) (1 / N) hh
    _ = M * (1 / (N : ℝ)) ^ 4 / 24 := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        field_simp

/-- **Theorem 2, conditional on the midpoint quadrature estimates.** -/
theorem area_law_of_midpoint_rules (F : ℝ × ℝ → E3) (hF : ContDiff ℝ 5 F)
    (hreg : ∀ y ∈ unitSquare, crossE (fderiv ℝ F y (1, 0)) (fderiv ℝ F y (0, 1)) ≠ 0)
    (A c Q K1 K2 : ℝ)
    (hJ : ∀ N : ℕ, 0 < N →
      |(1 / (N : ℝ)) ^ 2 * ∑ i ∈ range N, ∑ j ∈ range N, jac F (center N i j) -
          (A + c * (1 / (N : ℝ)) ^ 2)| ≤ K1 * (1 / (N : ℝ)) ^ 4)
    (hq : ∀ N : ℕ, 0 < N →
      |(1 / (N : ℝ)) ^ 2 * ∑ i ∈ range N, ∑ j ∈ range N, q2 F (center N i j) - Q| ≤
        K2 * (1 / (N : ℝ)) ^ 2) :
    ∃ H M : ℝ, 0 < H ∧ 0 ≤ M ∧ ∀ N : ℕ, 0 < N → (1 : ℝ) / N ≤ H →
      |chordalArea F N - (A + (c + Q) * (1 / (N : ℝ)) ^ 2)| ≤
        (M / 24 + K1 + K2) * (1 / (N : ℝ)) ^ 4 := by
  obtain ⟨H, M, hH, hM, hsum⟩ := chordalArea_cell_sum F hF hreg
  refine ⟨H, M, hH, hM, ?_⟩
  intro N hN hNH
  have h1 := hsum N hN hNH
  have h2 := hJ N hN
  have h3 := hq N hN
  set h : ℝ := 1 / (N : ℝ) with hdef
  set SJ := ∑ i ∈ range N, ∑ j ∈ range N, jac F (center N i j) with hSJ
  set Sq := ∑ i ∈ range N, ∑ j ∈ range N, q2 F (center N i j) with hSq
  have hsplit : ∑ i ∈ range N, ∑ j ∈ range N,
      (jac F (center N i j) * h ^ 2 + q2 F (center N i j) * h ^ 4) =
      h ^ 2 * SJ + h ^ 2 * (h ^ 2 * Sq) := by
    simp only [sum_add_distrib, ← sum_mul, hSJ, hSq]
    ring
  rw [hsplit] at h1
  have h3' : |h ^ 2 * (h ^ 2 * Sq - Q)| ≤ K2 * h ^ 4 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
    calc h ^ 2 * |h ^ 2 * Sq - Q| ≤ h ^ 2 * (K2 * h ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg h)
      _ = K2 * h ^ 4 := by ring
  have e : chordalArea F N - (A + (c + Q) * h ^ 2) =
      (chordalArea F N - (h ^ 2 * SJ + h ^ 2 * (h ^ 2 * Sq))) +
        (h ^ 2 * SJ - (A + c * h ^ 2)) + h ^ 2 * (h ^ 2 * Sq - Q) := by ring
  rw [e]
  calc |(chordalArea F N - (h ^ 2 * SJ + h ^ 2 * (h ^ 2 * Sq))) +
          (h ^ 2 * SJ - (A + c * h ^ 2)) + h ^ 2 * (h ^ 2 * Sq - Q)|
      ≤ |chordalArea F N - (h ^ 2 * SJ + h ^ 2 * (h ^ 2 * Sq))| +
          |h ^ 2 * SJ - (A + c * h ^ 2)| + |h ^ 2 * (h ^ 2 * Sq - Q)| := abs_add_three _ _ _
    _ ≤ M * h ^ 4 / 24 + K1 * h ^ 4 + K2 * h ^ 4 := add_le_add (add_le_add h1 h2) h3'
    _ = (M / 24 + K1 + K2) * h ^ 4 := by ring

end BakerSpherical.GlobalSum

#print axioms BakerSpherical.GlobalSum.center_mem
#print axioms BakerSpherical.GlobalSum.chordalArea_cell_sum
#print axioms BakerSpherical.GlobalSum.area_law_of_midpoint_rules
