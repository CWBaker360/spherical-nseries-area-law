import Mathlib
import NondegenerateAreaDomain
import CompactUniformWidth

namespace BakerSpherical.CrossContinuous

open BakerSpherical.SmoothExtension
open BakerSpherical.UniformTaylor

/--
A compact regular surface patch has a common positive
cell width for which both normalized triangle cross
products remain nonzero.
-/
theorem spherical_uniform_width
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ 5 F)
    (K : Set (ℝ × ℝ))
    (hK : IsCompact K)
    (hreg : ∀ y ∈ K,
      crossE
        (fderiv ℝ F y (1, 0))
        (fderiv ℝ F y (0, 1)) ≠ 0) :
    ∃ H : ℝ, 0 < H ∧
      ∀ y ∈ K, ∀ h : ℝ,
        |h| ≤ H →
          w1 crossE F (y, h) ≠ 0 ∧
          w2 crossE F (y, h) ≠ 0 := by

  let U : Set ((ℝ × ℝ) × ℝ) :=
    {p | w1 crossE F p ≠ 0 ∧
         w2 crossE F p ≠ 0}

  have hU : IsOpen U :=
    regular_area_domain_open F hF

  have hzero : ∀ y ∈ K, (y, (0 : ℝ)) ∈ U := by
    intro y hy
    rcases y with ⟨s, t⟩
    change
      w1 crossE F ((s, t), 0) ≠ 0 ∧
      w2 crossE F ((s, t), 0) ≠ 0
    constructor
    · rw [w1_zero crossE F crossE_self]
      exact hreg (s, t) hy
    · rw [w2_zero crossE F crossE_self]
      exact hreg (s, t) hy

  obtain ⟨H, hH, hwidth⟩ :=
    compact_uniform_width K U hK hU hzero

  refine ⟨H, hH, ?_⟩
  intro y hy h hh
  exact hwidth y hy h hh

end BakerSpherical.CrossContinuous

#print axioms
  BakerSpherical.CrossContinuous.spherical_uniform_width