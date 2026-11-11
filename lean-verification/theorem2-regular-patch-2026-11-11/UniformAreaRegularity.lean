import Mathlib
import CrossProductRegularity
import SphericalUniformWidth

namespace BakerSpherical.CrossContinuous

open BakerSpherical.SmoothExtension

/--
A compact regular surface patch admits a common
positive cell width on which normalized area is C4.
-/
theorem spherical_uniform_contDiffAt
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
          ContDiffAt ℝ 4
            (normArea crossE F) (y, h) := by

  obtain ⟨H, hH, hwidth⟩ :=
    spherical_uniform_width F hF K hK hreg

  refine ⟨H, hH, ?_⟩
  intro y hy h hh

  obtain ⟨hn1, hn2⟩ := hwidth y hy h hh

  exact cross_normArea_contDiffAt_general
    (n := 4) F
    (hF.of_le (by norm_num))
    (y, h) hn1 hn2

end BakerSpherical.CrossContinuous

#print axioms
  BakerSpherical.CrossContinuous.spherical_uniform_contDiffAt