import Mathlib
import UniformAreaRegularity
import CompactUniformBound

namespace BakerSpherical.CrossContinuous

open BakerSpherical.SmoothExtension
open BakerSpherical.UniformTaylor

/--
On a nonempty compact regular surface patch, the
fourth Frechet derivative of normalized paired area
has a common finite norm bound.
-/
theorem spherical_fourth_derivative_uniform_bound
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ 5 F)
    (K : Set (ℝ × ℝ))
    (hK : IsCompact K)
    (hne : K.Nonempty)
    (hreg : ∀ y ∈ K,
      crossE
        (fderiv ℝ F y (1, 0))
        (fderiv ℝ F y (0, 1)) ≠ 0) :
    ∃ H M : ℝ, 0 < H ∧ 0 ≤ M ∧
      ∀ y ∈ K, ∀ h : ℝ, |h| ≤ H →
        ‖iteratedFDeriv ℝ 4
          (normArea crossE F) (y, h)‖ ≤ M := by

  obtain ⟨H, hH, hregular⟩ :=
    spherical_uniform_contDiffAt F hF K hK hreg

  let S : Set ((ℝ × ℝ) × ℝ) :=
    K ×ˢ Set.Icc (-H) H

  have hS : IsCompact S := by
    exact hK.prod isCompact_Icc

  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    refine ⟨(y, (0 : ℝ)), ?_⟩
    change y ∈ K ∧ (0 : ℝ) ∈ Set.Icc (-H) H
    constructor
    · exact hy
    · constructor <;> linarith

  have hD : ContinuousOn
      (iteratedFDeriv ℝ 4 (normArea crossE F)) S := by
    intro p hp
    rcases p with ⟨y, h⟩
    change y ∈ K ∧ h ∈ Set.Icc (-H) H at hp
    obtain ⟨hy, hh⟩ := hp
    have habs : |h| ≤ H := abs_le.mpr hh
    have hcd : ContDiffAt ℝ 4
        (normArea crossE F) (y, h) :=
      hregular y hy h habs
    exact
      (hcd.continuousAt_iteratedFDeriv
        (by norm_num)).continuousWithinAt

  obtain ⟨M, hM0, hbound⟩ :=
    compact_uniform_norm_bound S hS hSne
      (iteratedFDeriv ℝ 4 (normArea crossE F)) hD

  refine ⟨H, M, hH, hM0, ?_⟩
  intro y hy h hh
  apply hbound (y, h)
  change y ∈ K ∧ h ∈ Set.Icc (-H) H
  exact ⟨hy, abs_le.mp hh⟩

end BakerSpherical.CrossContinuous

#print axioms
  BakerSpherical.CrossContinuous.spherical_fourth_derivative_uniform_bound
