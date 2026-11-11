import Mathlib
import NormalizedChordSmoothExtension
import CrossProductBilinear

namespace BakerSpherical.CrossContinuous

open BakerSpherical.SmoothExtension

/-- Exact factorization of paired area for the real cross product. -/
theorem cross_pairedArea_eq
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ 1 F) (s t h : ℝ) :
    pairedArea crossE F s t h =
      h ^ 2 * normArea crossE F ((s, t), h) := by
  exact pairedArea_eq crossE F hF s t h

/-- The leading coefficient is the Euclidean surface Jacobian. -/
theorem cross_normArea_zero
    (F : ℝ × ℝ → E3) (s t : ℝ) :
    normArea crossE F ((s, t), 0) =
      ‖crossE (fderiv ℝ F (s, t) (1, 0))
          (fderiv ℝ F (s, t) (0, 1))‖ := by
  exact normArea_zero crossE F crossE_self s t

/-- The normalized paired area is even in cell width. -/
theorem cross_normArea_neg
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ 1 F) (s t h : ℝ) :
    normArea crossE F ((s, t), -h) =
      normArea crossE F ((s, t), h) := by
  exact normArea_neg crossE F hF crossE_self s t h

/-- Smoothness at a regular point of the spherical parametrization. -/
theorem cross_normArea_contDiffAt
    {n : ℕ∞}
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ (n + 1) F)
    (s t : ℝ)
    (hreg : crossE
      (fderiv ℝ F (s, t) (1, 0))
      (fderiv ℝ F (s, t) (0, 1)) ≠ 0) :
    ContDiffAt ℝ n (normArea crossE F) ((s, t), 0) := by
  exact normArea_contDiffAt crossE F hF crossE_self s t hreg

end BakerSpherical.CrossContinuous

#print axioms BakerSpherical.CrossContinuous.cross_pairedArea_eq
#print axioms BakerSpherical.CrossContinuous.cross_normArea_zero
#print axioms BakerSpherical.CrossContinuous.cross_normArea_neg
#print axioms BakerSpherical.CrossContinuous.cross_normArea_contDiffAt