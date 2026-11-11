import Mathlib
import NormalizedChordSmoothExtension
import CrossProductBilinear

namespace BakerSpherical.CrossContinuous

open BakerSpherical.SmoothExtension

/--
The actual Euclidean normalized paired area is C^n
at any point where both triangle cross products
are nonzero.

Unlike the earlier theorem, this is not
restricted to h = 0.
-/
theorem cross_normArea_contDiffAt_general
    {n : ℕ∞}
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ (n + 1) F)
    (p : (ℝ × ℝ) × ℝ)
    (h1 : w1 crossE F p ≠ 0)
    (h2 : w2 crossE F p ≠ 0) :
    ContDiffAt ℝ n (normArea crossE F) p := by

  have hw1 :
      ContDiffAt ℝ n
        (fun q : (ℝ × ℝ) × ℝ =>
          ‖w1 crossE F q‖) p :=
    (w1_contDiff crossE F hF).contDiffAt.norm ℝ h1

  have hw2 :
      ContDiffAt ℝ n
        (fun q : (ℝ × ℝ) × ℝ =>
          ‖w2 crossE F q‖) p :=
    (w2_contDiff crossE F hF).contDiffAt.norm ℝ h2

  exact (hw1.add hw2).div_const 2

end BakerSpherical.CrossContinuous

#print axioms
  BakerSpherical.CrossContinuous.cross_normArea_contDiffAt_general