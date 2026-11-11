import Mathlib
import SphericalVerticalDirection

namespace BakerSpherical.UniformTaylor

/--
A fourth continuous multilinear derivative, evaluated
four times on the unit cell-width direction, is bounded
by its operator norm.
-/
theorem vertical_fourth_le_opNorm
    (G : ((ℝ × ℝ) × ℝ) → ℝ)
    (p : (ℝ × ℝ) × ℝ) :
    ‖(iteratedFDeriv ℝ 4 G p)
        (fun _ : Fin 4 => verticalDirection)‖
      ≤ ‖iteratedFDeriv ℝ 4 G p‖ := by

  have hb :=
    (iteratedFDeriv ℝ 4 G p).le_opNorm
      (fun _ : Fin 4 => verticalDirection)

  simpa [verticalDirection_norm] using hb

/--
Transfer any existing fourth-Fréchet-derivative bound
to its evaluation along the width coordinate.
-/
theorem vertical_fourth_uniform_bound
    (G : ((ℝ × ℝ) × ℝ) → ℝ)
    (p : (ℝ × ℝ) × ℝ)
    (M : ℝ)
    (hM : ‖iteratedFDeriv ℝ 4 G p‖ ≤ M) :
    ‖(iteratedFDeriv ℝ 4 G p)
        (fun _ : Fin 4 => verticalDirection)‖
      ≤ M := by

  exact (vertical_fourth_le_opNorm G p).trans hM

end BakerSpherical.UniformTaylor

#print axioms
  BakerSpherical.UniformTaylor.vertical_fourth_le_opNorm
#print axioms
  BakerSpherical.UniformTaylor.vertical_fourth_uniform_bound