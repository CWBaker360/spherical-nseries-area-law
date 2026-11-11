import Mathlib
import SphericalSliceFourthIdentity
import SphericalVerticalFourthBound

namespace BakerSpherical.UniformTaylor

/-- The two representations of the vertical vector agree. -/
private theorem verticalDirection_eq :
    verticalDirection =
      ((0 : ℝ × ℝ), (1 : ℝ)) := by
  ext <;> simp [verticalDirection]

/--
The fourth derivative of a vertical slice is bounded
by the fourth Frechet derivative operator norm.
Only local C4 regularity is required.
-/
theorem slice_fourth_le_frechet
    (G : ((ℝ × ℝ) × ℝ) → ℝ)
    (y : ℝ × ℝ)
    (h : ℝ)
    (hG : ContDiffAt ℝ 4 G (y, h)) :
    |iteratedDeriv 4
        (fun u : ℝ => G (y, u)) h|
      ≤ ‖iteratedFDeriv ℝ 4 G (y, h)‖ := by

  have hid :=
    slice_fourth_identity G y h hG

  have hb :=
    vertical_fourth_le_opNorm G (y, h)

  rw [hid]
  rw [verticalDirection_eq] at hb

  simpa only [Real.norm_eq_abs] using hb

/--
A uniform fourth Frechet derivative bound transfers
to the ordinary fourth derivative of the slice.
-/
theorem slice_fourth_le_uniform
    (G : ((ℝ × ℝ) × ℝ) → ℝ)
    (y : ℝ × ℝ)
    (h M : ℝ)
    (hG : ContDiffAt ℝ 4 G (y, h))
    (hM : ‖iteratedFDeriv ℝ 4 G (y, h)‖ ≤ M) :
    |iteratedDeriv 4
        (fun u : ℝ => G (y, u)) h| ≤ M := by

  exact (slice_fourth_le_frechet G y h hG).trans hM

end BakerSpherical.UniformTaylor

#print axioms
  BakerSpherical.UniformTaylor.slice_fourth_le_frechet
#print axioms
  BakerSpherical.UniformTaylor.slice_fourth_le_uniform