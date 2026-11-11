import Mathlib

namespace BakerSpherical.UniformTaylor

/-- The unit direction of the cell-width coordinate. -/
def verticalDirection : (ℝ × ℝ) × ℝ :=
  ((0, 0), 1)

/-- The cell-width direction has norm exactly one. -/
theorem verticalDirection_norm :
    ‖verticalDirection‖ = 1 := by
  simp [verticalDirection]

/-- The vertical slice is smooth to fourth order. -/
theorem verticalPath_contDiff
    (y : ℝ × ℝ) :
    ContDiff ℝ 4
      (fun h : ℝ => (y, h)) := by
  fun_prop

end BakerSpherical.UniformTaylor

#print axioms
  BakerSpherical.UniformTaylor.verticalDirection_norm
#print axioms
  BakerSpherical.UniformTaylor.verticalPath_contDiff