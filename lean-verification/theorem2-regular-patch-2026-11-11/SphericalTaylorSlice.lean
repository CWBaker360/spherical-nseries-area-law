import Mathlib
import CrossProductAreaBridge_v2

namespace BakerSpherical.CrossContinuous

open BakerSpherical.SmoothExtension

/--
The normalized spherical paired-cell area as a
one-variable function of the signed cell width.
-/
noncomputable def sliceArea
    (F : ℝ × ℝ → E3)
    (y : ℝ × ℝ) (h : ℝ) : ℝ :=
  normArea crossE F (y, h)

/-- The spherical area slice is even in h. -/
theorem sliceArea_even
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ 1 F)
    (y : ℝ × ℝ) (h : ℝ) :
    sliceArea F y (-h) = sliceArea F y h := by
  exact cross_normArea_neg F hF y.1 y.2 h

/--
The value at zero width is the norm of the
cross product of the coordinate derivatives.
-/
theorem sliceArea_zero
    (F : ℝ × ℝ → E3)
    (y : ℝ × ℝ) :
    sliceArea F y 0 =
      ‖crossE
        (fderiv ℝ F y (1, 0))
        (fderiv ℝ F y (0, 1))‖ := by
  exact cross_normArea_zero F y.1 y.2

end BakerSpherical.CrossContinuous

#print axioms BakerSpherical.CrossContinuous.sliceArea_even
#print axioms BakerSpherical.CrossContinuous.sliceArea_zero