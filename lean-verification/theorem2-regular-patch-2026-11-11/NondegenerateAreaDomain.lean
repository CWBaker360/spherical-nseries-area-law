import Mathlib
import NormalizedChordSmoothExtension
import CrossProductBilinear

namespace BakerSpherical.CrossContinuous

open BakerSpherical.SmoothExtension

/-- The domain where both normalized cross products
are nonzero is open. -/
theorem regular_area_domain_open
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ 5 F) :
    IsOpen {p : (ℝ × ℝ) × ℝ |
      w1 crossE F p ≠ 0 ∧
      w2 crossE F p ≠ 0} := by

  have hc1 : Continuous (w1 crossE F) :=
    (w1_contDiff crossE F (n := 4)
      (hF.of_le (by norm_num))).continuous

  have hc2 : Continuous (w2 crossE F) :=
    (w2_contDiff crossE F (n := 4)
      (hF.of_le (by norm_num))).continuous

  change IsOpen
    (Function.support (w1 crossE F) ∩
     Function.support (w2 crossE F))

  exact hc1.isOpen_support.inter hc2.isOpen_support

end BakerSpherical.CrossContinuous

#print axioms BakerSpherical.CrossContinuous.regular_area_domain_open