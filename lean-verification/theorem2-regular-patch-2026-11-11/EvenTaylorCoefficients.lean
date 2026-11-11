import Mathlib
import SphericalTaylorSlice

namespace BakerSpherical.CrossContinuous

/--
For any even real function, the first and third
iterated derivatives vanish at zero.
-/
theorem even_odd_derivatives_zero
    (f : ℝ → ℝ)
    (hf : ∀ h : ℝ, f (-h) = f h) :
    iteratedDeriv 1 f 0 = 0 ∧
    iteratedDeriv 3 f 0 = 0 := by

  have heq : (fun h : ℝ => f (-h)) = f := by
    funext h
    exact hf h

  constructor

  · have hd := congrArg
      (fun g : ℝ → ℝ => iteratedDeriv 1 g 0) heq
    rw [iteratedDeriv_comp_neg] at hd
    norm_num at hd
    have hz : deriv f 0 = 0 := by
      linarith
    simpa only [iteratedDeriv_one] using hz

  · have hd := congrArg
      (fun g : ℝ → ℝ => iteratedDeriv 3 g 0) heq
    rw [iteratedDeriv_comp_neg] at hd
    norm_num at hd
    linarith

/--
The first and third derivatives of the normalized
spherical area slice vanish at zero.
-/
theorem sliceArea_odd_derivatives_zero
    (F : ℝ × ℝ → E3)
    (hF : ContDiff ℝ 1 F)
    (y : ℝ × ℝ) :
    iteratedDeriv 1 (sliceArea F y) 0 = 0 ∧
    iteratedDeriv 3 (sliceArea F y) 0 = 0 := by

  apply even_odd_derivatives_zero
  intro h
  exact sliceArea_even F hF y h

end BakerSpherical.CrossContinuous

#print axioms BakerSpherical.CrossContinuous.even_odd_derivatives_zero
#print axioms BakerSpherical.CrossContinuous.sliceArea_odd_derivatives_zero