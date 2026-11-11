import Mathlib
import TaylorDerivativeBridge
import TaylorCubicReduction
import EvenTaylorCoefficients

namespace BakerSpherical.UniformTaylor

open BakerSpherical.CrossContinuous

theorem even_taylor_polynomial
    (f : ℝ → ℝ)
    (s : Set ℝ)
    (h : ℝ)
    (hs : UniqueDiffOn ℝ s)
    (hz : (0 : ℝ) ∈ s)
    (hf : ContDiffAt ℝ 4 f 0)
    (heven : ∀ u : ℝ, f (-u) = f u) :
    taylorWithinEval f 3 s 0 h =
      f 0 + iteratedDeriv 2 f 0 * h ^ 2 / 2 := by

  have hd :=
    taylor_derivatives_agree f s hs hz hf

  have hodd :=
    even_odd_derivatives_zero f heven

  have h1 :
      iteratedDerivWithin 1 f s 0 = 0 := by
    rw [hd 1 (by norm_num)]
    exact hodd.1

  have h3 :
      iteratedDerivWithin 3 f s 0 = 0 := by
    rw [hd 3 (by norm_num)]
    exact hodd.2

  rw [taylor_cubic_reduction f s h h1 h3]
  rw [hd 2 (by norm_num)]

end BakerSpherical.UniformTaylor

#print axioms
  BakerSpherical.UniformTaylor.even_taylor_polynomial