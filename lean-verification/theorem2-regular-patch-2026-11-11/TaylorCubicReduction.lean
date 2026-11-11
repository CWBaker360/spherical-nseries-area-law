import Mathlib

namespace BakerSpherical.UniformTaylor

/--
A cubic Taylor polynomial reduces to its even
terms when the first and third within-derivatives
at zero vanish.
-/
theorem taylor_cubic_reduction
    (f : ℝ → ℝ) (s : Set ℝ) (h : ℝ)
    (h1 : iteratedDerivWithin 1 f s 0 = 0)
    (h3 : iteratedDerivWithin 3 f s 0 = 0) :
    taylorWithinEval f 3 s 0 h =
      f 0 + (iteratedDerivWithin 2 f s 0) * h ^ 2 / 2 := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ]
  simp [h1, h3, iteratedDerivWithin_zero]
  ring

end BakerSpherical.UniformTaylor

#print axioms
  BakerSpherical.UniformTaylor.taylor_cubic_reduction