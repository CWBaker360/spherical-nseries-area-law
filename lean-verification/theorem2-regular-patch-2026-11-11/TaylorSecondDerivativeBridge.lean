import Mathlib

namespace BakerSpherical.UniformTaylor

/--
The second iterated derivative is the
ordinary derivative taken twice.
-/
theorem second_iterated_derivative
    (f : ℝ → ℝ) :
    iteratedDeriv 2 f 0 =
      deriv (deriv f) 0 := by
  change iteratedDeriv (1 + 1) f 0 =
    deriv (deriv f) 0
  rw [iteratedDeriv_succ', iteratedDeriv_one]

end BakerSpherical.UniformTaylor

#print axioms
  BakerSpherical.UniformTaylor.second_iterated_derivative