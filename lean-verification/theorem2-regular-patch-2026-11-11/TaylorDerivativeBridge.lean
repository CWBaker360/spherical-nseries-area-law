import Mathlib

namespace BakerSpherical.UniformTaylor

/--
For a C4 real function, derivatives within a set
with unique derivatives agree with ordinary
derivatives through order four.
-/
theorem taylor_derivatives_agree
    (f : ℝ → ℝ)
    (s : Set ℝ)
    (hs : UniqueDiffOn ℝ s)
    (hz : (0 : ℝ) ∈ s)
    (hf : ContDiffAt ℝ 4 f 0) :
    (∀ n : ℕ, n ≤ 4 →
      iteratedDerivWithin n f s 0 =
        iteratedDeriv n f 0) := by
  intro n hn
  apply iteratedDerivWithin_eq_iteratedDeriv hs
    (hf.of_le (by exact_mod_cast hn))
    hz

end BakerSpherical.UniformTaylor

#print axioms
  BakerSpherical.UniformTaylor.taylor_derivatives_agree