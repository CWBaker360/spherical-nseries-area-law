import Mathlib

namespace BakerSpherical.UniformTaylor

/--
A continuous vector-valued function on a nonempty
compact set has one finite uniform norm bound.

The bound M is constructed from compactness;
it is not supplied as a hypothesis.
-/
theorem compact_uniform_norm_bound
    {X E : Type*}
    [TopologicalSpace X]
    [NormedAddCommGroup E]
    (K : Set X)
    (hK : IsCompact K)
    (hne : K.Nonempty)
    (D : X → E)
    (hD : ContinuousOn D K) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ K, ‖D x‖ ≤ M := by
  obtain ⟨x, hx, hmax⟩ :=
    hK.exists_isMaxOn hne hD.norm
  refine ⟨‖D x‖, norm_nonneg _, ?_⟩
  intro y hy
  exact hmax hy

end BakerSpherical.UniformTaylor

#print axioms
  BakerSpherical.UniformTaylor.compact_uniform_norm_bound