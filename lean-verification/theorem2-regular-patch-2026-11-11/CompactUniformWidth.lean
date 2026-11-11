import Mathlib

namespace BakerSpherical.UniformTaylor

/--
An open neighborhood of a compact parameter patch
at h = 0 contains a uniform closed interval
[-H, H] in the h direction, with H > 0.
-/
theorem compact_uniform_width
    (K : Set (ℝ × ℝ))
    (U : Set ((ℝ × ℝ) × ℝ))
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hzero : ∀ y ∈ K, (y, (0 : ℝ)) ∈ U) :
    ∃ H : ℝ, 0 < H ∧
      ∀ y ∈ K, ∀ h : ℝ,
        |h| ≤ H → (y, h) ∈ U := by

  have hprod : K ×ˢ ({0} : Set ℝ) ⊆ U := by
    intro p hp
    rcases hp with ⟨hy, hh⟩
    have hz : p.2 = 0 := by simpa using hh
    cases p with
    | mk y h =>
      simp only at hy hz
      subst h
      exact hzero y hy

  obtain ⟨A, B, hA, hB, hKA, h0B, hAB⟩ :=
    generalized_tube_lemma hK
      (isCompact_singleton : IsCompact ({0} : Set ℝ))
      hU hprod

  have hzB : (0 : ℝ) ∈ B :=
    h0B (by simp)

  obtain ⟨eps, heps, hball⟩ :=
    (Metric.isOpen_iff.mp hB) 0 hzB

  refine ⟨eps / 2, by positivity, ?_⟩
  intro y hy h hh

  have hlt : |h| < eps := by
    have heps2 : eps / 2 < eps := by linarith
    exact lt_of_le_of_lt hh heps2

  have hmem : h ∈ Metric.ball (0 : ℝ) eps := by
    simpa [Metric.mem_ball, Real.dist_eq] using hlt

  exact hAB ⟨hKA hy, hball hmem⟩

end BakerSpherical.UniformTaylor

#print axioms BakerSpherical.UniformTaylor.compact_uniform_width