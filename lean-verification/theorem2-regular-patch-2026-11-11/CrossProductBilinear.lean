import Mathlib
import CrossProductEuclidean

namespace BakerSpherical.CrossContinuous

/-- The Euclidean cross product is linear in its first argument. -/
noncomputable def crossELinear :
    E3 →ₗ[ℝ] (E3 →L[ℝ] E3) where
  toFun := crossEAt
  map_add' := by
    intro u v
    ext w
    simp [crossEAt, map_add]
  map_smul' := by
    intro a u
    ext w
    simp [crossEAt, map_smul]

/-- The complete real three-dimensional continuous bilinear cross product. -/
noncomputable def crossE :
    E3 →L[ℝ] E3 →L[ℝ] E3 :=
  crossELinear.toContinuousLinearMap

/-- The continuous bilinear cross product agrees with crossEAt. -/
theorem crossE_apply (u v : E3) :
    crossE u v = crossEAt u v := by
  rfl

/-- Alternation required by the smooth-extension theorem. -/
theorem crossE_self (u : E3) :
    crossE u u = 0 := by
  rw [crossE_apply]
  exact crossEAt_self u

end BakerSpherical.CrossContinuous

#print axioms BakerSpherical.CrossContinuous.crossE_apply
#print axioms BakerSpherical.CrossContinuous.crossE_self