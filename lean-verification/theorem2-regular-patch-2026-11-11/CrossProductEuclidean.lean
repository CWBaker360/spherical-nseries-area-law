import Mathlib
import CrossProductContinuous

namespace BakerSpherical.CrossContinuous

/-- Standard Euclidean three-space with its inner product. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The canonical continuous linear equivalence to coordinate functions. -/
noncomputable def coordEquiv :
    E3 ≃L[ℝ] Vec3 :=
  EuclideanSpace.equiv (Fin 3) ℝ

/-- Cross product expressed in Euclidean three-space. -/
noncomputable def crossEAt (u : E3) : E3 →L[ℝ] E3 :=
  coordEquiv.symm.toContinuousLinearMap.comp
    ((crossB (coordEquiv u)).comp
      coordEquiv.toContinuousLinearMap)

/-- The Euclidean cross product is alternating. -/
theorem crossEAt_self (u : E3) :
    crossEAt u u = 0 := by
  simp [crossEAt, crossB_self]

end BakerSpherical.CrossContinuous

#print axioms BakerSpherical.CrossContinuous.crossEAt_self