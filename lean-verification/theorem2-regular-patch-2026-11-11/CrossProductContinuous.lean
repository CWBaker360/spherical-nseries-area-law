import Mathlib

namespace BakerSpherical.CrossContinuous

abbrev Vec3 := Fin 3 → ℝ

/-- The real cross product as a continuous bilinear map. -/
noncomputable def crossB :
    Vec3 →L[ℝ] Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap
      (𝕜 := ℝ) (E := Vec3) (F' := Vec3)).toLinearMap.comp
        (crossProduct (R := ℝ)))

/-- The continuous map agrees with the ordinary cross product. -/
theorem crossB_apply (u v : Vec3) :
    crossB u v = crossProduct u v := by
  rfl

/-- The continuous cross product is alternating. -/
theorem crossB_self (u : Vec3) :
    crossB u u = 0 := by
  rw [crossB_apply]
  exact cross_self u

end BakerSpherical.CrossContinuous

#print axioms BakerSpherical.CrossContinuous.crossB_apply
#print axioms BakerSpherical.CrossContinuous.crossB_self