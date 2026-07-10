import Gleason.Harmonic.Sphere.S2FrameRotation
import Gleason.Harmonic.Zonal.NorthZonalReduction
import SphericalHarmonics.NorthAxisAverageSector

noncomputable section

open Complex InnerProductSpace

namespace GleasonS2Bridge

open SphericalHarmonics

@[simp] lemma spherePoint3ToS2_val_zero (x : spherePoint3) :
    (spherePoint3ToS2 x : E3) 0 = x.1.fst.re := by
  simpa [e3ToCoord, spherePointCoord] using congrArg Prod.fst (spherePoint3ToS2_apply x)

@[simp] lemma spherePoint3ToS2_val_one (x : spherePoint3) :
    (spherePoint3ToS2 x : E3) 1 = x.1.fst.im := by
  simpa [e3ToCoord, spherePointCoord] using
    congrArg (fun r : ℝ × ℝ × ℝ => r.2.1) (spherePoint3ToS2_apply x)

@[simp] lemma spherePoint3ToS2_val_two (x : spherePoint3) :
    (spherePoint3ToS2 x : E3) 2 = x.1.snd := by
  simpa [e3ToCoord, spherePointCoord] using
    congrArg (fun r : ℝ × ℝ × ℝ => r.2.2) (spherePoint3ToS2_apply x)

@[simp] theorem spherePoint3Rotate_rotation01
    (t : ℝ) (x : spherePoint3) :
    spherePoint3Rotate (rotation01 t) x = sphereMap (northRotation t) x := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  refine Prod.ext ?_ ?_
  · apply Complex.ext <;>
      simp [spherePoint3Rotate, s2ToSpherePoint3, sphereMap, ambientPointOfCoords,
        northRotation_apply,
        rotation01_symm_apply, rot01Point, Complex.exp_mul_I, Complex.mul_re,
        Complex.mul_im]
    · ring
  · simp [spherePoint3Rotate, s2ToSpherePoint3, sphereMap, northRotation_apply,
      ambientPointOfCoords, rotation01_symm_apply, rot01Point]

@[simp] theorem s2Pullback_compContinuous_rotation01
    (t : ℝ) (f : C(S2, ℝ)) :
    s2Pullback (Rotation.compContinuous (rotation01 t) f) =
      spherePrecomp (northRotation t) (s2Pullback f) := by
  ext x
  simp [s2Pullback_apply, spherePrecomp_apply, spherePoint3Rotate_rotation01]

theorem isNorthZonal_s2Pullback_of_mem_northFixedSubmodule
    {f : C(S2, ℝ)} (hf : f ∈ northFixedSubmodule) :
    IsNorthZonal (s2Pullback f) := by
  intro t
  rw [← s2Pullback_compContinuous_rotation01]
  simpa using congrArg s2Pullback ((mem_northFixedSubmodule_iff f).1 hf t)

theorem isNorthZonal_s2Pullback_distinguishedZonalSector
    (n : ℕ) :
    IsNorthZonal
      (s2Pullback
        (((((SphericalHarmonics.distinguishedZonalSector n :
            SphericalHarmonics.northFixedSector n) :
          sector n) : C(S2, ℝ))))) := by
  apply isNorthZonal_s2Pullback_of_mem_northFixedSubmodule
  exact (SphericalHarmonics.distinguishedZonalSector n).property

end GleasonS2Bridge
