import Gleason.Harmonic.Sphere.S2PointConstraintRotation
import Gleason.Harmonic.Sphere.S2NorthZonalBridge
import Gleason.Harmonic.Zonal.NorthOrbitAverage
import Gleason.Harmonic.Sphere.S2ExceptionalSectorReduction
import SphericalHarmonics.NorthAxisAverageSector

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics
open MeasureTheory intervalIntegral

theorem s2Pullback_northAxisAverage (f : C(S2, ℝ)) :
    s2Pullback (northAxisAverage f) = northOrbitAverage (s2Pullback f) := by
  ext x
  simp [s2Pullback_apply, northAxisAverage_apply, northOrbitAverage_apply]
  congr 2
  funext t
  have hrot :
      (rotation01 t).toSphereEquiv.symm (spherePoint3ToS2 x) =
        spherePoint3ToS2 (sphereMap (northRotation t) x) := by
    simpa [spherePoint3Rotate] using
      congrArg spherePoint3ToS2 (spherePoint3Rotate_rotation01 t x)
  exact congrArg f hrot

theorem northAxisAverage_mem_continuousSphereGreatCirclePointConstraintSubmoduleS2
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    northAxisAverage f ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 := by
  rw [mem_continuousSphereGreatCirclePointConstraintSubmoduleS2_iff, s2Pullback_northAxisAverage]
  exact northOrbitAverage_mem_continuousSphereGreatCirclePointConstraintSubmodule
    ((mem_continuousSphereGreatCirclePointConstraintSubmoduleS2_iff f).1 hf)

theorem ambientSectorProjectionContinuous_northAxisAverage
    (n : ℕ) (f : C(S2, ℝ)) :
    ambientSectorProjectionContinuous n (northAxisAverage f) =
      northAxisAverage (ambientSectorProjectionContinuous n f) := by
  let A : C(S2, ℝ) →L[ℝ] C(S2, ℝ) := ambientSectorProjectionContinuous n
  have hcomm :=
    (ContinuousLinearMap.intervalIntegral_comp_comm A
      (northRotationOrbit_intervalIntegrableS2 f)).symm
  calc
    ambientSectorProjectionContinuous n (northAxisAverage f)
        = ((2 * Real.pi)⁻¹ : ℝ) •
            A (∫ t in 0..2 * Real.pi, Rotation.compContinuous (rotation01 t) f) := by
              simp [northAxisAverage, A]
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
          ∫ t in 0..2 * Real.pi, A (Rotation.compContinuous (rotation01 t) f) := by
            rw [hcomm]
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
          ∫ t in 0..2 * Real.pi,
            Rotation.compContinuous (rotation01 t) (ambientSectorProjectionContinuous n f) := by
              congr 2
              funext t
              exact ambientSectorProjectionContinuous_compContinuous (rotation01 t) n f
    _ = northAxisAverage (ambientSectorProjectionContinuous n f) := by
          simp [northAxisAverage]

theorem exists_northFixed_witness_of_mem_pointConstraintSectorImageSubmoduleS2
    {n : ℕ} {u : C(S2, ℝ)}
    (hu : u ∈ pointConstraintSectorImageSubmoduleS2 n)
    (hufix : u ∈ northFixedSubmodule) :
    ∃ g : C(S2, ℝ),
      g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
      g ∈ northFixedSubmodule ∧
      ambientSectorProjectionContinuous n g = u := by
  rcases hu with ⟨f, hf, hfu⟩
  refine ⟨northAxisAverage f, ?_, ?_, ?_⟩
  · exact northAxisAverage_mem_continuousSphereGreatCirclePointConstraintSubmoduleS2 hf
  · exact northAxisAverage_mem_northFixedSubmodule f
  · calc
      ambientSectorProjectionContinuous n (northAxisAverage f)
          = northAxisAverage (ambientSectorProjectionContinuous n f) := by
              exact ambientSectorProjectionContinuous_northAxisAverage n f
      _ = northAxisAverage u := by simpa using congrArg northAxisAverage hfu
      _ = u := northAxisAverage_eq_self_of_mem_northFixedSubmodule hufix

theorem exists_northFixed_pointConstraint_witness_of_continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_ne_bot
    {n : ℕ}
    (hne :
      continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n ≠ ⊥) :
    ∃ g : C(S2, ℝ),
      g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
      g ∈ northFixedSubmodule ∧
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) := by
  apply exists_northFixed_witness_of_mem_pointConstraintSectorImageSubmoduleS2
  · exact
      distinguishedZonalSector_mem_pointConstraintSectorImageSubmoduleS2_of_continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_ne_bot
        hne
  · exact (distinguishedZonalSector n).property

end GleasonS2Bridge
