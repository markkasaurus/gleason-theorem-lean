import Gleason.Harmonic.Sphere.S2PointConstraintBridge
import Gleason.Harmonic.Sphere.S2FrameRotation
import Gleason.Harmonic.Sphere.SphericalSectorEquivariance

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

theorem continuousSphereGreatCirclePointConstraintSubmoduleS2_invariant_under_compContinuous
    (ρ : Rotation) :
    continuousSphereGreatCirclePointConstraintSubmoduleS2 ≤
      continuousSphereGreatCirclePointConstraintSubmoduleS2.comap (Rotation.compContinuous ρ) := by
  simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
    using continuousSphereFrameSubmoduleS2_invariant_under_compContinuous ρ

/-- The image of the transported point-constraint submodule under the continuous degree-`n`
sector projector. -/
def pointConstraintSectorImageSubmoduleS2 (n : ℕ) : Submodule ℝ C(S2, ℝ) :=
  Submodule.map (ambientSectorProjectionContinuous n).toLinearMap
    continuousSphereGreatCirclePointConstraintSubmoduleS2

theorem pointConstraintSectorImageSubmoduleS2_le_sector (n : ℕ) :
    pointConstraintSectorImageSubmoduleS2 n ≤ sector n := by
  intro f hf
  rcases hf with ⟨g, -, rfl⟩
  exact sectorProjectionContinuous_apply_mem n g

theorem pointConstraintSectorImageSubmoduleS2_invariant_under_compContinuous
    (ρ : Rotation) (n : ℕ) :
    pointConstraintSectorImageSubmoduleS2 n ≤
      (pointConstraintSectorImageSubmoduleS2 n).comap (Rotation.compContinuous ρ) := by
  intro f hf
  rcases hf with ⟨g, hg, rfl⟩
  refine ⟨Rotation.compContinuous ρ g, ?_, ?_⟩
  · exact continuousSphereGreatCirclePointConstraintSubmoduleS2_invariant_under_compContinuous
      ρ hg
  · simpa using (ambientSectorProjectionContinuous_compContinuous ρ n g)

end GleasonS2Bridge
