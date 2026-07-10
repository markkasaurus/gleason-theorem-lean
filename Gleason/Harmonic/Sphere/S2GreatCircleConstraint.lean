import Gleason.Harmonic.Sphere.S2FrameBridge
import Gleason.Harmonic.Sphere.SphericalBridge
import Gleason.Harmonic.GreatCircle.GreatCircleConstraints
import Gleason.Harmonic.GreatCircle.GreatCircleEndpoint

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

/-- The transported continuous great-circle constraint submodule on `S²`. -/
def continuousSphereGreatCircleConstraintSubmoduleS2 : Submodule ℝ C(S2, ℝ) :=
  continuousSphereGreatCircleConstraintSubmodule.comap s2Pullback.toLinearMap

@[simp] theorem mem_continuousSphereGreatCircleConstraintSubmoduleS2_iff
    (f : C(S2, ℝ)) :
    f ∈ continuousSphereGreatCircleConstraintSubmoduleS2 ↔
      s2Pullback f ∈ continuousSphereGreatCircleConstraintSubmodule :=
  Iff.rfl

theorem continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2 :
    continuousSphereFrameSubmoduleS2 ≤ continuousSphereGreatCircleConstraintSubmoduleS2 := by
  intro f hf
  exact continuousSphereFrameSubmodule_le_continuousSphereGreatCircleConstraintSubmodule hf

theorem sector_zero_le_continuousSphereGreatCircleConstraintSubmoduleS2 :
    sector 0 ≤ continuousSphereGreatCircleConstraintSubmoduleS2 := by
  intro f hf
  exact continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereGreatCircleConstraintSubmodule
    (s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule hf)

theorem sector_two_le_continuousSphereGreatCircleConstraintSubmoduleS2 :
    sector 2 ≤ continuousSphereGreatCircleConstraintSubmoduleS2 := by
  intro f hf
  exact continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereGreatCircleConstraintSubmodule
    (s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule hf)

theorem lowSectorS2_le_continuousSphereGreatCircleConstraintSubmoduleS2 :
    lowSectorS2 ≤ continuousSphereGreatCircleConstraintSubmoduleS2 := by
  rw [lowSectorS2]
  exact sup_le sector_zero_le_continuousSphereGreatCircleConstraintSubmoduleS2
    sector_two_le_continuousSphereGreatCircleConstraintSubmoduleS2

end GleasonS2Bridge
