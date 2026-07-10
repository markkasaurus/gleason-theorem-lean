import Gleason.Harmonic.Sphere.S2FrameBridge
import Gleason.Harmonic.Auxiliary.PointConstraintFrame

noncomputable section

open Complex InnerProductSpace
open SphericalHarmonics

namespace GleasonS2Bridge

/-- The transported great-circle point-constraint submodule on `S²`. -/
def continuousSphereGreatCirclePointConstraintSubmoduleS2 : Submodule ℝ C(S2, ℝ) :=
  continuousSphereGreatCirclePointConstraintSubmodule.comap s2Pullback.toLinearMap

@[simp] theorem mem_continuousSphereGreatCirclePointConstraintSubmoduleS2_iff
    (f : C(S2, ℝ)) :
    f ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 ↔
      s2Pullback f ∈ continuousSphereGreatCirclePointConstraintSubmodule :=
  Iff.rfl

theorem continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2 :
    continuousSphereGreatCirclePointConstraintSubmoduleS2 = continuousSphereFrameSubmoduleS2 := by
  ext f
  simp [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]

end GleasonS2Bridge
