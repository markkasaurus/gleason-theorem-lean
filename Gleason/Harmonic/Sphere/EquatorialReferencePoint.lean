import Gleason.Harmonic.Sphere.SphericalBridge

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

/-- The point of `S2` corresponding to the first ambient coordinate vector. -/
noncomputable def s2E1 : S2 := spherePoint3ToS2 sphereE1

@[simp] theorem s2Pullback_s2E1 (f : C(S2, ℝ)) :
    s2Pullback f sphereE1 = f s2E1 := by
  simp [s2E1, s2Pullback_apply]

end GleasonS2Bridge
