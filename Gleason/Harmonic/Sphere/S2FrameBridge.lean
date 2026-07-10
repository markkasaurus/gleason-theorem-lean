import Gleason.Harmonic.Sphere.SphericalBridge
import Gleason.Harmonic.Fischer.FischerFrameIntersection
import SphericalHarmonics.LowDegree

noncomputable section

open Complex InnerProductSpace
open scoped BigOperators

namespace GleasonS2Bridge

open SphericalHarmonics

/-- The transported continuous frame-function submodule on `S²`. -/
def continuousSphereFrameSubmoduleS2 : Submodule ℝ C(S2, ℝ) :=
  continuousSphereFrameSubmodule.comap s2Pullback.toLinearMap

/-- The low sector on `S²` relevant for theorem `2.3`. -/
def lowSectorS2 : Submodule ℝ C(S2, ℝ) :=
  sector 0 ⊔ sector 2

@[simp] theorem mem_continuousSphereFrameSubmoduleS2_iff
    (f : C(S2, ℝ)) :
    f ∈ continuousSphereFrameSubmoduleS2 ↔
      s2Pullback f ∈ continuousSphereFrameSubmodule :=
  Iff.rfl

theorem sector_zero_le_continuousSphereFrameSubmoduleS2 :
    sector 0 ≤ continuousSphereFrameSubmoduleS2 := by
  intro f hf
  exact continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereFrameSubmodule
    (s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule hf)

theorem sector_two_le_continuousSphereFrameSubmoduleS2 :
    sector 2 ≤ continuousSphereFrameSubmoduleS2 := by
  intro f hf
  exact continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereFrameSubmodule
    (s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule hf)

theorem lowSectorS2_le_continuousSphereFrameSubmoduleS2 :
    lowSectorS2 ≤ continuousSphereFrameSubmoduleS2 := by
  rw [lowSectorS2]
  exact sup_le sector_zero_le_continuousSphereFrameSubmoduleS2
    sector_two_le_continuousSphereFrameSubmoduleS2

theorem eq_zero_of_mem_sector_and_continuousSphereFrameSubmoduleS2_of_ne_zero_two
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2)
    {f : C(S2, ℝ)}
    (hfS : f ∈ sector n)
    (hfF : f ∈ continuousSphereFrameSubmoduleS2) :
    f = 0 := by
  apply s2Pullback.injective
  refine eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule_and_continuousSphereFrameSubmodule_of_ne_zero_two
    hn0 hn2 ?_ hfF
  rcases hfS with ⟨p, hp, rfl⟩
  exact ⟨p, by
    simpa [harmonicHomogeneousSubmodule_eq_harmonicPolyHomogeneousSubmodule n] using hp, by
      simpa using (s2Pullback_restrictToSphere p).symm⟩

theorem sector_inf_continuousSphereFrameSubmoduleS2_eq_bot_of_ne_zero_two
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    sector n ⊓ continuousSphereFrameSubmoduleS2 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  exact eq_zero_of_mem_sector_and_continuousSphereFrameSubmoduleS2_of_ne_zero_two
    hn0 hn2 hf.1 hf.2

end GleasonS2Bridge
