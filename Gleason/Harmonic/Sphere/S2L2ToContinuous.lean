import Gleason.Harmonic.Sphere.S2L2Low

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

theorem continuousSphereFrameSubmoduleS2_le_lowSectorS2_of_sector_intersections_bot
    (hbot : ∀ n : ℕ, n ≠ 0 → n ≠ 2 →
      continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n = ⊥) :
    continuousSphereFrameSubmoduleS2 ≤ lowSectorS2 := by
  intro f hf
  have hL2 : continuousToLp f ∈ lowSectorL2S2 := by
    rw [← continuousSphereFrameClosedSubmoduleL2S2_eq_low_of_sector_intersections_bot hbot]
    exact subset_closure ⟨f, hf, rfl⟩
  rw [lowSectorL2S2] at hL2
  rcases Submodule.mem_sup.mp hL2 with ⟨x0, hx0, x2, hx2, hsum⟩
  rcases sectorToSectorL2_surjective 0 ⟨x0, hx0⟩ with ⟨g0, hg0⟩
  rcases sectorToSectorL2_surjective 2 ⟨x2, hx2⟩ with ⟨g2, hg2⟩
  rw [Subtype.ext_iff] at hg0 hg2
  dsimp at hg0 hg2
  have hfg : f = g0 + g2 := ContinuousMap.toLp_injective rotationMeasure <| by
    calc
      continuousToLp f = x0 + x2 := by simpa using hsum.symm
      _ = ↑((sectorToSectorL2 0) g0) + ↑((sectorToSectorL2 2) g2) := by
            rw [hg0, hg2]
      _ = continuousToLp (g0 + g2) := by
            simp [sectorToSectorL2]
  rw [hfg, lowSectorS2]
  exact Submodule.mem_sup.mpr ⟨g0, g0.property, g2, g2.property, rfl⟩

theorem continuousSphereFrameSubmoduleS2_eq_lowSectorS2_of_sector_intersections_bot
    (hbot : ∀ n : ℕ, n ≠ 0 → n ≠ 2 →
      continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n = ⊥) :
    continuousSphereFrameSubmoduleS2 = lowSectorS2 := by
  refine le_antisymm
    (continuousSphereFrameSubmoduleS2_le_lowSectorS2_of_sector_intersections_bot hbot)
    lowSectorS2_le_continuousSphereFrameSubmoduleS2

end GleasonS2Bridge
