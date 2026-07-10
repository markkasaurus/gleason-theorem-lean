import Gleason.Harmonic.Sphere.S2L2Frame
import SphericalHarmonics.FiniteDimensional

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

/-- The low `L²` sector on `S²` relevant for theorem `2.3`. -/
def lowSectorL2S2 : Submodule ℝ L2S2Geom :=
  sectorL2 0 ⊔ sectorL2 2

theorem sectorL2_zero_le_continuousSphereFrameClosedSubmoduleL2S2 :
    sectorL2 0 ≤ continuousSphereFrameClosedSubmoduleL2S2.toSubmodule := by
  intro x hx
  rcases sectorToSectorL2_surjective 0 ⟨x, hx⟩ with ⟨f, hfx⟩
  rw [Subtype.ext_iff] at hfx
  dsimp at hfx
  rw [← hfx]
  exact subset_closure ⟨f, sector_zero_le_continuousSphereFrameSubmoduleS2 f.property, rfl⟩

theorem sectorL2_two_le_continuousSphereFrameClosedSubmoduleL2S2 :
    sectorL2 2 ≤ continuousSphereFrameClosedSubmoduleL2S2.toSubmodule := by
  intro x hx
  rcases sectorToSectorL2_surjective 2 ⟨x, hx⟩ with ⟨f, hfx⟩
  rw [Subtype.ext_iff] at hfx
  dsimp at hfx
  rw [← hfx]
  exact subset_closure ⟨f, sector_two_le_continuousSphereFrameSubmoduleS2 f.property, rfl⟩

theorem lowSectorL2S2_le_continuousSphereFrameClosedSubmoduleL2S2 :
    lowSectorL2S2 ≤ continuousSphereFrameClosedSubmoduleL2S2.toSubmodule := by
  rw [lowSectorL2S2]
  exact sup_le sectorL2_zero_le_continuousSphereFrameClosedSubmoduleL2S2
    sectorL2_two_le_continuousSphereFrameClosedSubmoduleL2S2

theorem continuousSphereFrameClosedSubmoduleL2S2_eq_low_of_sector_intersections_bot
    (hbot : ∀ n : ℕ, n ≠ 0 → n ≠ 2 →
      continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n = ⊥) :
    continuousSphereFrameClosedSubmoduleL2S2.toSubmodule = lowSectorL2S2 := by
  have hdecomp :=
    continuousSphereFrameClosedSubmoduleL2S2_eq_topologicalClosure_iSup_inf_sectorL2
  refine le_antisymm ?_ lowSectorL2S2_le_continuousSphereFrameClosedSubmoduleL2S2
  rw [hdecomp]
  refine Submodule.topologicalClosure_minimal
    (s := ⨆ n : ℕ, continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n) ?_ ?_
  · refine iSup_le ?_
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      exact le_trans inf_le_right (by
        rw [lowSectorL2S2]
        exact le_sup_left)
    · by_cases hn2 : n = 2
      · subst hn2
        exact le_trans inf_le_right (by
          rw [lowSectorL2S2]
          exact le_sup_right)
      · have hzero := hbot n hn0 hn2
        rw [hzero]
        exact bot_le
  ·
    have hclosed :
        IsClosed ((sectorL2 0 ⊔ sectorL2 2 : Submodule ℝ L2S2Geom) : Set L2S2Geom) :=
      Submodule.closed_of_finiteDimensional (sectorL2 0 ⊔ sectorL2 2 : Submodule ℝ L2S2Geom)
    simpa [lowSectorL2S2] using hclosed

end GleasonS2Bridge
