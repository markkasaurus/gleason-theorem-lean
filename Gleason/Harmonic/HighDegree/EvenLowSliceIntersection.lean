import Gleason.Harmonic.HighDegree.EvenLowConcrete
import Gleason.Harmonic.Fischer.FischerFrameIntersection

noncomputable section

open Complex InnerProductSpace

theorem lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereFrameSubmodule :
    lowHarmonicPolyHomogeneousImageSubmodule ≤ continuousSphereFrameSubmodule := by
  refine sup_le ?_ ?_
  · exact harmonicPolyHomogeneousImageSubmodule_zero_le_continuousSphereFrameSubmodule
  · exact harmonicPolyHomogeneousImageSubmodule_two_le_continuousSphereFrameSubmodule

theorem eq_zero_of_mem_lowHarmonicPolyHomogeneousImageSubmodule_and_mem_harmonicPolyHomogeneousImageSubmodule
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2)
    {f : C(spherePoint3, ℝ)}
    (hfLow : f ∈ lowHarmonicPolyHomogeneousImageSubmodule)
    (hfH : f ∈ harmonicPolyHomogeneousImageSubmodule n) :
    f = 0 := by
  exact
    eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule_and_continuousSphereFrameSubmodule_of_ne_zero_two
      hn0 hn2 hfH (lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereFrameSubmodule hfLow)

theorem lowHarmonicPolyHomogeneousImageSubmodule_inf_harmonicPolyHomogeneousImageSubmodule_eq_bot_of_ne_zero_two
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    lowHarmonicPolyHomogeneousImageSubmodule ⊓ harmonicPolyHomogeneousImageSubmodule n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  exact eq_zero_of_mem_lowHarmonicPolyHomogeneousImageSubmodule_and_mem_harmonicPolyHomogeneousImageSubmodule
    hn0 hn2 hf.1 hf.2

theorem lowHarmonicPolyHomogeneousImageSubmodule_inf_harmonicPolyHomogeneousImageSubmodule_eq_bot_of_gt_two
    {n : ℕ} (hn : 2 < n) :
    lowHarmonicPolyHomogeneousImageSubmodule ⊓ harmonicPolyHomogeneousImageSubmodule n = ⊥ := by
  exact lowHarmonicPolyHomogeneousImageSubmodule_inf_harmonicPolyHomogeneousImageSubmodule_eq_bot_of_ne_zero_two
    (by omega) (by omega)
