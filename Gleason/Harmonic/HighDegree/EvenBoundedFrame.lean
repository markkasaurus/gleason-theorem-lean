import Gleason.Harmonic.HighDegree.EvenBoundedSplit

noncomputable section

open Complex InnerProductSpace

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_low_of_one_le
    {N : ℕ} (hN : 1 ≤ N) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N ⊓ continuousSphereFrameSubmodule =
      lowHarmonicPolyHomogeneousImageSubmodule :=
  evenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_low hN

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_low_or_zero
    (N : ℕ) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N ⊓ continuousSphereFrameSubmodule =
      if N = 0 then harmonicPolyHomogeneousImageSubmodule 0
      else lowHarmonicPolyHomogeneousImageSubmodule := by
  by_cases hN : N = 0
  · subst hN
    simp [evenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_zero]
  · have hN1 : 1 ≤ N := by omega
    simp [hN, evenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_low hN1]

theorem lowHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    lowHarmonicPolyHomogeneousImageSubmodule ≤
      evenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_low_sup_highEven hN]
  exact le_sup_left

