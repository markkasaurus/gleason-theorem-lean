import Gleason.Harmonic.HighDegree.EvenBoundedFrame
import Gleason.Harmonic.HighDegree.HighEvenClosedFinal
import Gleason.Harmonic.HighDegree.EvenBoundedMonotonicity
import Mathlib.Order.CompactlyGenerated.Basic

noncomputable section

open Complex InnerProductSpace

theorem disjoint_iSup_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_continuousSphereFrameSubmodule :
    Disjoint
      (⨆ N : ℕ, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
      continuousSphereFrameSubmodule := by
  have hmono : Monotone (fun N : ℕ => highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) := by
    intro N M hNM
    exact highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono hNM
  rw [hmono.directed_le.disjoint_iSup_left]
  intro N
  rw [disjoint_iff]
  exact highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot N

theorem iSup_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot :
    (⨆ N : ℕ, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  exact disjoint_iff.mp
    disjoint_iSup_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_continuousSphereFrameSubmodule

theorem disjoint_lowHarmonicPolyHomogeneousImageSubmodule_iSup_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule :
    Disjoint lowHarmonicPolyHomogeneousImageSubmodule
      (⨆ N : ℕ, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) := by
  have hmono : Monotone (fun N : ℕ => highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) := by
    intro N M hNM
    exact highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono hNM
  rw [hmono.directed_le.disjoint_iSup_right]
  intro N
  rw [disjoint_iff]
  exact lowHarmonicPolyHomogeneousImageSubmodule_inf_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_bot N

theorem lowHarmonicPolyHomogeneousImageSubmodule_inf_iSup_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_bot :
    lowHarmonicPolyHomogeneousImageSubmodule ⊓
      (⨆ N : ℕ, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) = ⊥ := by
  exact disjoint_iff.mp
    disjoint_lowHarmonicPolyHomogeneousImageSubmodule_iSup_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule

set_option maxHeartbeats 800000 in
theorem iSup_evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_low_sup_iSup_highEvenBounded :
    (⨆ N : ℕ, evenBoundedHarmonicPolyHomogeneousImageSubmodule N) ≤
      lowHarmonicPolyHomogeneousImageSubmodule ⊔
        (⨆ N : ℕ, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) := by
  refine iSup_le ?_
  intro N
  by_cases hN : N = 0
  · subst hN
    simpa [evenBoundedHarmonicPolyHomogeneousImageSubmodule] using
      (show harmonicPolyHomogeneousImageSubmodule 0 ≤
        lowHarmonicPolyHomogeneousImageSubmodule ⊔
          (⨆ N : ℕ, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) from
        (show harmonicPolyHomogeneousImageSubmodule 0 ≤ lowHarmonicPolyHomogeneousImageSubmodule from
          le_sup_left).trans le_sup_left)
  · have hN1 : 1 ≤ N := by omega
    rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_low_sup_highEven hN1]
    exact sup_le_sup le_rfl
      (le_iSup (fun N : ℕ => highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) N)

theorem continuousSphereFrameSubmodule_le_low_sup_iSup_highEvenBounded_closure :
    continuousSphereFrameSubmodule ≤
      (lowHarmonicPolyHomogeneousImageSubmodule ⊔
        (⨆ N : ℕ, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)).topologicalClosure := by
  exact continuousSphereFrameSubmodule_le_evenBoundedHarmonicPolyImage_closure.trans <|
    Submodule.topologicalClosure_mono
      iSup_evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_low_sup_iSup_highEvenBounded
