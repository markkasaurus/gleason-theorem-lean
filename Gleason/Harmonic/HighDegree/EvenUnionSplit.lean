import Gleason.Harmonic.HighDegree.HighEvenUnion

noncomputable section

open Complex InnerProductSpace

def evenUnionHarmonicPolyHomogeneousImageSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  ⨆ N : ℕ, evenBoundedHarmonicPolyHomogeneousImageSubmodule N

def highEvenUnionHarmonicPolyHomogeneousImageSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  ⨆ N : ℕ, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N

theorem lowHarmonicPolyHomogeneousImageSubmodule_le_evenUnionHarmonicPolyHomogeneousImageSubmodule :
    lowHarmonicPolyHomogeneousImageSubmodule ≤
      evenUnionHarmonicPolyHomogeneousImageSubmodule := by
  intro f hf
  have h1 : 1 ≤ (1 : ℕ) := by norm_num
  exact Submodule.mem_iSup_of_mem 1 <|
    lowHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
      h1 hf

theorem highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_evenUnionHarmonicPolyHomogeneousImageSubmodule :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule ≤
      evenUnionHarmonicPolyHomogeneousImageSubmodule := by
  refine iSup_le ?_
  intro N
  exact
    (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
      N).trans <|
      le_iSup (fun N : ℕ => evenBoundedHarmonicPolyHomogeneousImageSubmodule N) N

theorem evenUnionHarmonicPolyHomogeneousImageSubmodule_eq_low_sup_highEvenUnion :
    evenUnionHarmonicPolyHomogeneousImageSubmodule =
      lowHarmonicPolyHomogeneousImageSubmodule ⊔
        highEvenUnionHarmonicPolyHomogeneousImageSubmodule := by
  apply le_antisymm
  · simpa [evenUnionHarmonicPolyHomogeneousImageSubmodule,
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule] using
      iSup_evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_low_sup_iSup_highEvenBounded
  · refine sup_le ?_ ?_
    · exact lowHarmonicPolyHomogeneousImageSubmodule_le_evenUnionHarmonicPolyHomogeneousImageSubmodule
    · exact highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_evenUnionHarmonicPolyHomogeneousImageSubmodule

theorem lowHarmonicPolyHomogeneousImageSubmodule_inf_highEvenUnion_eq_bot :
    lowHarmonicPolyHomogeneousImageSubmodule ⊓
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule = ⊥ := by
  simpa [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] using
    lowHarmonicPolyHomogeneousImageSubmodule_inf_iSup_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_bot

theorem highEvenUnionHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  simpa [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] using
    iSup_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot

theorem evenUnionHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_low :
    evenUnionHarmonicPolyHomogeneousImageSubmodule ⊓ continuousSphereFrameSubmodule =
      lowHarmonicPolyHomogeneousImageSubmodule := by
  apply le_antisymm
  · intro f hf
    rw [evenUnionHarmonicPolyHomogeneousImageSubmodule_eq_low_sup_highEvenUnion] at hf
    rcases Submodule.mem_inf.mp hf with ⟨hf_even, hf_frame⟩
    rcases Submodule.mem_sup.mp hf_even with ⟨f₁, hf₁, f₂, hf₂, rfl⟩
    have hlow_frame : lowHarmonicPolyHomogeneousImageSubmodule ≤ continuousSphereFrameSubmodule := by
      exact lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereFrameSubmodule
    have hf₁_frame' : f₁ ∈ continuousSphereFrameSubmodule := hlow_frame hf₁
    have hf₂_frame : f₂ ∈ continuousSphereFrameSubmodule := by
      have : f₂ = (f₁ + f₂) - f₁ := by abel
      rw [this]
      exact Submodule.sub_mem _ hf_frame hf₁_frame'
    have hf₂_bot :
        f₂ ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ⊓
          continuousSphereFrameSubmodule := ⟨hf₂, hf₂_frame⟩
    rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot] at hf₂_bot
    have hf₂_zero : f₂ = 0 := by simpa using hf₂_bot
    simpa [hf₂_zero] using hf₁
  · intro f hf
    exact ⟨lowHarmonicPolyHomogeneousImageSubmodule_le_evenUnionHarmonicPolyHomogeneousImageSubmodule hf,
      lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereFrameSubmodule hf⟩
