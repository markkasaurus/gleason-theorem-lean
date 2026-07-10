import Gleason.Harmonic.Fischer.FischerRotationGeneral
import Gleason.Harmonic.Fischer.FischerNorthOrbit
import Gleason.Continuity.Auxiliary.FrameClosedTransfer
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

open Complex InnerProductSpace

theorem harmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot_of_gt_two
    {n : ℕ} (hn : 2 < n) :
    harmonicPolyHomogeneousImageSubmodule n ⊓ continuousSphereFrameSubmodule = ⊥ := by
  let G : Submodule ℝ C(spherePoint3, ℝ) :=
    harmonicPolyHomogeneousImageSubmodule n ⊓ continuousSphereFrameSubmodule
  have hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)) := by
    letI : FiniteDimensional ℝ ↥G := by
      exact Submodule.finiteDimensional_of_le (show G ≤ harmonicPolyHomogeneousImageSubmodule n by
        exact inf_le_left)
    exact Submodule.closed_of_finiteDimensional G
  have hGrot :
      ∀ e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3,
        G.map (spherePrecompLinearEquiv e).toLinearMap = G := by
    intro e
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨spherePrecomp_mem_harmonicPolyHomogeneousImageSubmodule e hg.1,
        continuousSphereFrameSubmodule_invariant_under_spherePrecomp e hg.2⟩
    · intro hf
      refine ⟨spherePrecomp e.symm f, ?_, ?_⟩
      · exact ⟨spherePrecomp_mem_harmonicPolyHomogeneousImageSubmodule e.symm hf.1,
          continuousSphereFrameSubmodule_invariant_under_spherePrecomp e.symm hf.2⟩
      · ext x
        simp [spherePrecompLinearEquiv, spherePrecomp]
  have hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n := by
    calc
      G ≤ harmonicPolyHomogeneousImageSubmodule n := inf_le_left
      _ ≤ continuousHarmonicSphereDegreeSubmodule n :=
        harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule n
  have hGframe : G ≤ continuousSphereFrameSubmodule := inf_le_right
  have hbot : G = ⊥ :=
    eq_bot_of_isClosed_of_rotationInvariant_of_le_gt_two_degree_of_le_frame
      hn hGclosed hGrot hGdeg hGframe
  exact hbot

theorem harmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot_of_ne_zero_two
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    harmonicPolyHomogeneousImageSubmodule n ⊓ continuousSphereFrameSubmodule = ⊥ := by
  let G : Submodule ℝ C(spherePoint3, ℝ) :=
    harmonicPolyHomogeneousImageSubmodule n ⊓ continuousSphereFrameSubmodule
  have hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)) := by
    letI : FiniteDimensional ℝ ↥G := by
      exact Submodule.finiteDimensional_of_le (show G ≤ harmonicPolyHomogeneousImageSubmodule n by
        exact inf_le_left)
    exact Submodule.closed_of_finiteDimensional G
  have hGrot :
      ∀ e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3,
        G.map (spherePrecompLinearEquiv e).toLinearMap = G := by
    intro e
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨spherePrecomp_mem_harmonicPolyHomogeneousImageSubmodule e hg.1,
        continuousSphereFrameSubmodule_invariant_under_spherePrecomp e hg.2⟩
    · intro hf
      refine ⟨spherePrecomp e.symm f, ?_, ?_⟩
      · exact ⟨spherePrecomp_mem_harmonicPolyHomogeneousImageSubmodule e.symm hf.1,
          continuousSphereFrameSubmodule_invariant_under_spherePrecomp e.symm hf.2⟩
      · ext x
        simp [spherePrecompLinearEquiv, spherePrecomp]
  have hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n := by
    calc
      G ≤ harmonicPolyHomogeneousImageSubmodule n := inf_le_left
      _ ≤ continuousHarmonicSphereDegreeSubmodule n :=
        harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule n
  have hGframe : G ≤ continuousSphereFrameSubmodule := inf_le_right
  have hbot : G = ⊥ :=
    eq_bot_of_isClosed_of_rotationInvariant_of_le_ne_zero_two_degree_of_le_frame
      hn0 hn2 hGclosed hGrot hGdeg hGframe
  exact hbot

theorem eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule_and_continuousSphereFrameSubmodule_of_gt_two
    {n : ℕ} (hn : 2 < n)
    {f : C(spherePoint3, ℝ)}
    (hfH : f ∈ harmonicPolyHomogeneousImageSubmodule n)
    (hfF : f ∈ continuousSphereFrameSubmodule) :
    f = 0 := by
  have hf : f ∈ harmonicPolyHomogeneousImageSubmodule n ⊓ continuousSphereFrameSubmodule :=
    ⟨hfH, hfF⟩
  simpa [harmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot_of_gt_two hn]
    using hf

theorem eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule_and_continuousSphereFrameSubmodule_of_ne_zero_two
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2)
    {f : C(spherePoint3, ℝ)}
    (hfH : f ∈ harmonicPolyHomogeneousImageSubmodule n)
    (hfF : f ∈ continuousSphereFrameSubmodule) :
    f = 0 := by
  have hf : f ∈ harmonicPolyHomogeneousImageSubmodule n ⊓ continuousSphereFrameSubmodule :=
    ⟨hfH, hfF⟩
  simpa [harmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot_of_ne_zero_two hn0 hn2]
    using hf

theorem harmonicPolyHomogeneousImageSubmodule_zero_le_continuousSphereFrameSubmodule :
    harmonicPolyHomogeneousImageSubmodule 0 ≤ continuousSphereFrameSubmodule := by
  calc
    harmonicPolyHomogeneousImageSubmodule 0 ≤ continuousHarmonicSphereDegreeSubmodule 0 :=
      harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule 0
    _ ≤ continuousSphereFrameSubmodule :=
      continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereFrameSubmodule

theorem harmonicPolyHomogeneousImageSubmodule_two_le_continuousSphereFrameSubmodule :
    harmonicPolyHomogeneousImageSubmodule 2 ≤ continuousSphereFrameSubmodule := by
  calc
    harmonicPolyHomogeneousImageSubmodule 2 ≤ continuousHarmonicSphereDegreeSubmodule 2 :=
      harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule 2
    _ ≤ continuousSphereFrameSubmodule :=
      continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereFrameSubmodule
