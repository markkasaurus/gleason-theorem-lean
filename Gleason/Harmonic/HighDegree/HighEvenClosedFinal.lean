import Gleason.Harmonic.HighDegree.HighEvenFullWitness
import Gleason.Harmonic.HighDegree.HighEvenInduction
import Gleason.Continuity.Auxiliary.ClosedFrame

noncomputable section

open Complex InnerProductSpace

theorem eq_bot_of_isClosed_of_rotationInvariant_of_le_highEvenBounded_of_le_frame
    {N : ℕ} {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGbounded : G ≤ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hGframe : G ≤ continuousSphereFrameSubmodule)
    (hGne : G ≠ ⊥) :
    G = ⊥ := by
  by_contra hGbot
  rcases exists_nonzero_mem_lowHarmonicPolyHomogeneousImageSubmodule_with_even_and_harmonic_repr_of_isClosed_of_rotationInvariant_of_le_highEvenBounded_of_le_frame
      hGclosed hGrot hGbounded hGframe hGne with
    ⟨g, q, p, hgG, hgne, hgz, hgLow, hqdeg, hqEval, hqEven, hpdeg, hpΔ, hpEval⟩
  have hgHigh : g ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    hGbounded hgG
  have hzero :
      g = 0 :=
    eq_zero_of_mem_lowHarmonicPolyHomogeneousImageSubmodule_and_mem_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
      hgLow hgHigh
  exact hgne hzero

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot
    (N : ℕ) :
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ⊓ continuousSphereFrameSubmodule = ⊥ := by
  let G : Submodule ℝ C(spherePoint3, ℝ) :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ⊓ continuousSphereFrameSubmodule
  have hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)) := by
    simpa [G] using
      (isClosed_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).inter
        isClosed_continuousSphereFrameSubmodule
  have hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G := by
    intro e
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨?_, continuousSphereFrameSubmodule_invariant_under_spherePrecomp e hg.2⟩
      have hmap :
          spherePrecomp e g ∈
            (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).map
              (spherePrecompLinearEquiv e).toLinearMap := by
        exact ⟨g, hg.1, rfl⟩
      simpa [highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_invariant_under_spherePrecomp N e]
        using hmap
    · intro hf
      refine ⟨spherePrecomp e.symm f, ?_, ?_⟩
      · refine ⟨?_, continuousSphereFrameSubmodule_invariant_under_spherePrecomp e.symm hf.2⟩
        have hmap :
            spherePrecomp e.symm f ∈
              (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).map
                (spherePrecompLinearEquiv e.symm).toLinearMap := by
          exact ⟨f, hf.1, rfl⟩
        simpa [highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_invariant_under_spherePrecomp N e.symm]
          using hmap
      · ext x
        simp [spherePrecompLinearEquiv, spherePrecomp]
  have hGbounded : G ≤ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N := inf_le_left
  have hGframe : G ≤ continuousSphereFrameSubmodule := inf_le_right
  by_cases hGne : G = ⊥
  · exact hGne
  · exact
      eq_bot_of_isClosed_of_rotationInvariant_of_le_highEvenBounded_of_le_frame
        hGclosed hGrot hGbounded hGframe hGne
