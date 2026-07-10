import Gleason.Harmonic.Sectors.BoundedHarmonicRepresentation
import Gleason.Harmonic.HighDegree.EvenLowConcrete
import Gleason.Harmonic.HighDegree.HighEvenBoundedClosure

noncomputable section

open Complex InnerProductSpace

theorem exists_nonzero_mem_lowHarmonicPolyHomogeneousImageSubmodule_with_even_and_harmonic_repr_of_isClosed_of_rotationInvariant_of_le_highEvenBounded_of_le_frame
    {N : ℕ} {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGbounded : G ≤ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hGframe : G ≤ continuousSphereFrameSubmodule)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ), ∃ q p : MvPolynomial (Fin 3) ℝ,
      g ∈ G ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      g ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
      q ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ (2 * N) ∧
      sphereCoordMvEval q = g ∧
      sphereCoordPolyAntipode q = q ∧
      p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ (2 * N) ∧
      polyLaplacian p = 0 ∧
      sphereCoordMvEval p = g := by
  rcases exists_nonzero_northZonal_even_bounded_mvPolynomial_of_isClosed_of_rotationInvariant_of_le_evenBounded_of_le_frame
      hGclosed hGrot
      ((hGbounded).trans
        (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
          N))
      hGframe hGne with
    ⟨g, q, hgG, hgne, hgz, hqdeg, hqEval, hqEven⟩
  have hgLow :
      g ∈ lowHarmonicPolyHomogeneousImageSubmodule :=
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isNorthZonal_mem_frame_of_mvPolynomial
      (hGframe hgG) hgz hqEval
  have hgBounded : g ∈ boundedHarmonicPolyHomogeneousImageSubmodule (2 * N) := by
    exact
      (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_boundedHarmonicPolyHomogeneousImageSubmodule
        N) (hGbounded hgG)
  rcases exists_harmonic_mvPolynomial_of_mem_boundedHarmonicPolyHomogeneousImageSubmodule hgBounded with
    ⟨p, hpdeg, hpΔ, hpEval⟩
  exact ⟨g, q, p, hgG, hgne, hgz, hgLow, hqdeg, hqEval, hqEven, hpdeg, hpΔ, hpEval⟩
