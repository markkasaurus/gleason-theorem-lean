import Gleason.Harmonic.HighDegree.EvenBoundedPolyDegree
import Gleason.Harmonic.Zonal.NorthZonalClosed

noncomputable section

open Complex InnerProductSpace

theorem exists_nonzero_northZonal_even_mvPolynomial_of_isClosed_of_rotationInvariant_of_le_evenBounded_of_le_frame
    {N : ℕ} {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGbounded : G ≤ evenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (_hGframe : G ≤ continuousSphereFrameSubmodule)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ), ∃ p : MvPolynomial (Fin 3) ℝ,
      g ∈ G ∧ g ≠ 0 ∧ IsNorthZonal g ∧ sphereCoordMvEval p = g ∧ sphereCoordPolyAntipode p = p := by
  rcases exists_nonzero_northZonal_mem_of_isClosed_of_rotationInvariant hGclosed hGrot hGne with
    ⟨g, hgG, hgne, hgz⟩
  rcases exists_even_mvPolynomial_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule
      (hGbounded hgG) with ⟨p, hpEval, hpEven⟩
  exact ⟨g, p, hgG, hgne, hgz, hpEval, hpEven⟩

theorem exists_nonzero_northZonal_even_bounded_mvPolynomial_of_isClosed_of_rotationInvariant_of_le_evenBounded_of_le_frame
    {N : ℕ} {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGbounded : G ≤ evenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (_hGframe : G ≤ continuousSphereFrameSubmodule)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ), ∃ p : MvPolynomial (Fin 3) ℝ,
      g ∈ G ∧ g ≠ 0 ∧ IsNorthZonal g ∧
      p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ (2 * N) ∧
      sphereCoordMvEval p = g ∧ sphereCoordPolyAntipode p = p := by
  rcases exists_nonzero_northZonal_mem_of_isClosed_of_rotationInvariant hGclosed hGrot hGne with
    ⟨g, hgG, hgne, hgz⟩
  rcases exists_even_mvPolynomial_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule_degree
      (hGbounded hgG) with ⟨p, hpdeg, hpEval, hpEven⟩
  exact ⟨g, p, hgG, hgne, hgz, hpdeg, hpEval, hpEven⟩
