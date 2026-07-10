import Gleason.Harmonic.HighDegree.EvenLowConcrete
import Gleason.Harmonic.HighDegree.HighEvenFullWitness

noncomputable section

open Complex InnerProductSpace

theorem exists_low_harmonic_mvPolynomial_of_mem_lowHarmonicPolyHomogeneousImageSubmodule
    {g : C(spherePoint3, ℝ)}
    (hg : g ∈ lowHarmonicPolyHomogeneousImageSubmodule) :
    ∃ r : MvPolynomial (Fin 3) ℝ,
      r ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ 2 ∧
      polyLaplacian r = 0 ∧
      sphereCoordMvEval r = g := by
  rcases Submodule.mem_sup.mp hg with ⟨g0, hg0, g2, hg2, rfl⟩
  rcases hg0 with ⟨p0, hp0, hp0Eval⟩
  rcases hg2 with ⟨p2, hp2, hp2Eval⟩
  refine ⟨p0 + p2, ?_, ?_, ?_⟩
  · refine Submodule.add_mem _ ?_ ?_
    · exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := 2) p0).2 <|
        le_trans hp0.1.totalDegree_le (by omega)
    · exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := 2) p2).2 <|
        le_trans hp2.1.totalDegree_le (by omega)
  · rw [LinearMap.map_add]
    rw [show polyLaplacian p0 = 0 by simpa [harmonicPolyHomogeneousSubmodule, LinearMap.mem_ker] using hp0.2]
    rw [show polyLaplacian p2 = 0 by simpa [harmonicPolyHomogeneousSubmodule, LinearMap.mem_ker] using hp2.2]
    simp
  · change sphereCoordMvEval.toLinearMap (p0 + p2) = g0 + g2
    rw [LinearMap.map_add, hp0Eval, hp2Eval]

theorem exists_zero_boundary_harmonic_difference_of_mem_highEvenBounded_and_frame_nonzero
    {N : ℕ} {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGbounded : G ≤ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hGframe : G ≤ continuousSphereFrameSubmodule)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ), ∃ p r : MvPolynomial (Fin 3) ℝ,
      g ∈ G ∧
      g ≠ 0 ∧
      p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ (2 * N) ∧
      polyLaplacian p = 0 ∧
      r ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ 2 ∧
      polyLaplacian r = 0 ∧
      sphereCoordMvEval p = g ∧
      sphereCoordMvEval r = g ∧
      polyLaplacian (p - r) = 0 ∧
      sphereCoordMvEval (p - r) = 0 := by
  rcases
    exists_nonzero_mem_lowHarmonicPolyHomogeneousImageSubmodule_with_even_and_harmonic_repr_of_isClosed_of_rotationInvariant_of_le_highEvenBounded_of_le_frame
      hGclosed hGrot hGbounded hGframe hGne with
    ⟨g, q, p, hgG, hgne, hgz, hgLow, hqdeg, hqEval, hqEven, hpdeg, hpΔ, hpEval⟩
  rcases exists_low_harmonic_mvPolynomial_of_mem_lowHarmonicPolyHomogeneousImageSubmodule hgLow with
    ⟨r, hrdeg, hrΔ, hrEval⟩
  refine ⟨g, p, r, hgG, hgne, hpdeg, hpΔ, hrdeg, hrΔ, hpEval, hrEval, ?_, ?_⟩
  · rw [LinearMap.map_sub, hpΔ, hrΔ]
    simp
  · rw [map_sub, hpEval, hrEval]
    simp
