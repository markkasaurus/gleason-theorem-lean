import Gleason.Harmonic.Zonal.NorthZonalParity
import Gleason.Harmonic.Zonal.NorthZonalClosed

noncomputable section

open Complex InnerProductSpace

theorem eq_bot_of_isClosed_of_rotationInvariant_of_le_odd_degree_of_le_pointConstraint
    {n : ℕ}
    (hnodd : Odd n)
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n)
    (hGpc : G ≤ continuousSphereGreatCirclePointConstraintSubmodule) :
    G = ⊥ := by
  by_contra hGne
  rcases exists_nonzero_northZonal_mem_of_isClosed_of_rotationInvariant
      hGclosed hGrot hGne with ⟨g, hgG, hgne, hgz⟩
  have hgdeg : g ∈ continuousHarmonicSphereDegreeSubmodule n := hGdeg hgG
  have hgpc' : g ∈ continuousSphereGreatCirclePointConstraintSubmodule := hGpc hgG
  have hgzero :
      g = 0 :=
    eq_zero_of_odd_of_mem_continuousHarmonicSphereDegreeSubmodule_of_northZonal_pointConstraint
      hnodd hgdeg hgpc' hgz
  exact hgne hgzero
