import Gleason.Harmonic.Zonal.NorthZonalSectorStruct
import Gleason.Harmonic.Zonal.NorthZonalQuadraticQ02

noncomputable section

open Complex InnerProductSpace

theorem eq_bot_or_exists_nonzero_mem_inf_northZonalSubmodule_mem_sup_zero_two_of_isClosed_of_rotationInvariant_of_le_degree_of_le_pointConstraint
    {n : ℕ}
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n)
    (hGpc : G ≤ continuousSphereGreatCirclePointConstraintSubmodule) :
    G = ⊥ ∨
      ∃ g : C(spherePoint3, ℝ),
        g ∈ G ⊓ northZonalSubmodule ∧ g ≠ 0 ∧
          g ∈ continuousHarmonicSphereDegreeSubmodule 0 ⊔
            continuousHarmonicSphereDegreeSubmodule 2 := by
  rcases
      eq_bot_or_exists_nonzero_mem_inf_northZonalSubmodule_mem_quadratic_of_isClosed_of_rotationInvariant_of_le_degree_of_le_pointConstraint
        hGclosed hGrot hGdeg hGpc with hGbot | ⟨g, hgInf, hgne, hgQuad⟩
  · exact Or.inl hGbot
  · right
    refine ⟨g, hgInf, hgne, ?_⟩
    exact mem_sup_zero_two_of_isNorthZonal_mem_quadratic_pointConstraint
      hgQuad (hGpc hgInf.1) ((mem_northZonalSubmodule_iff g).1 hgInf.2)
