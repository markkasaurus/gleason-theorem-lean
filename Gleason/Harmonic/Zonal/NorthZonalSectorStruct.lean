import Gleason.Harmonic.Zonal.NorthZonalSquaredFactorBridge
import Gleason.Harmonic.Zonal.NorthZonalClosed
import Gleason.Harmonic.Zonal.NorthZonalOddClosed
import Gleason.Continuity.Auxiliary.ClosedQuadratic
import Gleason.Harmonic.Rotation.RotationEquiv

noncomputable section

open Complex InnerProductSpace

theorem continuousSphereQuadraticSubmodule_invariant_under_spherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    continuousSphereQuadraticSubmodule ≤
      continuousSphereQuadraticSubmodule.comap (spherePrecomp e) := by
  intro f hf
  rcases hf with ⟨Q, hQ⟩
  refine ⟨Q.comp e.toLinearEquiv.toLinearMap, ?_⟩
  intro x
  rw [QuadraticMap.comp_apply]
  simpa [spherePrecomp_apply, sphereMap]
    using hQ (sphereMap e x)

theorem continuousSphereQuadraticSubmodule_map_spherePrecompLinearEquiv
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    continuousSphereQuadraticSubmodule.map (spherePrecompLinearEquiv e).toLinearMap =
      continuousSphereQuadraticSubmodule := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact continuousSphereQuadraticSubmodule_invariant_under_spherePrecomp e
  · intro f hf
    refine ⟨(spherePrecompLinearEquiv e).symm f, ?_, ?_⟩
    · simpa [spherePrecompLinearEquiv] using
        continuousSphereQuadraticSubmodule_invariant_under_spherePrecomp e.symm hf
    · ext x
      simp [spherePrecompLinearEquiv, spherePrecomp]

theorem inf_northZonalSubmodule_le_continuousSphereQuadraticSubmodule_of_le_even_degree_of_le_pointConstraint
    {n : ℕ}
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hnEven : Even n)
    (hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n)
    (hGpc : G ≤ continuousSphereGreatCirclePointConstraintSubmodule) :
    G ⊓ northZonalSubmodule ≤ continuousSphereQuadraticSubmodule := by
  intro g hg
  have hgz : IsNorthZonal g := (mem_northZonalSubmodule_iff g).1 hg.2
  exact
    mem_continuousSphereQuadraticSubmodule_of_even_mem_continuousHarmonicSphereDegreeSubmodule
      (hGdeg hg.1) (hGpc hg.1) hgz hnEven

theorem exists_nonzero_mem_inf_northZonalSubmodule_of_isClosed_of_rotationInvariant_of_ne_bot
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ), g ∈ G ⊓ northZonalSubmodule ∧ g ≠ 0 := by
  rcases exists_nonzero_northZonal_mem_of_isClosed_of_rotationInvariant
      hGclosed hGrot hGne with ⟨g, hgG, hgne, hgz⟩
  exact ⟨g, ⟨hgG, hgz⟩, hgne⟩

theorem exists_nonzero_mem_inf_northZonalSubmodule_mem_quadratic_of_isClosed_of_rotationInvariant_of_le_even_degree_of_le_pointConstraint
    {n : ℕ}
    (hnEven : Even n)
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n)
    (hGpc : G ≤ continuousSphereGreatCirclePointConstraintSubmodule)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ G ⊓ northZonalSubmodule ∧ g ≠ 0 ∧ g ∈ continuousSphereQuadraticSubmodule := by
  rcases exists_nonzero_mem_inf_northZonalSubmodule_of_isClosed_of_rotationInvariant_of_ne_bot
      hGclosed hGrot hGne with ⟨g, hg, hgne⟩
  exact ⟨g, hg, hgne,
    inf_northZonalSubmodule_le_continuousSphereQuadraticSubmodule_of_le_even_degree_of_le_pointConstraint
      hnEven hGdeg hGpc hg⟩

theorem eq_bot_or_exists_nonzero_mem_inf_northZonalSubmodule_mem_quadratic_of_isClosed_of_rotationInvariant_of_le_degree_of_le_pointConstraint
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
          g ∈ continuousSphereQuadraticSubmodule := by
  by_cases hGne : G = ⊥
  · exact Or.inl hGne
  · by_cases hnEven : Even n
    · right
      exact
        exists_nonzero_mem_inf_northZonalSubmodule_mem_quadratic_of_isClosed_of_rotationInvariant_of_le_even_degree_of_le_pointConstraint
          hnEven hGclosed hGrot hGdeg hGpc hGne
    · left
      exact
        eq_bot_of_isClosed_of_rotationInvariant_of_le_odd_degree_of_le_pointConstraint
          (Nat.not_even_iff_odd.mp hnEven) hGclosed hGrot hGdeg hGpc
