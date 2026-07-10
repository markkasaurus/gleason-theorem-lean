import Gleason.Harmonic.Zonal.NorthZonalSectorQ02
import Gleason.Harmonic.Profile.LowProfileVanishing

noncomputable section

open Complex InnerProductSpace

theorem eq_bot_of_isClosed_of_rotationInvariant_of_le_gt_two_degree_of_le_pointConstraint
    {n : ℕ} (hn : 2 < n)
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n)
    (hGpc : G ≤ continuousSphereGreatCirclePointConstraintSubmodule) :
    G = ⊥ := by
  rcases
      eq_bot_or_exists_nonzero_mem_inf_northZonalSubmodule_mem_sup_zero_two_of_isClosed_of_rotationInvariant_of_le_degree_of_le_pointConstraint
        hGclosed hGrot hGdeg hGpc with hGbot | ⟨g, hgInf, hgne, hgsup⟩
  · exact hGbot
  · have hgz : IsNorthZonal g := (mem_northZonalSubmodule_iff g).1 hgInf.2
    have hgzero :
        g = 0 :=
      eq_zero_of_mem_continuousHarmonicSphereDegreeSubmodule_gt_two_of_northZonal_mem_sup_zero_two
        hn (hGdeg hgInf.1) (hGpc hgInf.1) hgz hgsup
    exact (hgne hgzero).elim
