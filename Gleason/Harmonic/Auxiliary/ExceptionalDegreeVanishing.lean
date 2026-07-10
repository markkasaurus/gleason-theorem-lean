import Gleason.Harmonic.HighDegree.HighDegreeClosed

noncomputable section

open Complex InnerProductSpace

theorem eq_zero_of_mem_continuousHarmonicSphereDegreeSubmodule_gt_two_of_northZonal_pointConstraint
    {n : ℕ} (hn : 2 < n) {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hgz : IsNorthZonal g) :
    g = 0 := by
  rcases
      eq_zero_or_mem_continuousSphereQuadraticSubmodule_of_mem_continuousHarmonicSphereDegreeSubmodule
        hg hgpc hgz with hg0 | hgq
  · exact hg0
  · have hgsup :
        g ∈ continuousHarmonicSphereDegreeSubmodule 0 ⊔
          continuousHarmonicSphereDegreeSubmodule 2 :=
      mem_sup_zero_two_of_isNorthZonal_mem_quadratic_pointConstraint hgq hgpc hgz
    exact
      eq_zero_of_mem_continuousHarmonicSphereDegreeSubmodule_gt_two_of_northZonal_mem_sup_zero_two
        hn hg hgpc hgz hgsup

theorem eq_zero_of_mem_continuousHarmonicSphereDegreeSubmodule_ne_zero_two_of_northZonal_pointConstraint
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2) {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hgz : IsNorthZonal g) :
    g = 0 := by
  have hsplit : n = 1 ∨ 2 < n := by
    omega
  rcases hsplit with rfl | hn
  · exact
      eq_zero_of_odd_of_mem_continuousHarmonicSphereDegreeSubmodule_of_northZonal_pointConstraint
        (by decide) hg hgpc hgz
  · exact
      eq_zero_of_mem_continuousHarmonicSphereDegreeSubmodule_gt_two_of_northZonal_pointConstraint
        hn hg hgpc hgz

theorem eq_bot_of_isClosed_of_rotationInvariant_of_le_ne_zero_two_degree_of_le_pointConstraint
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2)
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
    eq_zero_of_mem_continuousHarmonicSphereDegreeSubmodule_ne_zero_two_of_northZonal_pointConstraint
      hn0 hn2 hgdeg hgpc' hgz
  exact hgne hgzero
