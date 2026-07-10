import Gleason.Harmonic.HighDegree.EvenLowConcrete
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileQuadratic
import Gleason.Harmonic.Auxiliary.PointConstraintFrame

noncomputable section

open Complex InnerProductSpace Polynomial

theorem mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isNorthZonal_mem_frame_of_sqprofile_polynomial
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {q : ℝ[X]}
    (hq : ∀ u : Set.Icc (0 : ℝ) 1,
      sqCenteredNorthZonalProfile g u = q.eval u.1) :
    g ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
  have hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
    rw [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]
    exact hgframe
  have hgquad :
      g ∈ continuousSphereQuadraticSubmodule :=
    mem_continuousSphereQuadraticSubmodule_of_isNorthZonal_pointConstraint_sqPolynomial
      hgpc hgz q hq
  rcases exists_const_add_sq_of_isNorthZonal_mem_quadratic_pointConstraint hgquad hgpc hgz with
    ⟨a, b, hab⟩
  have hdecomp :
      g = (a + b / 3) • (1 : C(spherePoint3, ℝ)) + (-b / 3) • zonalQuadraticMode := by
    ext x
    rw [hab x]
    simp [Pi.smul_apply, zonalQuadraticMode_apply]
    ring
  rw [hdecomp]
  apply Submodule.add_mem_sup
  · exact
      Submodule.smul_mem _ (a + b / 3)
        one_mem_harmonicPolyHomogeneousImageSubmodule_zero
  · exact
      Submodule.smul_mem _ (-b / 3)
        zonalQuadraticMode_mem_harmonicPolyHomogeneousImageSubmodule_two
