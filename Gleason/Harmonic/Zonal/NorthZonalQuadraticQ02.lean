import Gleason.Harmonic.Zonal.NorthZonalQuadraticRepresentation
import Gleason.Harmonic.Sectors.HarmonicBHomogeneous

noncomputable section

open Complex InnerProductSpace

def zonalQuadraticMode : C(spherePoint3, ℝ) :=
  ⟨sphereRestrictionLinear (surfaceModeBL2 2),
    continuous_sphereRestriction_of_harmonicHomogeneousDegree
      ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩⟩

lemma one_mem_continuousHarmonicSphereDegreeSubmodule_zero :
    (1 : C(spherePoint3, ℝ)) ∈ continuousHarmonicSphereDegreeSubmodule 0 := by
  show ((1 : C(spherePoint3, ℝ)) : spherePoint3 → ℝ) ∈ harmonicSphereDegreeSubmodule 0
  refine ⟨surfaceModeAL2 0, ⟨surfaceModeAL2_harmonicAt 0, surfaceModeAL2_homogeneous 0⟩, ?_⟩
  ext x
  simp [sphereRestrictionLinear, surfaceModeAL2]

lemma zonalQuadraticMode_mem_continuousHarmonicSphereDegreeSubmodule_two :
    zonalQuadraticMode ∈ continuousHarmonicSphereDegreeSubmodule 2 := by
  show sphereRestrictionLinear (surfaceModeBL2 2) ∈ harmonicSphereDegreeSubmodule 2
  exact ⟨surfaceModeBL2 2,
    ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩, rfl⟩

lemma zonalQuadraticMode_apply (x : spherePoint3) :
    zonalQuadraticMode x = 1 - 3 * sphereCoordZ x ^ 2 := by
  have hx : ‖x.1.fst‖ ^ 2 + x.1.snd ^ 2 = 1 := fst_norm_sq_add_snd_sq x
  have hnormSq :
      Complex.normSq x.1.fst = ‖x.1.fst‖ ^ 2 := by
    simp [Complex.normSq_eq_norm_sq]
  calc
    zonalQuadraticMode x
      = sphereRestrictionLinear (surfaceModeBL2 2) x := by
          rfl
    _ = (Complex.normSq x.1.fst - 2 * x.1.snd ^ 2) * ((1 : ℂ).re) := by
          norm_num [sphereRestrictionLinear, surfaceModeBL2, complexProjL, realProjL]
    _ = Complex.normSq x.1.fst - 2 * x.1.snd ^ 2 := by simp
    _ = ‖x.1.fst‖ ^ 2 - 2 * x.1.snd ^ 2 := by rw [hnormSq]
    _ = 1 - 3 * sphereCoordZ x ^ 2 := by
          rw [show sphereCoordZ x = x.1.snd by rfl]
          nlinarith

theorem mem_sup_zero_two_of_isNorthZonal_mem_quadratic_pointConstraint
    {f : C(spherePoint3, ℝ)}
    (hfq : f ∈ continuousSphereQuadraticSubmodule)
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f) :
    f ∈ continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 := by
  rcases exists_const_add_sq_of_isNorthZonal_mem_quadratic_pointConstraint hfq hfmem hfz
    with ⟨a, b, hab⟩
  have hdecomp :
      f = (a + b / 3) • (1 : C(spherePoint3, ℝ)) + (-b / 3) • zonalQuadraticMode := by
    ext x
    rw [hab x]
    simp [Pi.smul_apply, zonalQuadraticMode_apply]
    ring
  rw [hdecomp]
  apply Submodule.add_mem_sup
  · exact Submodule.smul_mem _ (a + b / 3) one_mem_continuousHarmonicSphereDegreeSubmodule_zero
  · exact Submodule.smul_mem _ (-b / 3) zonalQuadraticMode_mem_continuousHarmonicSphereDegreeSubmodule_two
