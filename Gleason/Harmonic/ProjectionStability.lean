import Gleason.Harmonic.GreatCircle.GreatCirclePointKernel
import Gleason.Harmonic.GreatCircle.GreatCirclePointRotation
import Gleason.Harmonic.Sphere.S2PoleAverageEquivariance
import Gleason.Harmonic.Sphere.SphereDegreeProjection

noncomputable section

open Complex InnerProductSpace
open SphericalHarmonics

namespace GleasonProjectionStability

open GleasonS2Bridge

/-- Continuous submodules of `C(S², ℝ)` stable under all ambient orthogonal precompositions. -/
def IsSpherePrecompInvariant (G : Submodule ℝ C(spherePoint3, ℝ)) : Prop :=
  ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
    G.map (spherePrecompLinearEquiv e).toLinearMap = G

theorem continuousSphereGreatCirclePointConstraintSubmodule_isSpherePrecompInvariant :
    IsSpherePrecompInvariant continuousSphereGreatCirclePointConstraintSubmodule := by
  intro e
  exact continuousSphereGreatCirclePointConstraintSubmodule_map_spherePrecompLinearEquiv e

theorem continuousHarmonicSphereDegreeSubmodule_isSpherePrecompInvariant
    (n : ℕ) :
    IsSpherePrecompInvariant (continuousHarmonicSphereDegreeSubmodule n) := by
  intro e
  exact continuousHarmonicSphereDegreeSubmodule_map_spherePrecompLinearEquiv e n

noncomputable def rotationOfSpherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) : Rotation :=
  ((GleasonS2Bridge.ambientToE3.symm.trans e.symm).trans GleasonS2Bridge.ambientToE3)

@[simp] theorem ambientRotation_rotationOfSpherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    GleasonS2Bridge.ambientRotation (rotationOfSpherePrecomp e) = e := by
  ext x
  change
    GleasonS2Bridge.ambientToE3.symm
      (GleasonS2Bridge.ambientToE3
        (e
          (GleasonS2Bridge.ambientToE3.symm
            (GleasonS2Bridge.ambientToE3 x)))) = e x
  rw [LinearIsometryEquiv.symm_apply_apply GleasonS2Bridge.ambientToE3 x]
  rw [LinearIsometryEquiv.symm_apply_apply GleasonS2Bridge.ambientToE3 (e x)]

private theorem s2Pullback_symm_spherePrecomp_eq_compContinuous_local
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : C(spherePoint3, ℝ)) :
    s2Pullback.symm (spherePrecomp e f) =
      (rotationOfSpherePrecomp e).compContinuous (s2Pullback.symm f) := by
  apply s2Pullback.injective
  calc
    s2Pullback (s2Pullback.symm (spherePrecomp e f))
        = spherePrecomp e f :=
      LinearEquiv.apply_symm_apply s2Pullback (spherePrecomp e f)
    _ =
        spherePrecomp (GleasonS2Bridge.ambientRotation (rotationOfSpherePrecomp e))
          (s2Pullback (s2Pullback.symm f)) := by
          rw [ambientRotation_rotationOfSpherePrecomp, LinearEquiv.apply_symm_apply]
    _ = s2Pullback
          ((rotationOfSpherePrecomp e).compContinuous (s2Pullback.symm f)) := by
            symm
            simpa using
              GleasonS2Bridge.s2Pullback_compContinuous_eq_spherePrecomp_ambientRotation
                (rotationOfSpherePrecomp e) (s2Pullback.symm f)

theorem IsSpherePrecompInvariant.map_of_commutes
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    {T : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ)}
    (hG : IsSpherePrecompInvariant G)
    (hcomm :
      ∀ (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) (f : C(spherePoint3, ℝ)),
        T (spherePrecomp e f) = spherePrecomp e (T f)) :
    IsSpherePrecompInvariant (G.map T) := by
  intro e
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨g, hg, rfl⟩
    rcases hg with ⟨g0, hg0, rfl⟩
    refine ⟨spherePrecomp e g0, ?_, ?_⟩
    · have hmem_map : spherePrecomp e g0 ∈ G.map (spherePrecompLinearEquiv e).toLinearMap := by
        exact ⟨g0, hg0, rfl⟩
      simpa [hG e] using hmem_map
    · simpa using (hcomm e g0)
  · intro f hf
    rcases hf with ⟨g0, hg0, rfl⟩
    refine ⟨T (spherePrecomp e.symm g0), ?_, ?_⟩
    · refine ⟨spherePrecomp e.symm g0, ?_, rfl⟩
      have hmem_map :
          spherePrecomp e.symm g0 ∈ G.map (spherePrecompLinearEquiv e.symm).toLinearMap := by
        exact ⟨g0, hg0, rfl⟩
      simpa [hG e.symm] using hmem_map
    · calc
        spherePrecomp e (T (spherePrecomp e.symm g0))
            = T (spherePrecomp e (spherePrecomp e.symm g0)) := by
                symm
                simpa using hcomm e (spherePrecomp e.symm g0)
        _ = T g0 := by
              congr 1
              ext x
              simp [spherePrecomp]

theorem harmonicDegreeProjectionContinuous_image_isSpherePrecompInvariant
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hG : IsSpherePrecompInvariant G)
    (n : ℕ) :
    IsSpherePrecompInvariant
      (G.map (GleasonS2Bridge.harmonicDegreeProjectionContinuous n)) := by
  exact hG.map_of_commutes (T := GleasonS2Bridge.harmonicDegreeProjectionContinuous n) <|
    by
      intro e f
      rw [GleasonS2Bridge.harmonicDegreeProjectionContinuous_apply,
        s2Pullback_symm_spherePrecomp_eq_compContinuous_local]
      rw [SphericalHarmonics.ambientSectorProjectionContinuous_compContinuous]
      rw [GleasonS2Bridge.s2Pullback_compContinuous_eq_spherePrecomp_ambientRotation]
      rw [ambientRotation_rotationOfSpherePrecomp]
      simp [GleasonS2Bridge.harmonicDegreeProjectionContinuous]

theorem harmonicDegreeProjectionContinuous_image_le_continuousHarmonicSphereDegreeSubmodule
    (G : Submodule ℝ C(spherePoint3, ℝ))
    (n : ℕ) :
    G.map (GleasonS2Bridge.harmonicDegreeProjectionContinuous n) ≤
      continuousHarmonicSphereDegreeSubmodule n := by
  intro f hf
  rcases hf with ⟨g, -, rfl⟩
  exact GleasonS2Bridge.harmonicDegreeProjectionContinuous_mem_continuousHarmonicSphereDegreeSubmodule n g

/-- Clean projection-stability reduction:
if the standard point constraint vanishes on the projected image, then the full great-circle
point-constraint submodule is preserved by the harmonic degree projector. -/
theorem harmonicDegreeProjectionContinuous_image_le_pointConstraint_of_std
    (n : ℕ)
    (hstd :
      continuousSphereGreatCirclePointConstraintSubmodule.map
          (GleasonS2Bridge.harmonicDegreeProjectionContinuous n) ≤
        stdGreatCirclePointConstraintSubmodule) :
    continuousSphereGreatCirclePointConstraintSubmodule.map
        (GleasonS2Bridge.harmonicDegreeProjectionContinuous n) ≤
      continuousSphereGreatCirclePointConstraintSubmodule := by
  apply le_continuousSphereGreatCirclePointConstraintSubmodule_of_invariant_and_le_std
  · exact
      harmonicDegreeProjectionContinuous_image_isSpherePrecompInvariant
        continuousSphereGreatCirclePointConstraintSubmodule_isSpherePrecompInvariant n
  · exact hstd

end GleasonProjectionStability
