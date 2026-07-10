import Gleason.Harmonic.Sphere.SphericalBridge
import Gleason.Harmonic.Sphere.SphericalSectorProjection
import Gleason.Harmonic.Sphere.SphericalSectorEquivariance
import Gleason.Harmonic.Sphere.S2NorthZonalBridge
import Gleason.Harmonic.Sphere.S2PoleAverageExceptionalDegree
import Gleason.Harmonic.Sphere.S2PoleAverageEquivariance

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

/-- The `S²` rotation corresponding to an ambient linear isometry of `spherePoint3`. -/
noncomputable def rotationOfSpherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) : Rotation :=
  ((ambientToE3.symm.trans e.symm).trans ambientToE3)

@[simp] theorem ambientRotation_rotationOfSpherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    ambientRotation (rotationOfSpherePrecomp e) = e := by
  ext x
  simp only [ambientRotation, rotationOfSpherePrecomp, LinearIsometryEquiv.trans_apply]
  change ambientToE3.symm (ambientToE3 (e (ambientToE3.symm (ambientToE3 x)))) = e x
  rw [LinearIsometryEquiv.symm_apply_apply ambientToE3 x]
  rw [LinearIsometryEquiv.symm_apply_apply ambientToE3 (e x)]

@[simp] theorem s2Pullback_symm_spherePrecomp_eq_compContinuous
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : C(spherePoint3, ℝ)) :
    s2Pullback.symm (spherePrecomp e f) =
      Rotation.compContinuous (rotationOfSpherePrecomp e) (s2Pullback.symm f) := by
  apply s2Pullback.injective
  calc
    s2Pullback (s2Pullback.symm (spherePrecomp e f))
        = spherePrecomp e f := by simp
    _ = spherePrecomp (ambientRotation (rotationOfSpherePrecomp e)) (s2Pullback (s2Pullback.symm f)) := by
          simp
    _ = s2Pullback
          (Rotation.compContinuous (rotationOfSpherePrecomp e) (s2Pullback.symm f)) := by
            symm
            simpa using
              s2Pullback_compContinuous_eq_spherePrecomp_ambientRotation
                (rotationOfSpherePrecomp e) (s2Pullback.symm f)

/-- Transport the continuous degree-`n` sector projector on `S²` back to `spherePoint3`. -/
noncomputable def harmonicDegreeProjectionContinuous (n : ℕ) :
    C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ) :=
  LinearMap.comp s2Pullback.toLinearMap <|
    LinearMap.comp (ambientSectorProjectionContinuous n).toLinearMap
      s2Pullback.symm.toLinearMap

@[simp] theorem harmonicDegreeProjectionContinuous_apply
    (n : ℕ) (f : C(spherePoint3, ℝ)) :
    harmonicDegreeProjectionContinuous n f =
      s2Pullback (ambientSectorProjectionContinuous n (s2Pullback.symm f)) := by
  rfl

@[simp] theorem s2Pullback_ambientSectorProjectionContinuous_eq_harmonicDegreeProjectionContinuous
    (n : ℕ) (f : C(S2, ℝ)) :
    harmonicDegreeProjectionContinuous n (s2Pullback f) =
      s2Pullback (ambientSectorProjectionContinuous n f) := by
  simp [harmonicDegreeProjectionContinuous]

theorem harmonicDegreeProjectionContinuous_mem_continuousHarmonicSphereDegreeSubmodule
    (n : ℕ) (f : C(spherePoint3, ℝ)) :
    harmonicDegreeProjectionContinuous n f ∈ continuousHarmonicSphereDegreeSubmodule n := by
  rw [harmonicDegreeProjectionContinuous_apply]
  exact
    s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule
      (sectorProjectionContinuous_apply_mem n (s2Pullback.symm f))

@[simp] theorem harmonicDegreeProjectionContinuous_spherePrecomp
    (n : ℕ)
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : C(spherePoint3, ℝ)) :
    harmonicDegreeProjectionContinuous n (spherePrecomp e f) =
      spherePrecomp e (harmonicDegreeProjectionContinuous n f) := by
  rw [harmonicDegreeProjectionContinuous_apply, s2Pullback_symm_spherePrecomp_eq_compContinuous]
  rw [ambientSectorProjectionContinuous_compContinuous]
  rw [s2Pullback_compContinuous_eq_spherePrecomp_ambientRotation]
  simp [harmonicDegreeProjectionContinuous]

theorem ambientSectorProjectionContinuous_mem_northFixedSubmodule
    {n : ℕ} {f : C(S2, ℝ)}
    (hf : f ∈ northFixedSubmodule) :
    ambientSectorProjectionContinuous n f ∈ northFixedSubmodule := by
  rw [mem_northFixedSubmodule_iff] at hf ⊢
  intro t
  calc
    Rotation.compContinuous (rotation01 t) (ambientSectorProjectionContinuous n f)
        = ambientSectorProjectionContinuous n
            (Rotation.compContinuous (rotation01 t) f) := by
              simpa using
                (ambientSectorProjectionContinuous_compContinuous (rotation01 t) n f).symm
    _ = ambientSectorProjectionContinuous n f := by simpa [hf t]

theorem isNorthZonal_harmonicDegreeProjectionContinuous_of_mem_northFixedSubmodule
    {n : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : s2Pullback.symm f ∈ northFixedSubmodule) :
    IsNorthZonal (harmonicDegreeProjectionContinuous n f) := by
  rw [harmonicDegreeProjectionContinuous_apply]
  apply isNorthZonal_s2Pullback_of_mem_northFixedSubmodule
  exact ambientSectorProjectionContinuous_mem_northFixedSubmodule hf

theorem harmonicDegreeProjectionContinuous_s2PoleAverageContinuousOfPointConstraint_eq_neg_half
    {n : ℕ} (hn0 : n ≠ 0)
    {g : C(S2, ℝ)}
    (hg : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    let gavg : C(S2, ℝ) :=
      s2PoleAverageContinuousOfGreatCircleConstraint g
        (by
          have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
            simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
              using hg
          exact
            continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe)
    harmonicDegreeProjectionContinuous n (s2Pullback gavg) =
      -((1 / 2 : ℝ)) • harmonicDegreeProjectionContinuous n (s2Pullback g) := by
  dsimp
  rw [s2Pullback_ambientSectorProjectionContinuous_eq_harmonicDegreeProjectionContinuous]
  rw [s2Pullback_ambientSectorProjectionContinuous_eq_harmonicDegreeProjectionContinuous]
  exact congrArg s2Pullback <|
    ambientSectorProjectionContinuous_s2PoleAverageLinear_eq_neg_half_of_mem_pointConstraint
      hn0 hg

end GleasonS2Bridge
