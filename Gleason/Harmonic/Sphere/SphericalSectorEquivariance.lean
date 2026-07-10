import Gleason.Harmonic.Sphere.SphericalSectorProjection
import SphericalHarmonics.RotationInvariant

noncomputable section

namespace SphericalHarmonics

@[simp] theorem sectorProjectionContinuous_compContinuous
    (ρ : Rotation) (n : ℕ) (f : C(S2, ℝ)) :
    sectorProjectionContinuous n (Rotation.compContinuous ρ f) =
      ⟨Rotation.compContinuous ρ (ambientSectorProjectionContinuous n f),
        SphericalHarmonics.compContinuous_mem_sector ρ n
          (sectorProjectionContinuous_apply_mem n f)⟩ := by
  apply sectorToSectorL2_injective n
  apply Subtype.ext
  have hproj :
      continuousToLp (ambientSectorProjectionContinuous n f) =
        (sectorL2 n).starProjection (continuousToLp f) := by
    let y : sectorL2 n :=
      (((sectorL2 n).starProjection.comp continuousToLp).codRestrict (sectorL2 n)
        (fun f =>
          ((sectorL2 n).starProjection_eq_self_iff).1 <| by
            change
              (sectorL2 n).starProjection
                  (((sectorL2 n).starProjection.comp continuousToLp) f) =
                ((sectorL2 n).starProjection.comp continuousToLp) f
            have hidem := (sectorL2 n).isIdempotentElem_starProjection.eq
            exact congrArg (fun T : L2S2 →L[ℝ] L2S2 => T (continuousToLp f)) hidem)) f
    have hy : sectorToSectorL2 n (sectorProjectionContinuous n f) = y := by
      exact (sectorToSectorL2Equiv n).apply_symm_apply y
    change continuousToLp (ambientSectorProjectionContinuous n f) = ↑y
    simpa [ambientSectorProjectionContinuous, sectorProjectionContinuous, sectorToSectorL2,
      ContinuousLinearMap.comp_apply] using congrArg Subtype.val hy
  have hprojρ :
      continuousToLp (ambientSectorProjectionContinuous n (Rotation.compContinuous ρ f)) =
        (sectorL2 n).starProjection (continuousToLp (Rotation.compContinuous ρ f)) := by
    let y : sectorL2 n :=
      (((sectorL2 n).starProjection.comp continuousToLp).codRestrict (sectorL2 n)
        (fun f =>
          ((sectorL2 n).starProjection_eq_self_iff).1 <| by
            change
              (sectorL2 n).starProjection
                  (((sectorL2 n).starProjection.comp continuousToLp) f) =
                ((sectorL2 n).starProjection.comp continuousToLp) f
            have hidem := (sectorL2 n).isIdempotentElem_starProjection.eq
            exact congrArg (fun T : L2S2 →L[ℝ] L2S2 => T (continuousToLp f)) hidem))
          (Rotation.compContinuous ρ f)
    have hy : sectorToSectorL2 n (sectorProjectionContinuous n (Rotation.compContinuous ρ f)) = y := by
      exact (sectorToSectorL2Equiv n).apply_symm_apply y
    change continuousToLp (ambientSectorProjectionContinuous n (Rotation.compContinuous ρ f)) = ↑y
    simpa [ambientSectorProjectionContinuous, sectorProjectionContinuous, sectorToSectorL2,
      ContinuousLinearMap.comp_apply] using congrArg Subtype.val hy
  have h :
      (sectorL2 n).starProjection (continuousToLp (Rotation.compContinuous ρ f)) =
        continuousToLp (Rotation.compContinuous ρ (ambientSectorProjectionContinuous n f)) := by
    calc
      (sectorL2 n).starProjection (continuousToLp (Rotation.compContinuous ρ f))
          =
            (sectorL2 n).starProjection
              (Rotation.compL2Rotation ρ.symm (continuousToLp f)) := by
                simpa using congrArg (fun x => (sectorL2 n).starProjection x)
                  (continuousToLp_compContinuous_symm ρ.symm f).symm
      _ =
            Rotation.compL2Rotation ρ.symm
              ((sectorL2 n).starProjection (continuousToLp f)) := by
                simpa using
                  (sectorL2_starProjection_compL2Rotation_apply
                    ρ.symm n (continuousToLp f))
      _ = continuousToLp
            (Rotation.compContinuous ρ (ambientSectorProjectionContinuous n f)) := by
            rw [← hproj]
            simpa using
              (continuousToLp_compContinuous_symm ρ.symm
                (ambientSectorProjectionContinuous n f))
  exact hprojρ.trans h

@[simp] theorem ambientSectorProjectionContinuous_compContinuous
    (ρ : Rotation) (n : ℕ) (f : C(S2, ℝ)) :
    ambientSectorProjectionContinuous n (Rotation.compContinuous ρ f) =
      Rotation.compContinuous ρ (ambientSectorProjectionContinuous n f) := by
  exact congrArg Subtype.val (sectorProjectionContinuous_compContinuous ρ n f)

end SphericalHarmonics
