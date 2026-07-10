import SphericalHarmonics.FiniteDimensional
import SphericalHarmonics.L2Decomposition

noncomputable section

open scoped ENNReal

namespace SphericalHarmonics

theorem sectorToSectorL2_injective (n : ℕ) :
    Function.Injective (sectorToSectorL2 n) := by
  intro f g hfg
  apply Subtype.ext
  exact ContinuousMap.toLp_injective rotationMeasure (by
    simpa [sectorToSectorL2] using congrArg Subtype.val hfg)

/-- The canonical identification of the continuous degree-`n` sector with its `L²` image. -/
noncomputable def sectorToSectorL2Equiv (n : ℕ) : sector n ≃ₗ[ℝ] sectorL2 n :=
  LinearEquiv.ofBijective (sectorToSectorL2 n)
    ⟨sectorToSectorL2_injective n, sectorToSectorL2_surjective n⟩

/-- Orthogonal projection to the degree-`n` sector, returned as a continuous function on `S²`. -/
noncomputable def sectorProjectionContinuous (n : ℕ) :
    C(S2, ℝ) →L[ℝ] sector n :=
  (sectorToSectorL2Equiv n).symm.toContinuousLinearMap.comp <|
    ((sectorL2 n).starProjection.comp continuousToLp).codRestrict (sectorL2 n) fun f =>
      ((sectorL2 n).starProjection_eq_self_iff).1 <| by
        change
          (sectorL2 n).starProjection
              (((sectorL2 n).starProjection.comp continuousToLp) f) =
            ((sectorL2 n).starProjection.comp continuousToLp) f
        have hidem := (sectorL2 n).isIdempotentElem_starProjection.eq
        exact congrArg (fun T : L2S2 →L[ℝ] L2S2 => T (continuousToLp f)) hidem

/-- Orthogonal projection to the degree-`n` sector, viewed in the ambient continuous function
space. -/
noncomputable def ambientSectorProjectionContinuous (n : ℕ) :
    C(S2, ℝ) →L[ℝ] C(S2, ℝ) :=
  (sector n).subtypeL.comp (sectorProjectionContinuous n)

@[simp] theorem sectorProjectionContinuous_apply_mem (n : ℕ) (f : C(S2, ℝ)) :
    ((sectorProjectionContinuous n f : sector n) : C(S2, ℝ)) ∈ sector n :=
  (sectorProjectionContinuous n f).property

@[simp] theorem ambientSectorProjectionContinuous_apply
    (n : ℕ) (f : C(S2, ℝ)) :
    ambientSectorProjectionContinuous n f = sectorProjectionContinuous n f := rfl

@[simp] theorem sectorProjectionContinuous_eq_self
    {n : ℕ} {f : C(S2, ℝ)} (hf : f ∈ sector n) :
    sectorProjectionContinuous n f = ⟨f, hf⟩ := by
  apply (sectorToSectorL2Equiv n).injective
  have hmem : continuousToLp f ∈ sectorL2 n := continuousToLp_mem_sectorL2 hf
  apply Subtype.ext
  simpa [sectorProjectionContinuous] using
    (sectorL2 n).starProjection_eq_self_iff.mpr hmem

@[simp] theorem ambientSectorProjectionContinuous_eq_self
    {n : ℕ} {f : C(S2, ℝ)} (hf : f ∈ sector n) :
    ambientSectorProjectionContinuous n f = f := by
  exact congrArg Subtype.val (sectorProjectionContinuous_eq_self hf)

@[simp] theorem sectorProjectionContinuous_eq_zero_of_orthogonal
    {m n : ℕ} (hmn : m ≠ n) {f : C(S2, ℝ)} (hf : f ∈ sector m) :
    sectorProjectionContinuous n f = 0 := by
  apply (sectorToSectorL2Equiv n).injective
  have hmem : continuousToLp f ∈ sectorL2 m := continuousToLp_mem_sectorL2 hf
  have hcomp0 :
      (sectorL2 n).starProjection ∘L (sectorL2 m).starProjection = 0 := by
    rw [Submodule.starProjection_comp_starProjection_eq_zero_iff]
    exact sectorL2_isOrtho_of_ne (by exact fun h => hmn h.symm)
  have hzero : (sectorL2 n).starProjection (continuousToLp f) = 0 := by
    have hmfix : (sectorL2 m).starProjection (continuousToLp f) = continuousToLp f := by
      exact (sectorL2 m).starProjection_eq_self_iff.mpr hmem
    have hzero' := DFunLike.congr_fun hcomp0 (continuousToLp f)
    simpa [hmfix] using hzero'
  apply Subtype.ext
  simpa [sectorProjectionContinuous] using hzero

@[simp] theorem ambientSectorProjectionContinuous_eq_zero_of_orthogonal
    {m n : ℕ} (hmn : m ≠ n) {f : C(S2, ℝ)} (hf : f ∈ sector m) :
    ambientSectorProjectionContinuous n f = 0 := by
  exact congrArg Subtype.val (sectorProjectionContinuous_eq_zero_of_orthogonal hmn hf)

end SphericalHarmonics
