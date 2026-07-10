import Gleason.Harmonic.Rotation.RotationHarmonic

noncomputable section

open Complex InnerProductSpace

@[simp] lemma sphereMap_symm_apply
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (x : spherePoint3) :
    sphereMap e.symm (sphereMap e x) = x := by
  apply Subtype.ext
  simp [sphereMap]

@[simp] lemma sphereMap_apply_symm
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (x : spherePoint3) :
    sphereMap e (sphereMap e.symm x) = x := by
  apply Subtype.ext
  simp [sphereMap]

def spherePrecompLinearEquiv
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    C(spherePoint3, ℝ) ≃ₗ[ℝ] C(spherePoint3, ℝ) where
  toFun := spherePrecomp e
  invFun := spherePrecomp e.symm
  left_inv := by
    intro f
    ext x
    simp [spherePrecomp]
  right_inv := by
    intro f
    ext x
    simp [spherePrecomp]
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

def ambientPrecompLinearEquiv
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    (WithLp 2 (ℂ × ℝ) → ℝ) ≃ₗ[ℝ] (WithLp 2 (ℂ × ℝ) → ℝ) where
  toFun := ambientPrecomp e
  invFun := ambientPrecomp e.symm
  left_inv := by
    intro f
    ext x
    simp [ambientPrecomp]
  right_inv := by
    intro f
    ext x
    simp [ambientPrecomp]
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

theorem continuousSphereFrameSubmodule_map_spherePrecompLinearEquiv
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    continuousSphereFrameSubmodule.map (spherePrecompLinearEquiv e).toLinearMap =
      continuousSphereFrameSubmodule := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact continuousSphereFrameSubmodule_invariant_under_spherePrecomp e
  · intro f hf
    refine ⟨(spherePrecompLinearEquiv e).symm f, ?_, ?_⟩
    · simpa [spherePrecompLinearEquiv] using
        continuousSphereFrameSubmodule_invariant_under_spherePrecomp e.symm hf
    · ext x
      simp [spherePrecompLinearEquiv, spherePrecomp]

theorem continuousHarmonicSphereDegreeSubmodule_map_spherePrecompLinearEquiv
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (n : ℕ) :
    (continuousHarmonicSphereDegreeSubmodule n).map (spherePrecompLinearEquiv e).toLinearMap =
      continuousHarmonicSphereDegreeSubmodule n := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact continuousHarmonicSphereDegreeSubmodule_invariant_under_spherePrecomp e n
  · intro f hf
    refine ⟨(spherePrecompLinearEquiv e).symm f, ?_, ?_⟩
    · simpa [spherePrecompLinearEquiv] using
        continuousHarmonicSphereDegreeSubmodule_invariant_under_spherePrecomp e.symm n hf
    · ext x
      simp [spherePrecompLinearEquiv, spherePrecomp]

theorem harmonicSphereDegreeSubmodule_map_spherePrecompLinearEquiv
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (n : ℕ) :
    (harmonicSphereDegreeSubmodule n).map (spherePrecompPi e) =
      harmonicSphereDegreeSubmodule n := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact harmonicSphereDegreeSubmodule_invariant_under_spherePrecompPi e n
  · intro f hf
    refine ⟨spherePrecompPi e.symm f, ?_, ?_⟩
    · simpa using harmonicSphereDegreeSubmodule_invariant_under_spherePrecompPi e.symm n hf
    · ext x
      simp [spherePrecompPi, sphereMap]

theorem harmonicHomogeneousDegreeSubmodule_map_ambientPrecompLinearEquiv
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (n : ℕ) :
    (harmonicHomogeneousDegreeSubmodule n).map (ambientPrecompLinearEquiv e).toLinearMap =
      harmonicHomogeneousDegreeSubmodule n := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact harmonicHomogeneousDegreeSubmodule_invariant_under_ambientPrecomp e n
  · intro f hf
    refine ⟨(ambientPrecompLinearEquiv e).symm f, ?_, ?_⟩
    · simpa [ambientPrecompLinearEquiv] using
        harmonicHomogeneousDegreeSubmodule_invariant_under_ambientPrecomp e.symm n hf
    · ext x
      simp [ambientPrecompLinearEquiv, ambientPrecomp]
