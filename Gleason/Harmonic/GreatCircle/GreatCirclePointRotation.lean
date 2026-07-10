import Gleason.Harmonic.GreatCircle.GreatCirclePointConstraints
import Gleason.Harmonic.Rotation.RotationEquiv

noncomputable section

open Complex InnerProductSpace

@[simp] lemma spherePrecomp_trans
    (e₁ e₂ : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : C(spherePoint3, ℝ)) :
    spherePrecomp e₁ (spherePrecomp e₂ f) = spherePrecomp (e₁.trans e₂) f := by
  ext x
  simp [spherePrecomp_apply, sphereMap, LinearIsometryEquiv.trans_apply]

lemma sphereTripleIsometryEquiv_sphereMap_eq_trans
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereTripleIsometryEquiv
        (sphereMap e x) (sphereMap e y) (sphereMap e z)
        (by simpa [sphereMap_inner] using hxy)
        (by simpa [sphereMap_inner] using hxz)
        (by simpa [sphereMap_inner] using hyz) =
      (sphereTripleIsometryEquiv x y z hxy hxz hyz).trans e := by
  apply Module.Basis.ext_linearIsometryEquiv sphereStdBasis
  intro i
  fin_cases i
  · simpa [sphereStdBasis_apply, sphereTripleVec] using
      sphereTripleIsometryEquiv_apply_sphereE1
        (sphereMap e x) (sphereMap e y) (sphereMap e z)
        (by simpa [sphereMap_inner] using hxy)
        (by simpa [sphereMap_inner] using hxz)
        (by simpa [sphereMap_inner] using hyz)
  · simpa [sphereStdBasis_apply, sphereTripleVec] using
      sphereTripleIsometryEquiv_apply_sphereE2
        (sphereMap e x) (sphereMap e y) (sphereMap e z)
        (by simpa [sphereMap_inner] using hxy)
        (by simpa [sphereMap_inner] using hxz)
        (by simpa [sphereMap_inner] using hyz)
  · simpa [sphereStdBasis_apply, sphereTripleVec] using
      sphereTripleIsometryEquiv_apply_sphereE3
        (sphereMap e x) (sphereMap e y) (sphereMap e z)
        (by simpa [sphereMap_inner] using hxy)
        (by simpa [sphereMap_inner] using hxz)
        (by simpa [sphereMap_inner] using hyz)

theorem greatCircleAverageLinear_spherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : C(spherePoint3, ℝ))
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    greatCircleAverageLinear x y z hxy hxz hyz (spherePrecomp e f) =
      greatCircleAverageLinear
        (sphereMap e x) (sphereMap e y) (sphereMap e z)
        (by simpa [sphereMap_inner] using hxy)
        (by simpa [sphereMap_inner] using hxz)
        (by simpa [sphereMap_inner] using hyz)
        f := by
  rw [greatCircleAverageLinear_apply, greatCircleAverageLinear_apply, spherePrecomp_trans]
  have hEq := sphereTripleIsometryEquiv_sphereMap_eq_trans e x y z hxy hxz hyz
  simpa [hEq]

theorem continuousSphereGreatCirclePointConstraintSubmodule_invariant_under_spherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    continuousSphereGreatCirclePointConstraintSubmodule ≤
      continuousSphereGreatCirclePointConstraintSubmodule.comap (spherePrecomp e) := by
  intro f hf
  show spherePrecomp e f ∈ continuousSphereGreatCirclePointConstraintSubmodule
  rw [mem_continuousSphereGreatCirclePointConstraintSubmodule_iff]
  intro x y z hxy hxz hyz
  have hxy' : inner (𝕜 := ℝ) (sphereMap e x).1 (sphereMap e y).1 = 0 := by
    simpa [sphereMap_inner] using hxy
  have hxz' : inner (𝕜 := ℝ) (sphereMap e x).1 (sphereMap e z).1 = 0 := by
    simpa [sphereMap_inner] using hxz
  have hyz' : inner (𝕜 := ℝ) (sphereMap e y).1 (sphereMap e z).1 = 0 := by
    simpa [sphereMap_inner] using hyz
  have hf' :=
    (mem_continuousSphereGreatCirclePointConstraintSubmodule_iff f).1 hf
      (sphereMap e x) (sphereMap e y) (sphereMap e z) hxy' hxz' hyz'
  rw [greatCircleAverageLinear_spherePrecomp]
  simpa [spherePrecomp_apply] using hf'

theorem continuousSphereGreatCirclePointConstraintSubmodule_map_spherePrecompLinearEquiv
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    continuousSphereGreatCirclePointConstraintSubmodule.map (spherePrecompLinearEquiv e).toLinearMap =
      continuousSphereGreatCirclePointConstraintSubmodule := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact continuousSphereGreatCirclePointConstraintSubmodule_invariant_under_spherePrecomp e
  · intro f hf
    refine ⟨(spherePrecompLinearEquiv e).symm f, ?_, ?_⟩
    · simpa [spherePrecompLinearEquiv] using
        continuousSphereGreatCirclePointConstraintSubmodule_invariant_under_spherePrecomp e.symm hf
    · ext x
      simp [spherePrecompLinearEquiv, spherePrecomp]
