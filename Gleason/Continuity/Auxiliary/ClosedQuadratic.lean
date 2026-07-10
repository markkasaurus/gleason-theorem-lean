import Gleason.Continuity.Auxiliary.ContinuousEndpoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.QuadraticForm.Basis

noncomputable section

open Complex InnerProductSpace Real

abbrev sphereAmbient := WithLp 2 (ℂ × ℝ)

def bilinToCLMLinear :
    LinearMap.BilinMap ℝ sphereAmbient ℝ →ₗ[ℝ]
      sphereAmbient →L[ℝ] sphereAmbient →L[ℝ] ℝ where
  toFun := fun B =>
    let B' : sphereAmbient →ₗ[ℝ] sphereAmbient →L[ℝ] ℝ := {
      toFun := fun x => LinearMap.toContinuousLinearMap (B x)
      map_add' := by
        intro x y
        ext z
        simp
      map_smul' := by
        intro c x
        ext z
        simp
    }
    LinearMap.toContinuousLinearMap B'
  map_add' := by
    intro B1 B2
    ext x y
    simp [LinearMap.toContinuousLinearMap]
  map_smul' := by
    intro c B
    ext x y
    simp [LinearMap.toContinuousLinearMap]

lemma continuous_sphere_bilin_eval (B : LinearMap.BilinMap ℝ sphereAmbient ℝ) :
    Continuous fun p : spherePoint3 => B p.1 p.1 := by
  let BC : sphereAmbient →L[ℝ] sphereAmbient →L[ℝ] ℝ := bilinToCLMLinear B
  have hcont : Continuous (Function.uncurry fun x y => BC x y) :=
    ContinuousLinearMap.continuous₂ BC
  simpa [BC, bilinToCLMLinear] using
    hcont.comp (continuous_subtype_val.prodMk continuous_subtype_val)

def sphereBilinRestrictionLinear :
    LinearMap.BilinMap ℝ sphereAmbient ℝ →ₗ[ℝ] C(spherePoint3, ℝ) where
  toFun := fun B => ⟨fun p => B p.1 p.1, continuous_sphere_bilin_eval B⟩
  map_add' := by
    intro B1 B2
    ext p
    simp
  map_smul' := by
    intro c B
    ext p
    simp

@[simp] theorem sphereBilinRestrictionLinear_apply
    (B : LinearMap.BilinMap ℝ sphereAmbient ℝ) (p : spherePoint3) :
    sphereBilinRestrictionLinear B p = B p.1 p.1 := by
  rfl

theorem continuousSphereQuadraticSubmodule_eq_range_sphereBilinRestrictionLinear :
    continuousSphereQuadraticSubmodule = LinearMap.range sphereBilinRestrictionLinear := by
  ext f
  constructor
  · intro hf
    rcases hf with ⟨Q, hQ⟩
    rcases (LinearMap.BilinMap.toQuadraticMap_surjective
      (R := ℝ) (M := sphereAmbient) (N := ℝ) Q) with ⟨B, rfl⟩
    refine ⟨B, ?_⟩
    ext p
    exact (hQ p).symm
  · rintro ⟨B, rfl⟩
    refine ⟨B.toQuadraticMap, ?_⟩
    intro p
    simp [sphereBilinRestrictionLinear, LinearMap.BilinMap.toQuadraticMap_apply]

theorem finiteDimensional_continuousSphereQuadraticSubmodule :
    FiniteDimensional ℝ continuousSphereQuadraticSubmodule := by
  rw [continuousSphereQuadraticSubmodule_eq_range_sphereBilinRestrictionLinear]
  exact LinearMap.finiteDimensional_range sphereBilinRestrictionLinear

theorem isClosed_continuousSphereQuadraticSubmodule :
    IsClosed (continuousSphereQuadraticSubmodule : Set C(spherePoint3, ℝ)) := by
  letI : FiniteDimensional ℝ continuousSphereQuadraticSubmodule :=
    finiteDimensional_continuousSphereQuadraticSubmodule
  exact Submodule.closed_of_finiteDimensional continuousSphereQuadraticSubmodule

def continuousSphereQuadraticClosedSubmodule :
    ClosedSubmodule ℝ C(spherePoint3, ℝ) :=
  ⟨continuousSphereQuadraticSubmodule, isClosed_continuousSphereQuadraticSubmodule⟩
