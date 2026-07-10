import Gleason.Continuity.Auxiliary.ClosedFrame
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section

open Complex InnerProductSpace

def sphereMap
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    spherePoint3 → spherePoint3 :=
  fun x => ⟨e x.1, by simpa [e.norm_map] using x.2⟩

lemma continuous_sphereMap
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    Continuous (sphereMap e) := by
  exact (e.toHomeomorph.continuous.comp continuous_subtype_val).subtype_mk fun x =>
    by simpa [sphereMap, e.norm_map] using x.2

@[simp] lemma sphereMap_apply_val
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (x : spherePoint3) :
    (sphereMap e x).1 = e x.1 := rfl

@[simp] lemma sphereMap_inner
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (x y : spherePoint3) :
    inner (𝕜 := ℝ) (sphereMap e x).1 (sphereMap e y).1 =
      inner (𝕜 := ℝ) x.1 y.1 := by
  simpa using e.inner_map_map x.1 y.1

def spherePrecompPi
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    (spherePoint3 → ℝ) →ₗ[ℝ] (spherePoint3 → ℝ) where
  toFun f := fun x => f (sphereMap e x)
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

def spherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ) where
  toFun f := ⟨fun x => f (sphereMap e x), f.continuous.comp (continuous_sphereMap e)⟩
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

@[simp] lemma spherePrecomp_apply
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : C(spherePoint3, ℝ)) (x : spherePoint3) :
    spherePrecomp e f x = f (sphereMap e x) := rfl

theorem isSphereFrameFunction_comp_sphereMap
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    {f : spherePoint3 → ℝ}
    (hf : IsSphereFrameFunction f) :
    IsSphereFrameFunction (fun x => f (sphereMap e x)) := by
  intro x y z hxy hxz hyz
  have hxy' :
      inner (𝕜 := ℝ) (sphereMap e x).1 (sphereMap e y).1 = 0 := by
    simpa [sphereMap_inner] using hxy
  have hxz' :
      inner (𝕜 := ℝ) (sphereMap e x).1 (sphereMap e z).1 = 0 := by
    simpa [sphereMap_inner] using hxz
  have hyz' :
      inner (𝕜 := ℝ) (sphereMap e y).1 (sphereMap e z).1 = 0 := by
    simpa [sphereMap_inner] using hyz
  have hE12 :
      inner (𝕜 := ℝ) (sphereMap e sphereE1).1 (sphereMap e sphereE2).1 = 0 := by
    simpa [sphereMap_inner] using sphereE1_inner_sphereE2
  have hE13 :
      inner (𝕜 := ℝ) (sphereMap e sphereE1).1 (sphereMap e sphereE3).1 = 0 := by
    simpa [sphereMap_inner] using sphereE1_inner_sphereE3
  have hE23 :
      inner (𝕜 := ℝ) (sphereMap e sphereE2).1 (sphereMap e sphereE3).1 = 0 := by
    simpa [sphereMap_inner] using sphereE2_inner_sphereE3
  have hconst :=
    hf (sphereMap e sphereE1) (sphereMap e sphereE2) (sphereMap e sphereE3) hE12 hE13 hE23
  calc
    f (sphereMap e x) + f (sphereMap e y) + f (sphereMap e z)
        = f sphereE1 + f sphereE2 + f sphereE3 := hf (sphereMap e x) (sphereMap e y)
            (sphereMap e z) hxy' hxz' hyz'
    _ = f (sphereMap e sphereE1) + f (sphereMap e sphereE2) + f (sphereMap e sphereE3) :=
      hconst.symm

theorem sphereFrameSubmodule_invariant_under_spherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    sphereFrameSubmodule ≤ sphereFrameSubmodule.comap (spherePrecompPi e) := by
  intro f hf
  show IsSphereFrameFunction ((spherePrecompPi e) f : spherePoint3 → ℝ)
  exact isSphereFrameFunction_comp_sphereMap e hf

theorem continuousSphereFrameSubmodule_invariant_under_spherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    continuousSphereFrameSubmodule ≤
      continuousSphereFrameSubmodule.comap (spherePrecomp e) := by
  intro f hf
  show IsSphereFrameFunction ((spherePrecomp e f : C(spherePoint3, ℝ)) : spherePoint3 → ℝ)
  exact isSphereFrameFunction_comp_sphereMap e hf
