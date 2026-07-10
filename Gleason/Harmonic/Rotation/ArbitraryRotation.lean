import Gleason.Harmonic.Zonal.NorthRotation
import Gleason.Harmonic.Sphere.SphereFrameQ02

noncomputable section

open Complex InnerProductSpace

abbrev sphereAmbient3 := WithLp 2 (ℂ × ℝ)

lemma sphereStdVec_orthonormal :
    Orthonormal ℝ (sphereTripleVec sphereE1 sphereE2 sphereE3) := by
  refine sphereTripleVec_orthonormal sphereE1 sphereE2 sphereE3 ?_ ?_ ?_
  · simpa using sphereE1_inner_sphereE2
  · simpa using sphereE1_inner_sphereE3
  · simpa using sphereE2_inner_sphereE3

lemma sphereTripleCardEqFinrank :
    Fintype.card (Fin 3) = Module.finrank ℝ sphereAmbient3 := by
  rw [finrank_real_withLp_complex_prod_real]
  norm_num

def sphereStdBasis : Module.Basis (Fin 3) ℝ sphereAmbient3 :=
  basisOfOrthonormalOfCardEqFinrank sphereStdVec_orthonormal sphereTripleCardEqFinrank

@[simp] lemma sphereStdBasis_apply (i : Fin 3) :
    sphereStdBasis i = sphereTripleVec sphereE1 sphereE2 sphereE3 i := by
  simpa [sphereStdBasis] using
    congrFun (coe_basisOfOrthonormalOfCardEqFinrank sphereStdVec_orthonormal sphereTripleCardEqFinrank)
      i

lemma sphereStdBasis_orthonormal :
    Orthonormal ℝ sphereStdBasis := by
  have hEq : (sphereStdBasis : Fin 3 → sphereAmbient3) = sphereTripleVec sphereE1 sphereE2 sphereE3 := by
    funext i
    simpa using sphereStdBasis_apply i
  simpa [hEq] using sphereStdVec_orthonormal

def sphereTripleBasis (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    Module.Basis (Fin 3) ℝ sphereAmbient3 :=
  basisOfOrthonormalOfCardEqFinrank
    (sphereTripleVec_orthonormal x y z hxy hxz hyz) sphereTripleCardEqFinrank

@[simp] lemma sphereTripleBasis_apply
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (i : Fin 3) :
    sphereTripleBasis x y z hxy hxz hyz i = sphereTripleVec x y z i := by
  simpa [sphereTripleBasis] using
    congrFun
      (coe_basisOfOrthonormalOfCardEqFinrank
        (sphereTripleVec_orthonormal x y z hxy hxz hyz) sphereTripleCardEqFinrank) i

lemma sphereTripleBasis_orthonormal
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    Orthonormal ℝ (sphereTripleBasis x y z hxy hxz hyz) := by
  have hEq :
      (sphereTripleBasis x y z hxy hxz hyz : Fin 3 → sphereAmbient3) = sphereTripleVec x y z := by
    funext i
    simpa using sphereTripleBasis_apply x y z hxy hxz hyz i
  simpa [hEq] using sphereTripleVec_orthonormal x y z hxy hxz hyz

def sphereTripleIsometryEquiv
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3 :=
  sphereStdBasis_orthonormal.equiv
    (sphereTripleBasis_orthonormal x y z hxy hxz hyz) (Equiv.refl _)

@[simp] lemma sphereTripleIsometryEquiv_apply_sphereE1
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereTripleIsometryEquiv x y z hxy hxz hyz sphereE1.1 = x.1 := by
  simpa [sphereTripleIsometryEquiv, sphereStdBasis_apply, sphereTripleBasis_apply, sphereTripleVec]
    using
      (Orthonormal.equiv_apply (hv := sphereStdBasis_orthonormal)
        (hv' := sphereTripleBasis_orthonormal x y z hxy hxz hyz)
        (e := Equiv.refl (Fin 3)) 0)

@[simp] lemma sphereTripleIsometryEquiv_apply_sphereE2
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereTripleIsometryEquiv x y z hxy hxz hyz sphereE2.1 = y.1 := by
  simpa [sphereTripleIsometryEquiv, sphereStdBasis_apply, sphereTripleBasis_apply, sphereTripleVec]
    using
      (Orthonormal.equiv_apply (hv := sphereStdBasis_orthonormal)
        (hv' := sphereTripleBasis_orthonormal x y z hxy hxz hyz)
        (e := Equiv.refl (Fin 3)) 1)

@[simp] lemma sphereTripleIsometryEquiv_apply_sphereE3
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereTripleIsometryEquiv x y z hxy hxz hyz sphereE3.1 = z.1 := by
  simpa [sphereTripleIsometryEquiv, sphereStdBasis_apply, sphereTripleBasis_apply, sphereTripleVec]
    using
      (Orthonormal.equiv_apply (hv := sphereStdBasis_orthonormal)
        (hv' := sphereTripleBasis_orthonormal x y z hxy hxz hyz)
        (e := Equiv.refl (Fin 3)) 2)

@[simp] lemma sphereMap_sphereTripleIsometryEquiv_sphereE1
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereMap (sphereTripleIsometryEquiv x y z hxy hxz hyz) sphereE1 = x := by
  apply Subtype.ext
  simpa using sphereTripleIsometryEquiv_apply_sphereE1 x y z hxy hxz hyz

@[simp] lemma sphereMap_sphereTripleIsometryEquiv_sphereE2
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereMap (sphereTripleIsometryEquiv x y z hxy hxz hyz) sphereE2 = y := by
  apply Subtype.ext
  simpa using sphereTripleIsometryEquiv_apply_sphereE2 x y z hxy hxz hyz

@[simp] lemma sphereMap_sphereTripleIsometryEquiv_sphereE3
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereMap (sphereTripleIsometryEquiv x y z hxy hxz hyz) sphereE3 = z := by
  apply Subtype.ext
  simpa using sphereTripleIsometryEquiv_apply_sphereE3 x y z hxy hxz hyz

theorem two_mul_northEquatorAverageLinear_spherePrecomp_sphereTripleIsometryEquiv_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    2 * northEquatorAverageLinear
        (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f) =
      f x + f y := by
  have hmem :
      spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f ∈ continuousSphereFrameSubmodule := by
    exact continuousSphereFrameSubmodule_invariant_under_spherePrecomp
      (sphereTripleIsometryEquiv x y z hxy hxz hyz) hf
  simpa [spherePrecomp_apply] using
    two_mul_northEquatorAverageLinear_apply_of_mem_continuousSphereFrameSubmodule hmem

theorem sphereFrameCenter_spherePrecomp_sphereTripleIsometryEquiv_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereFrameCenter (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f) =
      sphereFrameCenter f := by
  have hframe : IsSphereFrameFunction (f : spherePoint3 → ℝ) := hf
  have hsum := hframe x y z hxy hxz hyz
  unfold sphereFrameCenter
  simp [spherePrecomp_apply, hsum]

theorem northEquatorAverageCLM_centered_spherePrecomp_sphereTripleIsometryEquiv_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    northEquatorAverageLinear
        (sphereFrameCentered (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f)) =
      -((sphereFrameCentered f) z) / 2 := by
  have hmem :
      spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f ∈ continuousSphereFrameSubmodule := by
    exact continuousSphereFrameSubmodule_invariant_under_spherePrecomp
      (sphereTripleIsometryEquiv x y z hxy hxz hyz) hf
  rw [northEquatorAverageCLM_centered_of_mem_continuousSphereFrameSubmodule hmem]
  rw [sphereFrameCentered_apply, sphereFrameCentered_apply]
  simp [spherePrecomp_apply,
    sphereFrameCenter_spherePrecomp_sphereTripleIsometryEquiv_of_mem_continuousSphereFrameSubmodule
      hf x y z hxy hxz hyz]
