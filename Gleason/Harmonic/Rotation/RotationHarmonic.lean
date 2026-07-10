import Gleason.Harmonic.Rotation.RotationFrame
import Gleason.Continuity.Auxiliary.ContinuousEndpoint
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open Complex InnerProductSpace

def ambientPrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    (WithLp 2 (ℂ × ℝ) → ℝ) →ₗ[ℝ] (WithLp 2 (ℂ × ℝ) → ℝ) where
  toFun f := f ∘ e
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

lemma sphereRestrictionLinear_ambientPrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : WithLp 2 (ℂ × ℝ) → ℝ) :
    sphereRestrictionLinear (ambientPrecomp e f) =
      spherePrecompPi e (sphereRestrictionLinear f) := by
  ext x
  rfl

lemma contDiff_two_of_harmonicHomogeneousDegree
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) :
    ContDiff ℝ 2 f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (hf.1 x).1

theorem laplacian_linearIsometryEquiv_comp_right
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    Δ (f ∘ e) = (Δ f) ∘ e := by
  ext x
  let vG :
      OrthonormalBasis (Fin (Module.finrank ℝ (WithLp 2 (ℂ × ℝ)))) ℝ
        (WithLp 2 (ℂ × ℝ)) :=
    stdOrthonormalBasis ℝ (WithLp 2 (ℂ × ℝ))
  let vE :
      OrthonormalBasis (Fin (Module.finrank ℝ (WithLp 2 (ℂ × ℝ)))) ℝ
        (WithLp 2 (ℂ × ℝ)) :=
    ((vG.toBasis.map e.toLinearEquiv).toOrthonormalBasis
      (vG.orthonormal.mapLinearIsometryEquiv e))
  have hcomp :
      iteratedFDeriv ℝ 2 (f ∘ e) x =
        (iteratedFDeriv ℝ 2 f (e x)).compContinuousLinearMap fun _ => e.toContinuousLinearMap := by
    simpa using
      (e.toContinuousLinearMap.iteratedFDeriv_comp_right
        (f := f) hf x (i := 2) (by simp))
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f := f ∘ e) vG]
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f := f) vE]
  change
    ∑ i, (iteratedFDeriv ℝ 2 (f ∘ e) x) ![vG i, vG i] =
      ∑ i, (iteratedFDeriv ℝ 2 f (e x)) ![vE i, vE i]
  rw [hcomp]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply congrArg (iteratedFDeriv ℝ 2 f (e x))
  ext j
  fin_cases j <;> rfl

theorem HarmonicHomogeneousDegree.comp_linearIsometryEquiv
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f)
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    HarmonicHomogeneousDegree n (f ∘ e) := by
  constructor
  · intro x
    constructor
    · exact
        by
          simpa using
            (e.toContinuousLinearEquiv.contDiffAt_comp_iff (f := f) (x := e x)).2
              (hf.1 (e x)).1
    · rw [laplacian_linearIsometryEquiv_comp_right e (contDiff_two_of_harmonicHomogeneousDegree hf)]
      exact e.continuousAt.tendsto.eventually (hf.1 (e x)).2
  · intro t x
    simp [hf.2 t (e x)]

theorem harmonicHomogeneousDegreeSubmodule_invariant_under_ambientPrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (n : ℕ) :
    harmonicHomogeneousDegreeSubmodule n ≤
      (harmonicHomogeneousDegreeSubmodule n).comap (ambientPrecomp e) := by
  intro f hf
  exact hf.comp_linearIsometryEquiv e

theorem harmonicSphereDegreeSubmodule_invariant_under_spherePrecompPi
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (n : ℕ) :
    harmonicSphereDegreeSubmodule n ≤
      (harmonicSphereDegreeSubmodule n).comap (spherePrecompPi e) := by
  intro g hg
  rcases hg with ⟨f, hf, rfl⟩
  show spherePrecompPi e (sphereRestrictionLinear f) ∈ harmonicSphereDegreeSubmodule n
  refine ⟨ambientPrecomp e f, ?_, ?_⟩
  · exact hf.comp_linearIsometryEquiv e
  · exact (sphereRestrictionLinear_ambientPrecomp e f).symm

theorem continuousHarmonicSphereDegreeSubmodule_invariant_under_spherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (n : ℕ) :
    continuousHarmonicSphereDegreeSubmodule n ≤
      (continuousHarmonicSphereDegreeSubmodule n).comap (spherePrecomp e) := by
  intro g hg
  show ((spherePrecomp e g : C(spherePoint3, ℝ)) : spherePoint3 → ℝ) ∈
      harmonicSphereDegreeSubmodule n
  exact harmonicSphereDegreeSubmodule_invariant_under_spherePrecompPi e n hg
