import Gleason.Harmonic.Fischer.FischerNorthRotation
import Gleason.Harmonic.Rotation.RotationEquiv
import Mathlib.Algebra.Module.LinearMap.Polynomial

noncomputable section

open Complex InnerProductSpace

def ambientCoordL : Fin 3 → sphereAmbient3 →ₗ[ℝ] ℝ
  | 0 => Complex.reCLM.comp complexProjL
  | 1 => Complex.imCLM.comp complexProjL
  | 2 => realProjL

@[simp] lemma ambientCoordL_apply (x : sphereAmbient3) (i : Fin 3) :
    ambientCoordL i x = ambientCoordFun i x := by
  fin_cases i <;> rfl

lemma sphereStdBasis_repr_eq_ambientCoordFun
    (x : sphereAmbient3) (i : Fin 3) :
    sphereStdBasis.repr x i = ambientCoordFun i x := by
  have hsum := congrArg (fun y : sphereAmbient3 => ambientCoordL i y) (sphereStdBasis.sum_repr x)
  fin_cases i
  ·
    have h := hsum
    simp [ambientCoordL, ambientCoordFun, sphereStdBasis_apply, sphereTripleVec,
      Fin.sum_univ_three, sphereE1, sphereE2, sphereE3] at h
    exact h
  ·
    have h := hsum
    simp [ambientCoordL, ambientCoordFun, sphereStdBasis_apply, sphereTripleVec,
      Fin.sum_univ_three, sphereE1, sphereE2, sphereE3] at h
    exact h
  ·
    have h := hsum
    simp [ambientCoordL, ambientCoordFun, sphereStdBasis_apply, sphereTripleVec,
      Fin.sum_univ_three, sphereE1, sphereE2, sphereE3] at h
    exact h

def linearIsometryCoordPoly
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    (i : Fin 3) :
    MvPolynomial (Fin 3) ℝ :=
  LinearMap.toMvPolynomial sphereStdBasis sphereStdBasis (e : sphereAmbient3 →ₗ[ℝ] sphereAmbient3) i

def linearIsometryPoly
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3) :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval (linearIsometryCoordPoly e)

lemma linearIsometryCoordPoly_homogeneous
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3) (i : Fin 3) :
    (linearIsometryCoordPoly e i).IsHomogeneous 1 := by
  simpa [linearIsometryCoordPoly] using
    LinearMap.toMvPolynomial_isHomogeneous
      (b₁ := sphereStdBasis) (b₂ := sphereStdBasis)
      (f := (e : sphereAmbient3 →ₗ[ℝ] sphereAmbient3)) i

lemma ambientCoordMvEval_linearIsometryCoordPoly
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    (i : Fin 3) (x : sphereAmbient3) :
    MvPolynomial.eval (fun j => ambientCoordFun j x) (linearIsometryCoordPoly e i) =
      ambientCoordFun i (e x) := by
  calc
    MvPolynomial.eval (fun j => ambientCoordFun j x) (linearIsometryCoordPoly e i)
        = MvPolynomial.eval (sphereStdBasis.repr x) (linearIsometryCoordPoly e i) := by
            rw [show (fun j => ambientCoordFun j x) = sphereStdBasis.repr x by
              funext j
              exact (sphereStdBasis_repr_eq_ambientCoordFun x j).symm]
    _ = sphereStdBasis.repr
          ((e : sphereAmbient3 →ₗ[ℝ] sphereAmbient3)
            (sphereStdBasis.repr.symm (sphereStdBasis.repr x))) i := by
          simpa [linearIsometryCoordPoly] using
            LinearMap.toMvPolynomial_eval_eq_apply
              (b₁ := sphereStdBasis) (b₂ := sphereStdBasis)
              (f := (e : sphereAmbient3 →ₗ[ℝ] sphereAmbient3)) i (sphereStdBasis.repr x)
    _ = ambientCoordFun i (e x) := by
          rw [show sphereStdBasis.repr.symm (sphereStdBasis.repr x) = x by
            exact LinearEquiv.symm_apply_apply sphereStdBasis.repr x]
          rw [sphereStdBasis_repr_eq_ambientCoordFun]
          rfl

theorem ambientCoordMvEval_linearIsometryPoly
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    (p : MvPolynomial (Fin 3) ℝ) :
    ambientCoordMvEval (linearIsometryPoly e p) =
      ambientPrecomp e (ambientCoordMvEval p) := by
  refine MvPolynomial.induction_on
    (motive := fun p =>
      ambientCoordMvEval (linearIsometryPoly e p) =
        ambientPrecomp e (ambientCoordMvEval p))
    p ?_ ?_ ?_
  · intro a
    ext x
    simp [linearIsometryPoly, ambientPrecomp]
  · intro p q hp hq
    ext x
    have hp' := congrFun hp x
    have hq' := congrFun hq x
    change ambientCoordMvEval (linearIsometryPoly e p) x =
      ambientCoordMvEval p (e x) at hp'
    change ambientCoordMvEval (linearIsometryPoly e q) x =
      ambientCoordMvEval q (e x) at hq'
    rw [ambientCoordMvEval_apply, ambientCoordMvEval_apply] at hp' hq'
    change ambientCoordMvEval (linearIsometryPoly e (p + q)) x =
      ambientCoordMvEval (p + q) (e x)
    rw [map_add, ambientCoordMvEval_apply, ambientCoordMvEval_apply, MvPolynomial.eval_add,
      MvPolynomial.eval_add]
    exact congrArg₂ (· + ·) hp' hq'
  · intro p i hp
    ext x
    have hp' := congrFun hp x
    change ambientCoordMvEval (linearIsometryPoly e p) x =
      ambientCoordMvEval p (e x) at hp'
    rw [ambientCoordMvEval_apply, ambientCoordMvEval_apply] at hp'
    change ambientCoordMvEval (linearIsometryPoly e (p * MvPolynomial.X i)) x =
      ambientCoordMvEval (p * MvPolynomial.X i) (e x)
    rw [map_mul, ambientCoordMvEval_apply, ambientCoordMvEval_apply,
      MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X, hp']
    have hXi :
        (MvPolynomial.eval (fun j => ambientCoordFun j x))
            ((linearIsometryPoly e) (MvPolynomial.X i)) =
          ambientCoordFun i (e x) := by
      simpa [linearIsometryPoly] using ambientCoordMvEval_linearIsometryCoordPoly e i x
    simpa using
      congrArg
        (fun z =>
          (MvPolynomial.eval (fun j => ambientCoordFun j (e x)) p) * z) hXi

theorem linearIsometryPoly_mem_homogeneousSubmodule
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    linearIsometryPoly e p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
  simpa [linearIsometryPoly, one_mul] using
    MvPolynomial.IsHomogeneous.aeval (τ := Fin 3) (S := ℝ) hp
      (linearIsometryCoordPoly e) (linearIsometryCoordPoly_homogeneous e)

theorem linearIsometryPoly_polyLaplacian_of_homogeneous
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    polyLaplacian (linearIsometryPoly e p) = linearIsometryPoly e (polyLaplacian p) := by
  have hleft :
      (polyLaplacian (linearIsometryPoly e p)).IsHomogeneous (n - 2) := by
    exact polyLaplacian_mem_homogeneousSubmodule
      (linearIsometryPoly_mem_homogeneousSubmodule e hp)
  have hright :
      (linearIsometryPoly e (polyLaplacian p)).IsHomogeneous (n - 2) := by
    exact linearIsometryPoly_mem_homogeneousSubmodule e
      (polyLaplacian_mem_homogeneousSubmodule hp)
  apply MvPolynomial.IsHomogeneous.funext hleft hright
  intro r
  let x := ambientPointOfCoords r
  have hcomp :
      ambientCoordMvEval (polyLaplacian (linearIsometryPoly e p)) x =
        ambientCoordMvEval (linearIsometryPoly e (polyLaplacian p)) x := by
    calc
      ambientCoordMvEval (polyLaplacian (linearIsometryPoly e p)) x
          = Δ (ambientCoordMvEval (linearIsometryPoly e p)) x := by
              symm
              exact congrFun (ambientCoordMvEval_laplacian (linearIsometryPoly e p)) x
      _ = Δ (ambientPrecomp e (ambientCoordMvEval p)) x := by
            rw [ambientCoordMvEval_linearIsometryPoly]
      _ = Δ (ambientCoordMvEval p) (e x) := by
            simpa using
              congrFun
                (laplacian_linearIsometryEquiv_comp_right e
                  (ambientCoordMvEval_contDiff p)) x
      _ = ambientCoordMvEval (polyLaplacian p) (e x) := by
            exact congrFun (ambientCoordMvEval_laplacian p) (e x)
      _ = ambientCoordMvEval (linearIsometryPoly e (polyLaplacian p)) x := by
            rw [ambientCoordMvEval_linearIsometryPoly]
            rfl
  calc
    MvPolynomial.eval r (polyLaplacian (linearIsometryPoly e p))
        = ambientCoordMvEval (polyLaplacian (linearIsometryPoly e p)) x := by
            rw [ambientCoordMvEval_apply]
            simp [x, ambientCoordFun_ambientPointOfCoords]
    _ = ambientCoordMvEval (linearIsometryPoly e (polyLaplacian p)) x := hcomp
    _ = MvPolynomial.eval r (linearIsometryPoly e (polyLaplacian p)) := by
            rw [ambientCoordMvEval_apply]
            simp [x, ambientCoordFun_ambientPointOfCoords]

theorem linearIsometryPoly_mem_harmonicPolyHomogeneousSubmodule
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ harmonicPolyHomogeneousSubmodule n) :
    linearIsometryPoly e p ∈ harmonicPolyHomogeneousSubmodule n := by
  refine ⟨linearIsometryPoly_mem_homogeneousSubmodule e hp.1, ?_⟩
  change polyLaplacian (linearIsometryPoly e p) = 0
  rw [linearIsometryPoly_polyLaplacian_of_homogeneous e hp.1]
  have hpker : polyLaplacian p = 0 := by
    simpa [harmonicPolyHomogeneousSubmodule, LinearMap.mem_ker] using hp.2
  rw [hpker, map_zero]

theorem spherePrecomp_mem_harmonicPolyHomogeneousImageSubmodule
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    {n : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule n) :
    spherePrecomp e f ∈ harmonicPolyHomogeneousImageSubmodule n := by
  rcases hf with ⟨p, hp, rfl⟩
  refine ⟨linearIsometryPoly e p, linearIsometryPoly_mem_harmonicPolyHomogeneousSubmodule e hp, ?_⟩
  have h := congrArg sphereRestrictionLinear (ambientCoordMvEval_linearIsometryPoly e p)
  have h' :
      ((sphereCoordMvEval (linearIsometryPoly e p) : C(spherePoint3, ℝ)) : spherePoint3 → ℝ) =
        spherePrecompPi e (sphereCoordMvEval p : spherePoint3 → ℝ) := by
    simpa [sphereRestrictionLinear_ambientCoordMvEval, sphereRestrictionLinear_ambientPrecomp]
      using h
  ext x
  change sphereCoordMvEval (linearIsometryPoly e p) x =
    spherePrecomp e (sphereCoordMvEval p) x
  simpa [spherePrecomp_apply, spherePrecompPi] using congrFun h' x

theorem harmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    (n : ℕ) :
    (harmonicPolyHomogeneousImageSubmodule n).map (spherePrecompLinearEquiv e).toLinearMap =
      harmonicPolyHomogeneousImageSubmodule n := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro f hf
    exact spherePrecomp_mem_harmonicPolyHomogeneousImageSubmodule e hf
  · intro f hf
    refine ⟨(spherePrecompLinearEquiv e).symm f, ?_, ?_⟩
    · simpa [spherePrecompLinearEquiv] using
        spherePrecomp_mem_harmonicPolyHomogeneousImageSubmodule e.symm hf
    · ext x
      simp [spherePrecompLinearEquiv, spherePrecomp]
