import Gleason.Harmonic.Fischer.FischerAmbient
import Gleason.Harmonic.Sectors.HarmonicBWitness
import Gleason.Continuity.Auxiliary.ContinuousEndpoint

noncomputable section

open Complex InnerProductSpace
open scoped Topology

def ambientBasisVec : Fin 3 → WithLp 2 (ℂ × ℝ)
  | 0 => complexOneVec
  | 1 => complexIVec
  | 2 => realUnitVec

lemma ambientCoordFun_add_smul_basisVec
    (i j : Fin 3) (x : WithLp 2 (ℂ × ℝ)) (t : ℝ) :
    ambientCoordFun j (x + t • ambientBasisVec i) =
      ambientCoordFun j x + t * if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ambientBasisVec, ambientCoordFun, complexProjL, realProjL, map_add, map_smul]

lemma hasDerivAt_ambientCoordFun_path
    (i j : Fin 3) (x : WithLp 2 (ℂ × ℝ)) :
    HasDerivAt (fun t : ℝ => ambientCoordFun j (x + t • ambientBasisVec i))
      (if i = j then 1 else 0) 0 := by
  simpa [ambientCoordFun_add_smul_basisVec, one_mul] using
    (((hasDerivAt_id 0).mul_const (if i = j then 1 else 0)).const_add (ambientCoordFun j x))

theorem hasDerivAt_ambientCoordMvEval_path_pderiv
    (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    HasDerivAt (fun t : ℝ => ambientCoordMvEval p (x + t • ambientBasisVec i))
      (ambientCoordMvEval (MvPolynomial.pderiv i p) x) 0 := by
  refine (MvPolynomial.induction_on
    (motive := fun p => ∀ x,
      HasDerivAt (fun t : ℝ => ambientCoordMvEval p (x + t • ambientBasisVec i))
        (ambientCoordMvEval (MvPolynomial.pderiv i p) x) 0)
    p ?_ ?_ ?_) x
  · intro a x
    simpa [ambientCoordMvEval] using
      (show HasDerivAt (fun _ : ℝ => a) 0 0 from hasDerivAt_const 0 a)
  · intro p q hp hq x
    simpa [map_add] using (hp x).add (hq x)
  · intro p j hp x
    have hcoord := hasDerivAt_ambientCoordFun_path i j x
    have hmul := hcoord.mul (hp x)
    have hXi : ambientCoordMvEval (MvPolynomial.X j) x = ambientCoordFun j x := by
      simpa [MvPolynomial.eval_X] using ambientCoordMvEval_apply (MvPolynomial.X j) x
    by_cases hij : j = i
    · subst hij
      simpa [map_mul, MvPolynomial.pderiv_X, Derivation.leibniz,
        Pi.mul_apply, Pi.add_apply, Pi.single_apply, hXi, smul_eq_mul, mul_comm, mul_left_comm,
        mul_assoc, add_comm, add_left_comm, add_assoc]
        using hmul
    · have hne : i ≠ j := by
        intro h
        exact hij h.symm
      simpa [map_mul, MvPolynomial.pderiv_X, Derivation.leibniz, hij, hne,
        Pi.mul_apply, Pi.add_apply, Pi.single_apply, hXi, smul_eq_mul, mul_comm, mul_left_comm,
        mul_assoc, add_comm, add_left_comm, add_assoc]
        using hmul

lemma ambientCoordFun_contDiff (i : Fin 3) : ContDiff ℝ 2 (ambientCoordFun i) := by
  fin_cases i
  · simpa [ambientCoordFun] using Complex.reCLM.contDiff.comp complexProjL.contDiff
  · simpa [ambientCoordFun] using Complex.imCLM.contDiff.comp complexProjL.contDiff
  · simpa [ambientCoordFun] using realProjL.contDiff

lemma ambientCoordMvEval_contDiff (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ 2 (ambientCoordMvEval p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa [ambientCoordMvEval] using (contDiff_const : ContDiff ℝ 2 fun _ : WithLp 2 (ℂ × ℝ) => a)
  | add p q hp hq =>
      convert hp.add hq using 1
      funext x
      simp [map_add]
  | mul_X p i hp =>
      convert hp.mul (ambientCoordFun_contDiff i) using 1
      funext x
      simp [map_mul]

theorem hasDerivAt_ambientCoordMvEval_line_pderiv
    (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (x : WithLp 2 (ℂ × ℝ)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ambientCoordMvEval p (x + t • ambientBasisVec i))
      (ambientCoordMvEval (MvPolynomial.pderiv i p) (x + s • ambientBasisVec i)) s := by
  let g : ℝ → ℝ := fun u => ambientCoordMvEval p ((x + s • ambientBasisVec i) + u • ambientBasisVec i)
  have hg : HasDerivAt g
      (ambientCoordMvEval (MvPolynomial.pderiv i p) (x + s • ambientBasisVec i)) 0 :=
    hasDerivAt_ambientCoordMvEval_path_pderiv i p (x + s • ambientBasisVec i)
  have hshift : HasDerivAt (fun t : ℝ => t - s) 1 s := by
    simpa [sub_eq_add_neg] using (hasDerivAt_id s).add_const (-s)
  have hcomp : HasDerivAt (g ∘ fun t : ℝ => t - s)
      (ambientCoordMvEval (MvPolynomial.pderiv i p) (x + s • ambientBasisVec i)) s :=
    by
      simpa using
        (HasDerivAt.comp_of_eq (x := s) (hh₂ := hg) (hh := hshift) (by simp))
  convert hcomp using 1
  · funext t
    have hpoint :
        x + s • ambientBasisVec i + (t - s) • ambientBasisVec i = x + t • ambientBasisVec i := by
      have hs : s + (t - s) = t := by ring
      calc
        x + s • ambientBasisVec i + (t - s) • ambientBasisVec i
            = x + ((s + (t - s)) • ambientBasisVec i) := by
                rw [add_assoc, ← add_smul]
        _ = x + t • ambientBasisVec i := by rw [hs]
    simp [g, hpoint]

theorem deriv_ambientCoordMvEval_line
    (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    deriv (fun t : ℝ => ambientCoordMvEval p (x + t • ambientBasisVec i)) =
      fun s => ambientCoordMvEval (MvPolynomial.pderiv i p) (x + s • ambientBasisVec i) := by
  funext s
  exact (hasDerivAt_ambientCoordMvEval_line_pderiv i p x s).deriv

theorem iteratedDeriv_two_ambientCoordMvEval_path
    (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    iteratedDeriv 2 (fun t : ℝ => ambientCoordMvEval p (x + t • ambientBasisVec i)) 0 =
      ambientCoordMvEval (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_ambientCoordMvEval_line]
  simpa using (hasDerivAt_ambientCoordMvEval_line_pderiv i (MvPolynomial.pderiv i p) x 0).deriv

theorem iteratedFDeriv_two_ambientCoordMvEval_basis
    (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    (iteratedFDeriv ℝ 2 (ambientCoordMvEval p) x) ![ambientBasisVec i, ambientBasisVec i] =
      ambientCoordMvEval (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) x := by
  rw [← iteratedDeriv_two_comp_add_smul ((ambientCoordMvEval_contDiff p).contDiffAt)]
  exact iteratedDeriv_two_ambientCoordMvEval_path i p x

@[simp] lemma complexRealBasis_apply_inl_zero :
    complexRealBasis (Sum.inl 0) = ambientBasisVec 0 := by
  simp [complexRealBasis, complexBasis, realBasis, ambientBasisVec, complexOneVec]

@[simp] lemma complexRealBasis_apply_inl_one :
    complexRealBasis (Sum.inl 1) = ambientBasisVec 1 := by
  simp [complexRealBasis, complexBasis, realBasis, ambientBasisVec, complexIVec]

@[simp] lemma complexRealBasis_apply_inr_zero :
    complexRealBasis (Sum.inr 0) = ambientBasisVec 2 := by
  simp [complexRealBasis, complexBasis, realBasis, ambientBasisVec, realUnitVec]

theorem ambientCoordMvEval_laplacian
    (p : MvPolynomial (Fin 3) ℝ) :
    Δ (ambientCoordMvEval p) = ambientCoordMvEval (polyLaplacian p) := by
  ext x
  have h0 := iteratedFDeriv_two_ambientCoordMvEval_basis 0 p x
  have h1 := iteratedFDeriv_two_ambientCoordMvEval_basis 1 p x
  have h2 := iteratedFDeriv_two_ambientCoordMvEval_basis 2 p x
  have h0' :
      (iteratedFDeriv ℝ 2 (ambientCoordMvEval p) x) ![WithLp.toLp 2 ((1 : ℂ), (0 : ℝ)),
          WithLp.toLp 2 ((1 : ℂ), (0 : ℝ))] =
        ambientCoordMvEval ((MvPolynomial.pderiv 0) ((MvPolynomial.pderiv 0) p)) x := by
    simpa [ambientBasisVec, complexOneVec] using h0
  have h1' :
      (iteratedFDeriv ℝ 2 (ambientCoordMvEval p) x) ![WithLp.toLp 2 (Complex.I, (0 : ℝ)),
          WithLp.toLp 2 (Complex.I, (0 : ℝ))] =
        ambientCoordMvEval ((MvPolynomial.pderiv 1) ((MvPolynomial.pderiv 1) p)) x := by
    simpa [ambientBasisVec, complexIVec] using h1
  have h2' :
      (iteratedFDeriv ℝ 2 (ambientCoordMvEval p) x) ![WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)),
          WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))] =
        ambientCoordMvEval ((MvPolynomial.pderiv 2) ((MvPolynomial.pderiv 2) p)) x := by
    simpa [ambientBasisVec, realUnitVec] using h2
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f := ambientCoordMvEval p) complexRealBasis]
  simp [polyLaplacian, LinearMap.add_apply, complexRealBasis, complexBasis, realBasis,
    OrthonormalBasis.prod_apply, Fin.sum_univ_two, add_assoc, add_left_comm, add_comm]
  rw [h1', h2', h0']
  simp [ambientCoordMvEval_apply, add_left_comm, add_comm]

theorem ambientCoordMvEval_harmonicAt_of_mem_harmonicPolyHomogeneousSubmodule
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ harmonicPolyHomogeneousSubmodule n) (x : WithLp 2 (ℂ × ℝ)) :
    HarmonicAt (ambientCoordMvEval p) x := by
  refine ⟨(ambientCoordMvEval_contDiff p).contDiffAt, ?_⟩
  have hker : polyLaplacian p = 0 := by
    simpa [LinearMap.mem_ker] using hp.2
  have hLap : Δ (ambientCoordMvEval p) = 0 := by
    ext y
    have hΔ := congrArg (fun f : WithLp 2 (ℂ × ℝ) → ℝ => f y) (ambientCoordMvEval_laplacian p)
    simpa [hker] using hΔ
  simp [hLap]

theorem harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule (n : ℕ) :
    (harmonicPolyHomogeneousSubmodule n).map sphereCoordMvEval.toLinearMap ≤
      continuousHarmonicSphereDegreeSubmodule n := by
  intro f hf
  rcases hf with ⟨p, hp, rfl⟩
  show (sphereCoordMvEval p : spherePoint3 → ℝ) ∈ harmonicSphereDegreeSubmodule n
  refine ⟨ambientCoordMvEval p, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x
      exact ambientCoordMvEval_harmonicAt_of_mem_harmonicPolyHomogeneousSubmodule hp x
    · intro t x
      exact ambientCoordMvEval_smul_of_homogeneous hp.1 t x
  · symm
    exact (sphereRestrictionLinear_ambientCoordMvEval p).symm

theorem homogeneousImage_le_continuousHarmonicSphere_sup_prev (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap ≤
      continuousHarmonicSphereDegreeSubmodule n ⊔
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap := by
  calc
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap
      ≤ (harmonicPolyHomogeneousSubmodule n).map sphereCoordMvEval.toLinearMap ⊔
          (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap :=
        homogeneousImage_le_harmonicPolyImage_sup_prev n
    _ ≤ continuousHarmonicSphereDegreeSubmodule n ⊔
          (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap :=
        sup_le_sup (harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule n) le_rfl
