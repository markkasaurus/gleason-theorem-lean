import Gleason.Harmonic.Fischer.FischerExact
import Gleason.Harmonic.Rotation.RotationHarmonic
import Gleason.Harmonic.Zonal.NorthRotation
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section

open Complex InnerProductSpace

def northRotationCoordPoly (t : ℝ) : Fin 3 → MvPolynomial (Fin 3) ℝ
  | 0 => (Real.cos t) • MvPolynomial.X 0 - (Real.sin t) • MvPolynomial.X 1
  | 1 => (Real.sin t) • MvPolynomial.X 0 + (Real.cos t) • MvPolynomial.X 1
  | 2 => MvPolynomial.X 2

def northRotationPoly (t : ℝ) : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval (northRotationCoordPoly t)

lemma northRotationCoordPoly_homogeneous (t : ℝ) (i : Fin 3) :
    (northRotationCoordPoly t i).IsHomogeneous 1 := by
  fin_cases i
  ·
    have h0 :
        (((MvPolynomial.C (Real.cos t)) : MvPolynomial (Fin 3) ℝ) * MvPolynomial.X 0).IsHomogeneous 1 := by
      exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X _ _)
    have h1 :
        (((MvPolynomial.C (Real.sin t)) : MvPolynomial (Fin 3) ℝ) * MvPolynomial.X 1).IsHomogeneous 1 := by
      exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X _ _)
    simpa [northRotationCoordPoly, Algebra.smul_def, sub_eq_add_neg] using h0.sub h1
  ·
    have h0 :
        (((MvPolynomial.C (Real.sin t)) : MvPolynomial (Fin 3) ℝ) * MvPolynomial.X 0).IsHomogeneous 1 := by
      exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X _ _)
    have h1 :
        (((MvPolynomial.C (Real.cos t)) : MvPolynomial (Fin 3) ℝ) * MvPolynomial.X 1).IsHomogeneous 1 := by
      exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X _ _)
    simpa [northRotationCoordPoly, Algebra.smul_def] using h0.add h1
  · simpa [northRotationCoordPoly] using (MvPolynomial.isHomogeneous_X (R := ℝ) 2)

lemma ambientCoordFun_northRotation_zero
    (t : ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    ambientCoordFun 0 (northRotation t x) =
      Real.cos t * ambientCoordFun 0 x - Real.sin t * ambientCoordFun 1 x := by
  have hRe : (Complex.exp (Complex.I * t)).re = Real.cos t := by
    simpa [mul_comm] using congrArg Complex.re (Complex.exp_mul_I t)
  have hIm : (Complex.exp (Complex.I * t)).im = Real.sin t := by
    simpa [mul_comm] using congrArg Complex.im (Complex.exp_mul_I t)
  simp [ambientCoordFun, northRotation_apply, complexProjL, Complex.mul_re, sub_eq_add_neg,
    hRe, hIm, mul_comm, mul_left_comm, mul_assoc]

lemma ambientCoordFun_northRotation_one
    (t : ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    ambientCoordFun 1 (northRotation t x) =
      Real.sin t * ambientCoordFun 0 x + Real.cos t * ambientCoordFun 1 x := by
  have hRe : (Complex.exp (Complex.I * t)).re = Real.cos t := by
    simpa [mul_comm] using congrArg Complex.re (Complex.exp_mul_I t)
  have hIm : (Complex.exp (Complex.I * t)).im = Real.sin t := by
    simpa [mul_comm] using congrArg Complex.im (Complex.exp_mul_I t)
  simp [ambientCoordFun, northRotation_apply, complexProjL, Complex.mul_im,
    hRe, hIm, mul_comm]
  ring

lemma ambientCoordFun_northRotation_two
    (t : ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    ambientCoordFun 2 (northRotation t x) = ambientCoordFun 2 x := by
  simp [ambientCoordFun, northRotation_apply, realProjL]

theorem ambientCoordMvEval_northRotationPoly
    (t : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    ambientCoordMvEval (northRotationPoly t p) =
      ambientPrecomp (northRotation t) (ambientCoordMvEval p) := by
  refine MvPolynomial.induction_on
    (motive := fun p =>
      ambientCoordMvEval (northRotationPoly t p) =
        ambientPrecomp (northRotation t) (ambientCoordMvEval p))
    p ?_ ?_ ?_
  · intro a
    ext x
    simp [northRotationPoly, ambientPrecomp]
  · intro p q hp hq
    ext x
    have hp' := congrFun hp x
    have hq' := congrFun hq x
    change ambientCoordMvEval (northRotationPoly t p) x =
      ambientCoordMvEval p (northRotation t x) at hp'
    change ambientCoordMvEval (northRotationPoly t q) x =
      ambientCoordMvEval q (northRotation t x) at hq'
    rw [ambientCoordMvEval_apply, ambientCoordMvEval_apply] at hp' hq'
    change ambientCoordMvEval (northRotationPoly t (p + q)) x =
      ambientCoordMvEval (p + q) (northRotation t x)
    rw [map_add, ambientCoordMvEval_apply, ambientCoordMvEval_apply, MvPolynomial.eval_add,
      MvPolynomial.eval_add]
    exact congrArg₂ (· + ·) hp' hq'
  · intro p i hp
    ext x
    have hp' := congrFun hp x
    change ambientCoordMvEval (northRotationPoly t p) x =
      ambientCoordMvEval p (northRotation t x) at hp'
    rw [ambientCoordMvEval_apply, ambientCoordMvEval_apply] at hp'
    change ambientCoordMvEval (northRotationPoly t (p * MvPolynomial.X i)) x =
      ambientCoordMvEval (p * MvPolynomial.X i) (northRotation t x)
    rw [map_mul, ambientCoordMvEval_apply, ambientCoordMvEval_apply,
      MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X, hp']
    fin_cases i
    ·
      have hXi :
          (MvPolynomial.eval (fun i => ambientCoordFun i x))
              ((northRotationPoly t) (MvPolynomial.X 0)) =
            ambientCoordFun 0 (northRotation t x) := by
        simpa [northRotationPoly, northRotationCoordPoly, Algebra.smul_def] using
          (ambientCoordFun_northRotation_zero t x).symm
      simpa using
        congrArg
          (fun z =>
            (MvPolynomial.eval (fun i => ambientCoordFun i ((northRotation t) x)) p) * z) hXi
    ·
      have hXi :
          (MvPolynomial.eval (fun i => ambientCoordFun i x))
              ((northRotationPoly t) (MvPolynomial.X 1)) =
            ambientCoordFun 1 (northRotation t x) := by
        simpa [northRotationPoly, northRotationCoordPoly, Algebra.smul_def] using
          (ambientCoordFun_northRotation_one t x).symm
      simpa using
        congrArg
          (fun z =>
            (MvPolynomial.eval (fun i => ambientCoordFun i ((northRotation t) x)) p) * z) hXi
    ·
      have hXi :
          (MvPolynomial.eval (fun i => ambientCoordFun i x))
              ((northRotationPoly t) (MvPolynomial.X 2)) =
            ambientCoordFun 2 (northRotation t x) := by
        simpa [northRotationPoly, northRotationCoordPoly] using
          (ambientCoordFun_northRotation_two t x).symm
      simpa using
        congrArg
          (fun z =>
            (MvPolynomial.eval (fun i => ambientCoordFun i ((northRotation t) x)) p) * z) hXi

theorem northRotationPoly_mem_homogeneousSubmodule
    (t : ℝ) {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    northRotationPoly t p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
  simpa [northRotationPoly, one_mul] using
    MvPolynomial.IsHomogeneous.aeval (τ := Fin 3) (S := ℝ) hp
      (northRotationCoordPoly t) (northRotationCoordPoly_homogeneous t)

def ambientPointOfCoords (r : Fin 3 → ℝ) : WithLp 2 (ℂ × ℝ) :=
  WithLp.toLp 2 ((r 0 : ℂ) + Complex.I * (r 1 : ℂ), r 2)

@[simp] lemma ambientCoordFun_ambientPointOfCoords
    (r : Fin 3 → ℝ) (i : Fin 3) :
    ambientCoordFun i (ambientPointOfCoords r) = r i := by
  fin_cases i <;>
    simp [ambientPointOfCoords, ambientCoordFun, complexProjL, realProjL]

theorem northRotationPoly_polyLaplacian_of_homogeneous
    (t : ℝ) {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    polyLaplacian (northRotationPoly t p) = northRotationPoly t (polyLaplacian p) := by
  have hleft :
      (polyLaplacian (northRotationPoly t p)).IsHomogeneous (n - 2) := by
    exact polyLaplacian_mem_homogeneousSubmodule
      (northRotationPoly_mem_homogeneousSubmodule t hp)
  have hright :
      (northRotationPoly t (polyLaplacian p)).IsHomogeneous (n - 2) := by
    exact northRotationPoly_mem_homogeneousSubmodule t
      (polyLaplacian_mem_homogeneousSubmodule hp)
  apply MvPolynomial.IsHomogeneous.funext hleft hright
  intro r
  let x := ambientPointOfCoords r
  have hcomp :
      ambientCoordMvEval (polyLaplacian (northRotationPoly t p)) x =
        ambientCoordMvEval (northRotationPoly t (polyLaplacian p)) x := by
    calc
      ambientCoordMvEval (polyLaplacian (northRotationPoly t p)) x
          = Δ (ambientCoordMvEval (northRotationPoly t p)) x := by
              symm
              exact congrFun (ambientCoordMvEval_laplacian (northRotationPoly t p)) x
      _ = Δ (ambientPrecomp (northRotation t) (ambientCoordMvEval p)) x := by
            rw [ambientCoordMvEval_northRotationPoly]
      _ = Δ (ambientCoordMvEval p) (northRotation t x) := by
            simpa using
              congrFun
                (laplacian_linearIsometryEquiv_comp_right (northRotation t)
                  (ambientCoordMvEval_contDiff p)) x
      _ = ambientCoordMvEval (polyLaplacian p) (northRotation t x) := by
            exact congrFun (ambientCoordMvEval_laplacian p) (northRotation t x)
      _ = ambientCoordMvEval (northRotationPoly t (polyLaplacian p)) x := by
            rw [ambientCoordMvEval_northRotationPoly]
            rfl
  calc
    MvPolynomial.eval r (polyLaplacian (northRotationPoly t p))
        = ambientCoordMvEval (polyLaplacian (northRotationPoly t p)) x := by
            rw [ambientCoordMvEval_apply]
            simp [x, ambientCoordFun_ambientPointOfCoords]
    _ = ambientCoordMvEval (northRotationPoly t (polyLaplacian p)) x := hcomp
    _ = MvPolynomial.eval r (northRotationPoly t (polyLaplacian p)) := by
            rw [ambientCoordMvEval_apply]
            simp [x, ambientCoordFun_ambientPointOfCoords]

theorem northRotationPoly_mem_harmonicPolyHomogeneousSubmodule
    (t : ℝ) {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ harmonicPolyHomogeneousSubmodule n) :
    northRotationPoly t p ∈ harmonicPolyHomogeneousSubmodule n := by
  refine ⟨northRotationPoly_mem_homogeneousSubmodule t hp.1, ?_⟩
  change polyLaplacian (northRotationPoly t p) = 0
  rw [northRotationPoly_polyLaplacian_of_homogeneous t hp.1]
  have hpker : polyLaplacian p = 0 := by
    simpa [harmonicPolyHomogeneousSubmodule, LinearMap.mem_ker] using hp.2
  simp [hpker]

theorem spherePrecomp_northRotation_mem_harmonicPolyHomogeneousImageSubmodule
    (t : ℝ) {n : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule n) :
    spherePrecomp (northRotation t) f ∈ harmonicPolyHomogeneousImageSubmodule n := by
  rcases hf with ⟨p, hp, rfl⟩
  refine ⟨northRotationPoly t p, northRotationPoly_mem_harmonicPolyHomogeneousSubmodule t hp, ?_⟩
  have h := congrArg sphereRestrictionLinear (ambientCoordMvEval_northRotationPoly t p)
  have h' :
      ((sphereCoordMvEval (northRotationPoly t p) : C(spherePoint3, ℝ)) : spherePoint3 → ℝ) =
        spherePrecompPi (northRotation t) (sphereCoordMvEval p : spherePoint3 → ℝ) := by
    simpa [sphereRestrictionLinear_ambientCoordMvEval, sphereRestrictionLinear_ambientPrecomp]
      using h
  ext x
  change sphereCoordMvEval (northRotationPoly t p) x =
    spherePrecomp (northRotation t) (sphereCoordMvEval p) x
  simpa [spherePrecomp_apply, spherePrecompPi] using congrFun h' x

theorem harmonicPolyHomogeneousImageSubmodule_invariant_under_spherePrecomp_northRotation
    (t : ℝ) (n : ℕ) :
    harmonicPolyHomogeneousImageSubmodule n ≤
      (harmonicPolyHomogeneousImageSubmodule n).comap (spherePrecomp (northRotation t)) := by
  intro f hf
  exact spherePrecomp_northRotation_mem_harmonicPolyHomogeneousImageSubmodule t hf
