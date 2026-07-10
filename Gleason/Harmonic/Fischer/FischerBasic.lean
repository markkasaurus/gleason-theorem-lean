import Gleason.Harmonic.Auxiliary.CoordHomogeneousDegree
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section

open Complex InnerProductSpace

def rhoPoly : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2

def polyLaplacian : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  ((MvPolynomial.pderiv 0).toLinearMap.comp (MvPolynomial.pderiv 0).toLinearMap) +
    ((MvPolynomial.pderiv 1).toLinearMap.comp (MvPolynomial.pderiv 1).toLinearMap) +
    ((MvPolynomial.pderiv 2).toLinearMap.comp (MvPolynomial.pderiv 2).toLinearMap)

theorem rhoPoly_mem_homogeneousSubmodule_two :
    rhoPoly ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 2 := by
  simpa [rhoPoly, add_assoc, add_left_comm, add_comm] using
    (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 0 2).add
      ((MvPolynomial.isHomogeneous_X_pow (R := ℝ) 1 2).add
        (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 2 2))

@[simp] theorem pderiv_rhoPoly_zero :
    MvPolynomial.pderiv 0 rhoPoly = 2 * MvPolynomial.X 0 := by
  simp [rhoPoly, pow_two, add_comm, add_left_comm, add_assoc]
  ring

@[simp] theorem pderiv_rhoPoly_one :
    MvPolynomial.pderiv 1 rhoPoly = 2 * MvPolynomial.X 1 := by
  simp [rhoPoly, pow_two, add_comm, add_left_comm, add_assoc]
  ring

@[simp] theorem pderiv_rhoPoly_two :
    MvPolynomial.pderiv 2 rhoPoly = 2 * MvPolynomial.X 2 := by
  simp [rhoPoly, pow_two, add_comm, add_left_comm, add_assoc]
  ring

@[simp] theorem polyLaplacian_rhoPoly :
    polyLaplacian rhoPoly = 6 := by
  simp [polyLaplacian, rhoPoly, pow_two, add_assoc, add_left_comm, add_comm]
  ring

theorem sphereCoordMvEval_rhoPoly :
    sphereCoordMvEval rhoPoly = 1 := by
  ext x
  have hnorm :
      ‖x.1‖ ^ 2 = ‖x.1.fst‖ ^ 2 + ‖x.1.snd‖ ^ 2 := by
    simpa using (WithLp.prod_norm_sq_eq_of_L2 (x := x.1))
  have hx : ‖x.1‖ = 1 := x.2
  have hnorm' : 1 = Complex.normSq x.1.fst + x.1.snd ^ 2 := by
    calc
      1 = ‖x.1‖ ^ 2 := by simpa [hx]
      _ = ‖x.1.fst‖ ^ 2 + ‖x.1.snd‖ ^ 2 := hnorm
      _ = Complex.normSq x.1.fst + x.1.snd ^ 2 := by
            simp [Complex.normSq_eq_norm_sq]
  have hsum :
      x.1.fst.re ^ 2 + x.1.fst.im ^ 2 + x.1.snd ^ 2 = 1 := by
    rw [Complex.normSq_apply] at hnorm'
    nlinarith [hnorm']
  calc
    (sphereCoordMvEval rhoPoly) x
        = x.1.fst.re ^ 2 + x.1.fst.im ^ 2 + x.1.snd ^ 2 := by
            simp [rhoPoly, sphereCoordMvEval, sphereCoordVec, sphereCoordRe, sphereCoordIm,
              sphereCoordZ, pow_two, add_assoc, add_left_comm, add_comm]
    _ = 1 := hsum

@[simp] theorem sphereCoordMvEval_rhoPoly_mul (p : MvPolynomial (Fin 3) ℝ) :
    sphereCoordMvEval (rhoPoly * p) = sphereCoordMvEval p := by
  rw [map_mul, sphereCoordMvEval_rhoPoly, one_mul]

@[simp] theorem sphereCoordMvEval_mul_rhoPoly (p : MvPolynomial (Fin 3) ℝ) :
    sphereCoordMvEval (p * rhoPoly) = sphereCoordMvEval p := by
  rw [map_mul, sphereCoordMvEval_rhoPoly, mul_one]

@[simp] theorem sphereCoordMvEval_rhoPoly_pow (n : ℕ) :
    sphereCoordMvEval (rhoPoly ^ n) = 1 := by
  rw [map_pow, sphereCoordMvEval_rhoPoly, one_pow]

@[simp] theorem sphereCoordMvEval_rhoPoly_pow_mul (n : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) :
    sphereCoordMvEval (rhoPoly ^ n * p) = sphereCoordMvEval p := by
  rw [map_mul, sphereCoordMvEval_rhoPoly_pow, one_mul]

theorem homogeneousImage_two_step_mono (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap ≤
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2)).map sphereCoordMvEval.toLinearMap := by
  rintro f ⟨p, hp, rfl⟩
  refine ⟨rhoPoly * p, ?_, ?_⟩
  · simpa [add_assoc, add_left_comm, add_comm] using rhoPoly_mem_homogeneousSubmodule_two.mul hp
  · simpa [sphereCoordMvEval_rhoPoly_mul]
