import Gleason.Harmonic.Fischer.FischerIterates
import Gleason.Harmonic.Auxiliary.CoordHomogeneousDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

open Complex InnerProductSpace

theorem rhoPolyLaplacianCoeff_pos {n k : ℕ} (hk : 2 * k ≤ n) :
    0 < rhoPolyLaplacianCoeff n k := by
  induction k with
  | zero =>
      simp [rhoPolyLaplacianCoeff_zero]
      positivity
  | succ k ih =>
      rw [rhoPolyLaplacianCoeff_succ]
      have hk' : 2 * k ≤ n := by omega
      have hterm : 0 < (4 * ((n - 2 * (k + 1) : ℕ) : ℝ) + 6) := by
        positivity
      linarith [ih hk', hterm]

theorem eq_zero_of_polyLaplacian_rhoPoly_mul_eq_zero_of_homogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hT : polyLaplacian (rhoPoly * p) = 0) :
    p = 0 := by
  let m := n / 2
  have hmle : 2 * m ≤ n := by
    dsimp [m]
    omega
  have hmnext : n < 2 * (m + 1) := by
    dsimp [m]
    omega
  have hiterZero : ∀ k : ℕ, polyLaplacian^[k] (polyLaplacian (rhoPoly * p)) = 0 := by
    intro k
    simpa [hT] using
      (Function.iterate_fixed (f := polyLaplacian) (x := (0 : MvPolynomial (Fin 3) ℝ))
        polyLaplacian.map_zero k)
  have htopNext : polyLaplacian^[m + 1] p = 0 :=
    iter_polyLaplacian_eq_zero_of_homogeneous_lt hp hmnext
  have htopSmul :
      rhoPolyLaplacianCoeff n m • polyLaplacian^[m] p = 0 := by
    have hformula := iter_polyLaplacian_rhoPoly_mul_formula hp hmle
    simpa [hiterZero m, htopNext] using hformula.symm
  have htop : polyLaplacian^[m] p = 0 := by
    rcases smul_eq_zero.mp htopSmul with hcoeff | hzero
    · exact (False.elim ((ne_of_gt (rhoPolyLaplacianCoeff_pos hmle)) hcoeff))
    · exact hzero
  have hdesc : ∀ j : ℕ, j ≤ m → polyLaplacian^[m - j] p = 0 := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa using htop
    | succ j ih =>
        intro hj
        have hj' : j ≤ m := Nat.le_of_succ_le hj
        have hnext : polyLaplacian^[m - j] p = 0 := ih hj'
        let k0 := m - (j + 1)
        have hk0 : 2 * k0 ≤ n := by
          dsimp [k0, m]
          omega
        have hsmul :
            rhoPolyLaplacianCoeff n k0 • polyLaplacian^[k0] p = 0 := by
          have hformula := iter_polyLaplacian_rhoPoly_mul_formula hp hk0
          have hk1 : k0 + 1 = m - j := by
            dsimp [k0, m]
            omega
          simpa [hiterZero k0, hk1, hnext] using hformula.symm
        rcases smul_eq_zero.mp hsmul with hcoeff | hzero
        · exact (False.elim ((ne_of_gt (rhoPolyLaplacianCoeff_pos hk0)) hcoeff))
        · simpa [k0] using hzero
  simpa [m] using hdesc m le_rfl

def rhoPolyLaplacianHomogeneousLinear (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  polyLaplacian.comp
    ((LinearMap.mulLeft ℝ rhoPoly).comp
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).subtype)

def rhoPolyLaplacianHomogeneousEnd (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n →ₗ[ℝ]
      MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n :=
  LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (rhoPolyLaplacianHomogeneousLinear n) fun q => by
      have hmul :
          (1 : ℝ) • (rhoPoly * q.1) ∈
            MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2) :=
        smul_rhoPoly_mem_homogeneousSubmodule_succ_two q.2 1
      simpa [rhoPolyLaplacianHomogeneousLinear] using polyLaplacian_mem_homogeneousSubmodule hmul

theorem rhoPolyLaplacianHomogeneousEnd_injective (n : ℕ) :
    Function.Injective (rhoPolyLaplacianHomogeneousEnd n) := by
  intro q r hqr
  apply Subtype.ext
  change (q : MvPolynomial (Fin 3) ℝ) = (r : MvPolynomial (Fin 3) ℝ)
  let s : MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n := q - r
  have hzero :
      polyLaplacian (rhoPoly * (s : MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)) = 0 := by
    have hsub : rhoPolyLaplacianHomogeneousEnd n s = 0 := by
      change rhoPolyLaplacianHomogeneousEnd n (q - r) = 0
      rw [LinearMap.map_sub, hqr, sub_self]
    simpa [rhoPolyLaplacianHomogeneousEnd] using congrArg Subtype.val hsub
  have hqr0 :
      s = 0 := by
    apply Subtype.ext
    exact eq_zero_of_polyLaplacian_rhoPoly_mul_eq_zero_of_homogeneous s.2 hzero
  have hs : q - r = 0 := by simpa [s] using hqr0
  have hs' : ((q : MvPolynomial (Fin 3) ℝ) - r : MvPolynomial (Fin 3) ℝ) = 0 := by
    simpa using congrArg Subtype.val hs
  exact sub_eq_zero.mp hs'

theorem rhoPolyLaplacianHomogeneousEnd_surjective (n : ℕ) :
    Function.Surjective (rhoPolyLaplacianHomogeneousEnd n) :=
  LinearMap.surjective_of_injective (f := rhoPolyLaplacianHomogeneousEnd n)
    (rhoPolyLaplacianHomogeneousEnd_injective n)
