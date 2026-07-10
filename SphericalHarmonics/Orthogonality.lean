import SphericalHarmonics.Fischer
import SphericalHarmonics.LowDegree
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

open scoped BigOperators

namespace SphericalHarmonics

theorem pderiv_comm (i j : Fin 3) (p : Poly3) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  fin_cases i <;> fin_cases j
  all_goals
    ext d
    simp [coeff_pderiv, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]

/-- The Euler operator `∑ xᵢ ∂ᵢ` on ambient polynomials. -/
noncomputable def eulerOperator : Poly3 →ₗ[ℝ] Poly3 where
  toFun p := ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i p
  map_add' p q := by
    ext d
    simp [Fin.sum_univ_three, left_distrib]
    ring
  map_smul' a p := by
    ext d
    simp [Fin.sum_univ_three]

/-- The infinitesimal rotation in the `i,j`-plane, realized algebraically on polynomials. -/
noncomputable def angularDeriv (i j : Fin 3) : Poly3 →ₗ[ℝ] Poly3 where
  toFun p := MvPolynomial.X i * MvPolynomial.pderiv j p - MvPolynomial.X j * MvPolynomial.pderiv i p
  map_add' p q := by
    ext d
    simp [left_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' a p := by
    ext d
    simp [sub_eq_add_neg]

theorem eulerOperator_apply_eq_smul_of_isHomogeneous {n : ℕ} {p : Poly3}
    (hp : p.IsHomogeneous n) :
    eulerOperator p = n • p := by
  simpa [eulerOperator] using hp.sum_X_mul_pderiv

theorem angularDeriv_isHomogeneous {n : ℕ} {i j : Fin 3} {p : Poly3}
    (hp : p.IsHomogeneous n) :
    (angularDeriv i j p).IsHomogeneous n := by
  unfold angularDeriv
  cases n with
  | zero =>
      have hmem : p ∈ homogeneousSubmodule 0 := by
        exact (MvPolynomial.mem_homogeneousSubmodule 0 p).2 hp
      rcases mem_harmonicHomogeneousSubmodule_zero_of_mem_homogeneousSubmodule hmem with ⟨-, hhp⟩
      change laplacian p = 0 at hhp
      have hp0 : ∀ k : Fin 3, MvPolynomial.pderiv k p = 0 := by
        intro k
        have hconst : ∃ c : ℝ, p = MvPolynomial.C c := by
          have hzero : homogeneousSubmodule 0 = (1 : Submodule ℝ Poly3) := by
            simpa using (MvPolynomial.homogeneousSubmodule_zero (σ := Fin 3) (R := ℝ))
          rw [hzero] at hmem
          rcases (show ∃ y, MvPolynomial.C y = p by simpa [Submodule.mem_one] using hmem) with
            ⟨c, hc⟩
          exact ⟨c, hc.symm⟩
        rcases hconst with ⟨c, rfl⟩
        simp
      simpa [hp0] using (MvPolynomial.isHomogeneous_zero (σ := Fin 3) (R := ℝ) 0)
  | succ n =>
      have hi : (MvPolynomial.X i * MvPolynomial.pderiv j p).IsHomogeneous (n + 1) := by
        simpa [Nat.add_comm] using
          (MvPolynomial.isHomogeneous_X (R := ℝ) i).mul (hp.pderiv (i := j))
      have hj : (MvPolynomial.X j * MvPolynomial.pderiv i p).IsHomogeneous (n + 1) := by
        simpa [Nat.add_comm] using
          (MvPolynomial.isHomogeneous_X (R := ℝ) j).mul (hp.pderiv (i := i))
      exact hi.sub hj

theorem angularDeriv_mem_homogeneousSubmodule {n : ℕ} {i j : Fin 3} {p : Poly3}
    (hp : p ∈ homogeneousSubmodule n) :
    angularDeriv i j p ∈ homogeneousSubmodule n := by
  exact (MvPolynomial.mem_homogeneousSubmodule n _).2 <|
    angularDeriv_isHomogeneous ((MvPolynomial.mem_homogeneousSubmodule n p).1 hp)

private theorem laplacian_X_mul (i : Fin 3) (p : Poly3) :
    laplacian (MvPolynomial.X i * p) =
      MvPolynomial.X i * laplacian p + 2 • MvPolynomial.pderiv i p := by
  fin_cases i
  · suffices h :
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.X 0 * p)) +
          MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.X 0 * p)) +
        MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.X 0 * p)) =
        MvPolynomial.X 0 *
            (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) +
                MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) +
              MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)) +
          2 • MvPolynomial.pderiv 0 p by
      simpa [laplacian, Fin.sum_univ_three] using h
    simp [MvPolynomial.pderiv_mul, two_nsmul]
    ring_nf
  · suffices h :
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.X 1 * p)) +
          MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.X 1 * p)) +
        MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.X 1 * p)) =
        MvPolynomial.X 1 *
            (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) +
                MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) +
              MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)) +
          2 • MvPolynomial.pderiv 1 p by
      simpa [laplacian, Fin.sum_univ_three] using h
    simp [MvPolynomial.pderiv_mul, two_nsmul]
    ring_nf
  · suffices h :
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.X 2 * p)) +
          MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.X 2 * p)) +
        MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.X 2 * p)) =
        MvPolynomial.X 2 *
            (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) +
                MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) +
              MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)) +
          2 • MvPolynomial.pderiv 2 p by
      simpa [laplacian, Fin.sum_univ_three] using h
    simp [MvPolynomial.pderiv_mul, two_nsmul]
    ring_nf

private theorem laplacian_pderiv (i : Fin 3) (p : Poly3) :
    laplacian (MvPolynomial.pderiv i p) = MvPolynomial.pderiv i (laplacian p) := by
  fin_cases i
  · suffices h :
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p)) +
          MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 p)) +
        MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 0 p)) =
        MvPolynomial.pderiv 0
          (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) +
            MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) +
            MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)) by
      simpa [laplacian, Fin.sum_univ_three] using h
    simp [pderiv_comm]
  · suffices h :
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p)) +
          MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p)) +
        MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 1 p)) =
        MvPolynomial.pderiv 1
          (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) +
            MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) +
            MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)) by
      simpa [laplacian, Fin.sum_univ_three] using h
    simp [pderiv_comm]
  · suffices h :
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p)) +
          MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)) +
        MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)) =
        MvPolynomial.pderiv 2
          (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) +
            MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) +
            MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)) by
      simpa [laplacian, Fin.sum_univ_three] using h
    simp [pderiv_comm]

theorem laplacian_angularDeriv (i j : Fin 3) (p : Poly3) :
    laplacian (angularDeriv i j p) = angularDeriv i j (laplacian p) := by
  simp [angularDeriv]
  rw [laplacian_X_mul, laplacian_X_mul, laplacian_pderiv, laplacian_pderiv]
  simp [pderiv_comm, sub_eq_add_neg, left_distrib]
  ring_nf

private theorem angularDeriv_sq_01 (p : Poly3) :
    angularDeriv 0 1 (angularDeriv 0 1 p) =
      MvPolynomial.X 0 ^ 2 * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) +
        MvPolynomial.X 1 ^ 2 * MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) -
        2 • (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p)) -
        MvPolynomial.X 0 * MvPolynomial.pderiv 0 p -
        MvPolynomial.X 1 * MvPolynomial.pderiv 1 p := by
  simp [angularDeriv, MvPolynomial.pderiv_mul, pderiv_comm, two_nsmul]
  ring_nf

private theorem angularDeriv_sq_12 (p : Poly3) :
    angularDeriv 1 2 (angularDeriv 1 2 p) =
      MvPolynomial.X 1 ^ 2 * MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p) +
        MvPolynomial.X 2 ^ 2 * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) -
        2 • (MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p)) -
        MvPolynomial.X 1 * MvPolynomial.pderiv 1 p -
        MvPolynomial.X 2 * MvPolynomial.pderiv 2 p := by
  simp [angularDeriv, MvPolynomial.pderiv_mul, pderiv_comm, two_nsmul]
  ring_nf

private theorem angularDeriv_sq_20 (p : Poly3) :
    angularDeriv 2 0 (angularDeriv 2 0 p) =
      MvPolynomial.X 2 ^ 2 * MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) +
        MvPolynomial.X 0 ^ 2 * MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p) -
        2 • (MvPolynomial.X 2 * MvPolynomial.X 0 * MvPolynomial.pderiv 2 (MvPolynomial.pderiv 0 p)) -
        MvPolynomial.X 2 * MvPolynomial.pderiv 2 p -
        MvPolynomial.X 0 * MvPolynomial.pderiv 0 p := by
  simp [angularDeriv, MvPolynomial.pderiv_mul, pderiv_comm, two_nsmul]
  ring_nf

theorem sum_angularDeriv_sq (p : Poly3) :
    angularDeriv 0 1 (angularDeriv 0 1 p) +
        angularDeriv 1 2 (angularDeriv 1 2 p) +
      angularDeriv 2 0 (angularDeriv 2 0 p) =
      radiusSq * laplacian p - eulerOperator (eulerOperator p) - eulerOperator p := by
  rw [angularDeriv_sq_01, angularDeriv_sq_12, angularDeriv_sq_20]
  simp [radiusSq, eulerOperator, laplacian, Fin.sum_univ_three, MvPolynomial.pderiv_mul,
    pderiv_comm, two_nsmul, sub_eq_add_neg]
  ring_nf

theorem angularDeriv_mem_harmonicSubmodule {i j : Fin 3} {p : Poly3}
    (hp : p ∈ harmonicSubmodule) :
    angularDeriv i j p ∈ harmonicSubmodule := by
  change laplacian (angularDeriv i j p) = 0
  rw [laplacian_angularDeriv, show laplacian p = 0 from hp]
  simp [angularDeriv]

theorem angularDeriv_mem_harmonicHomogeneousSubmodule (n : ℕ) {i j : Fin 3} {p : Poly3}
    (hp : p ∈ harmonicHomogeneousSubmodule n) :
    angularDeriv i j p ∈ harmonicHomogeneousSubmodule n := by
  rcases Submodule.mem_inf.1 hp with ⟨hpn, hph⟩
  exact Submodule.mem_inf.2
    ⟨angularDeriv_mem_homogeneousSubmodule hpn, angularDeriv_mem_harmonicSubmodule hph⟩

end SphericalHarmonics
