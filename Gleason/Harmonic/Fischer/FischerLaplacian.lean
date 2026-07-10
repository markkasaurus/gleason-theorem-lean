import Gleason.Harmonic.Fischer.FischerBasic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

noncomputable section

open Complex InnerProductSpace

@[simp] theorem pderiv_natCast
    (i : Fin 3) (n : ℕ) :
    MvPolynomial.pderiv i (n : MvPolynomial (Fin 3) ℝ) = 0 := by
  simp

theorem polyLaplacian_mem_homogeneousSubmodule
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    polyLaplacian p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2) := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
  have h0 :
      (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p)).IsHomogeneous (n - 2) := by
    simpa [Nat.sub_eq] using (hp.pderiv (i := 0)).pderiv (i := 0)
  have h1 :
      (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p)).IsHomogeneous (n - 2) := by
    simpa [Nat.sub_eq] using (hp.pderiv (i := 1)).pderiv (i := 1)
  have h2 :
      (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p)).IsHomogeneous (n - 2) := by
    simpa [Nat.sub_eq] using (hp.pderiv (i := 2)).pderiv (i := 2)
  simpa [polyLaplacian, add_assoc, add_left_comm, add_comm] using h0.add (h1.add h2)

theorem pderiv_rhoPoly_mul_zero
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 0 (rhoPoly * p) =
      2 * MvPolynomial.X 0 * p + rhoPoly * MvPolynomial.pderiv 0 p := by
  simp [MvPolynomial.pderiv_mul, mul_assoc]
  ring_nf

theorem pderiv_rhoPoly_mul_one
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 1 (rhoPoly * p) =
      2 * MvPolynomial.X 1 * p + rhoPoly * MvPolynomial.pderiv 1 p := by
  simp [MvPolynomial.pderiv_mul, mul_assoc]
  ring_nf

theorem pderiv_rhoPoly_mul_two
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 2 (rhoPoly * p) =
      2 * MvPolynomial.X 2 * p + rhoPoly * MvPolynomial.pderiv 2 p := by
  simp [MvPolynomial.pderiv_mul, mul_assoc]
  ring_nf

theorem pderiv_two_mul_X_mul_zero
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 0 (2 * MvPolynomial.X 0 * p) =
      2 * p + 2 * MvPolynomial.X 0 * MvPolynomial.pderiv 0 p := by
  have hconst : (MvPolynomial.pderiv 0) (2 : MvPolynomial (Fin 3) ℝ) = 0 := by
    simpa using (MvPolynomial.pderiv 0).map_natCast 2
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, hconst]
  simp [mul_assoc, left_distrib, right_distrib]

theorem pderiv_two_mul_X_mul_one
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 1 (2 * MvPolynomial.X 1 * p) =
      2 * p + 2 * MvPolynomial.X 1 * MvPolynomial.pderiv 1 p := by
  have hconst : (MvPolynomial.pderiv 1) (2 : MvPolynomial (Fin 3) ℝ) = 0 := by
    simpa using (MvPolynomial.pderiv 1).map_natCast 2
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, hconst]
  simp [mul_assoc, left_distrib, right_distrib]

theorem pderiv_two_mul_X_mul_two
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 2 (2 * MvPolynomial.X 2 * p) =
      2 * p + 2 * MvPolynomial.X 2 * MvPolynomial.pderiv 2 p := by
  have hconst : (MvPolynomial.pderiv 2) (2 : MvPolynomial (Fin 3) ℝ) = 0 := by
    simpa using (MvPolynomial.pderiv 2).map_natCast 2
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, hconst]
  simp [mul_assoc, left_distrib, right_distrib]

theorem pderiv_rhoPoly_mul_pderiv_zero
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 0 (rhoPoly * MvPolynomial.pderiv 0 p) =
      2 * MvPolynomial.X 0 * MvPolynomial.pderiv 0 p +
        rhoPoly * MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) := by
  simp [MvPolynomial.pderiv_mul, mul_assoc]
  ring_nf

theorem pderiv_rhoPoly_mul_pderiv_one
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 1 (rhoPoly * MvPolynomial.pderiv 1 p) =
      2 * MvPolynomial.X 1 * MvPolynomial.pderiv 1 p +
        rhoPoly * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) := by
  simp [MvPolynomial.pderiv_mul, mul_assoc]
  ring_nf

theorem pderiv_rhoPoly_mul_pderiv_two
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 2 (rhoPoly * MvPolynomial.pderiv 2 p) =
      2 * MvPolynomial.X 2 * MvPolynomial.pderiv 2 p +
        rhoPoly * MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p) := by
  simp [MvPolynomial.pderiv_mul, mul_assoc]
  ring_nf

theorem pderiv_pderiv_rhoPoly_mul_zero
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (rhoPoly * p)) =
      2 * p + 4 * MvPolynomial.X 0 * MvPolynomial.pderiv 0 p +
        rhoPoly * MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) := by
  rw [pderiv_rhoPoly_mul_zero]
  rw [(MvPolynomial.pderiv 0).map_add]
  rw [pderiv_two_mul_X_mul_zero, pderiv_rhoPoly_mul_pderiv_zero]
  ring_nf

theorem pderiv_pderiv_rhoPoly_mul_one
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (rhoPoly * p)) =
      2 * p + 4 * MvPolynomial.X 1 * MvPolynomial.pderiv 1 p +
        rhoPoly * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) := by
  rw [pderiv_rhoPoly_mul_one]
  rw [(MvPolynomial.pderiv 1).map_add]
  rw [pderiv_two_mul_X_mul_one, pderiv_rhoPoly_mul_pderiv_one]
  ring_nf

theorem pderiv_pderiv_rhoPoly_mul_two
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (rhoPoly * p)) =
      2 * p + 4 * MvPolynomial.X 2 * MvPolynomial.pderiv 2 p +
        rhoPoly * MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p) := by
  rw [pderiv_rhoPoly_mul_two]
  rw [(MvPolynomial.pderiv 2).map_add]
  rw [pderiv_two_mul_X_mul_two, pderiv_rhoPoly_mul_pderiv_two]
  ring_nf

theorem polyLaplacian_rhoPoly_mul
    (p : MvPolynomial (Fin 3) ℝ) :
    polyLaplacian (rhoPoly * p) =
      6 * p + 4 * (∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i p) +
        rhoPoly * polyLaplacian p := by
  rw [polyLaplacian, LinearMap.add_apply, LinearMap.add_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [Fin.sum_univ_three]
  change
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (rhoPoly * p)) +
        MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (rhoPoly * p)) +
      MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (rhoPoly * p)) =
    6 * p + 4 * (MvPolynomial.X 0 * MvPolynomial.pderiv 0 p +
        MvPolynomial.X 1 * MvPolynomial.pderiv 1 p +
        MvPolynomial.X 2 * MvPolynomial.pderiv 2 p) +
      rhoPoly * polyLaplacian p
  rw [pderiv_pderiv_rhoPoly_mul_zero, pderiv_pderiv_rhoPoly_mul_one, pderiv_pderiv_rhoPoly_mul_two]
  rw [polyLaplacian, LinearMap.add_apply, LinearMap.add_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  ring_nf
  simpa

theorem polyLaplacian_mul_rhoPoly
    (p : MvPolynomial (Fin 3) ℝ) :
    polyLaplacian (p * rhoPoly) =
      6 * p + 4 * (∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i p) +
        rhoPoly * polyLaplacian p := by
  simpa [mul_comm] using polyLaplacian_rhoPoly_mul p

theorem polyLaplacian_rhoPoly_mul_of_homogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    polyLaplacian (rhoPoly * p) =
      ((4 * n + 6 : ℕ) • p) + rhoPoly * polyLaplacian p := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp
  rw [polyLaplacian_rhoPoly_mul, hp.sum_X_mul_pderiv]
  rw [nsmul_eq_mul]
  ring_nf

theorem polyLaplacian_mul_rhoPoly_of_homogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    polyLaplacian (p * rhoPoly) =
      ((4 * n + 6 : ℕ) • p) + rhoPoly * polyLaplacian p := by
  simpa [mul_comm] using polyLaplacian_rhoPoly_mul_of_homogeneous hp
