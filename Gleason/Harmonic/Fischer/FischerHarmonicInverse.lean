import Gleason.Harmonic.Fischer.FischerLaplacian

noncomputable section

open Complex InnerProductSpace

theorem pderiv_eq_zero_of_mem_homogeneousSubmodule_zero
    {i : Fin 3} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 0) :
    MvPolynomial.pderiv i p = 0 := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp
  rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp
  rw [hp, MvPolynomial.pderiv_C]

theorem polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_zero
    {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 0) :
    polyLaplacian p = 0 := by
  have h0 : MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) = 0 := by
    rw [pderiv_eq_zero_of_mem_homogeneousSubmodule_zero hp]
    simp
  have h1 : MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) = 0 := by
    rw [pderiv_eq_zero_of_mem_homogeneousSubmodule_zero hp]
    simp
  have h2 : MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p) = 0 := by
    rw [pderiv_eq_zero_of_mem_homogeneousSubmodule_zero hp]
    simp
  simp [polyLaplacian, h0, h1, h2]

theorem polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_one
    {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 1) :
    polyLaplacian p = 0 := by
  have hp0 : MvPolynomial.pderiv 0 p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 0 := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    simpa using hp.pderiv (i := 0)
  have hp1 : MvPolynomial.pderiv 1 p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 0 := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    simpa using hp.pderiv (i := 1)
  have hp2 : MvPolynomial.pderiv 2 p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 0 := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    simpa using hp.pderiv (i := 2)
  have h0 : MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p) = 0 :=
    pderiv_eq_zero_of_mem_homogeneousSubmodule_zero hp0
  have h1 : MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p) = 0 :=
    pderiv_eq_zero_of_mem_homogeneousSubmodule_zero hp1
  have h2 : MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p) = 0 :=
    pderiv_eq_zero_of_mem_homogeneousSubmodule_zero hp2
  simp [polyLaplacian, h0, h1, h2]

theorem polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_mod_two_lt_two
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hn : n < 2) :
    polyLaplacian p = 0 := by
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · exact polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_zero hp
  · exact polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_one hp

theorem smul_rhoPoly_mem_homogeneousSubmodule_succ_two
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) (c : ℝ) :
    c • (rhoPoly * p) ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2) := by
  have hmul : rhoPoly * p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2) := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    have hrho : rhoPoly.IsHomogeneous 2 := by
      simpa [rhoPoly, add_assoc, add_left_comm, add_comm] using
        (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 0 2).add
          ((MvPolynomial.isHomogeneous_X_pow (R := ℝ) 1 2).add
            (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 2 2))
    simpa [add_assoc, add_left_comm, add_comm] using hrho.mul hp
  exact (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2)).smul_mem c hmul

theorem polyLaplacian_smul_rhoPoly_of_harmonic_homogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hΔ : polyLaplacian p = 0) :
    polyLaplacian ((((4 * n + 6 : ℕ) : ℝ)⁻¹) • (rhoPoly * p)) = p := by
  rw [LinearMap.map_smul, polyLaplacian_rhoPoly_mul_of_homogeneous hp, hΔ]
  simp
  have hnz : (((4 * n + 6 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hmul : (((4 * n + 6 : ℕ) : ℝ)⁻¹) • ((((4 * n + 6 : ℕ) : ℝ)) • p) = p := by
    rw [smul_smul]
    field_simp [hnz]
    simp
  simpa [Algebra.smul_def] using hmul

theorem exists_preimage_polyLaplacian_of_harmonic_homogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hΔ : polyLaplacian p = 0) :
    ∃ q ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2), polyLaplacian q = p := by
  refine ⟨((((4 * n + 6 : ℕ) : ℝ)⁻¹) • (rhoPoly * p)), ?_, ?_⟩
  · exact smul_rhoPoly_mem_homogeneousSubmodule_succ_two hp _
  · exact polyLaplacian_smul_rhoPoly_of_harmonic_homogeneous hp hΔ
