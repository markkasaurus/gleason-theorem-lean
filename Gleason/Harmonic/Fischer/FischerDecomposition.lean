import Gleason.Harmonic.Fischer.FischerEndomorphism

noncomputable section

open Complex InnerProductSpace

def harmonicPolyHomogeneousSubmodule (n : ℕ) : Submodule ℝ (MvPolynomial (Fin 3) ℝ) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n ⊓ LinearMap.ker polyLaplacian

theorem exists_harmonic_rho_decomposition_of_homogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    ∃ h q,
      h ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n ∧
      polyLaplacian h = 0 ∧
      q ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2) ∧
      p = h + rhoPoly * q := by
  by_cases hn : n < 2
  · refine ⟨p, 0, hp, ?_, by simp, ?_⟩
    · exact polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_mod_two_lt_two hp hn
    · simp
  · have h2 : 2 ≤ n := by omega
    let r : MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2) :=
      ⟨polyLaplacian p, polyLaplacian_mem_homogeneousSubmodule hp⟩
    rcases rhoPolyLaplacianHomogeneousEnd_surjective (n - 2) r with ⟨qSub, hqSub⟩
    refine ⟨p - rhoPoly * qSub.1, qSub.1, ?_, ?_, qSub.2, ?_⟩
    · have hρq :
          rhoPoly * qSub.1 ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n := by
        simpa [Nat.sub_add_cancel h2] using
          smul_rhoPoly_mem_homogeneousSubmodule_succ_two qSub.2 (1 : ℝ)
      exact (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).sub_mem hp hρq
    · have hq :
          polyLaplacian (rhoPoly * qSub.1) = polyLaplacian p := by
        simpa [r, rhoPolyLaplacianHomogeneousEnd, rhoPolyLaplacianHomogeneousLinear] using
          congrArg Subtype.val hqSub
      simp [hq, map_sub]
    · ring

theorem homogeneousImage_le_harmonicPolyImage_sup_prev (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap ≤
      (harmonicPolyHomogeneousSubmodule n).map sphereCoordMvEval.toLinearMap ⊔
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap := by
  intro f hf
  rcases hf with ⟨p, hp, rfl⟩
  rcases exists_harmonic_rho_decomposition_of_homogeneous hp with
    ⟨h, q, hh, hΔh, hq, hpq⟩
  have hhmem :
      sphereCoordMvEval h ∈
        (harmonicPolyHomogeneousSubmodule n).map sphereCoordMvEval.toLinearMap := by
    refine ⟨h, ⟨hh, ?_⟩, rfl⟩
    simpa [LinearMap.mem_ker] using hΔh
  have hqmem :
      sphereCoordMvEval q ∈
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap := by
    exact ⟨q, hq, rfl⟩
  refine Submodule.mem_sup.2 ⟨sphereCoordMvEval h, hhmem, sphereCoordMvEval q, hqmem, ?_⟩
  rw [← sphereCoordMvEval_rhoPoly_mul, hpq]
  simp [map_add]
