import Gleason.Harmonic.Fischer.FischerHarmonicInverse

noncomputable section

open Complex InnerProductSpace

def rhoPolyLaplacianCoeff (n k : ℕ) : ℝ :=
  Nat.rec (4 * (n : ℝ) + 6)
    (fun j a => a + (4 * ((n - 2 * (j + 1) : ℕ) : ℝ) + 6)) k

@[simp] theorem rhoPolyLaplacianCoeff_zero (n : ℕ) :
    rhoPolyLaplacianCoeff n 0 = 4 * (n : ℝ) + 6 := by
  rfl

@[simp] theorem rhoPolyLaplacianCoeff_succ (n k : ℕ) :
    rhoPolyLaplacianCoeff n (k + 1) =
      rhoPolyLaplacianCoeff n k + (4 * ((n - 2 * (k + 1) : ℕ) : ℝ) + 6) := by
  rfl

theorem iter_polyLaplacian_mem_homogeneousSubmodule
    {n k : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hk : 2 * k ≤ n) :
    polyLaplacian^[k] p ∈
      MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2 * k) := by
  induction k generalizing n p with
  | zero =>
      simpa using hp
  | succ k ih =>
      have hk' : 2 * k ≤ n := by omega
      have hmem :
          polyLaplacian ((⇑polyLaplacian)^[k] p) ∈
            MvPolynomial.homogeneousSubmodule (Fin 3) ℝ ((n - 2 * k) - 2) :=
        polyLaplacian_mem_homogeneousSubmodule (ih hp hk')
      have hdeg : (n - 2 * k) - 2 = n - 2 * (k + 1) := by omega
      simpa [Function.iterate_succ_apply', hdeg] using hmem

theorem iter_polyLaplacian_eq_zero_of_homogeneous_lt
    {n k : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hk : n < 2 * k) :
    polyLaplacian^[k] p = 0 := by
  by_cases hkm1 : 2 * (k - 1) ≤ n
  · have hmem :
        polyLaplacian^[k - 1] p ∈
          MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2 * (k - 1)) :=
      iter_polyLaplacian_mem_homogeneousSubmodule hp hkm1
    have hlt : n - 2 * (k - 1) < 2 := by omega
    cases k with
    | zero => omega
    | succ k =>
        simpa [Function.iterate_succ_apply'] using
          polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_mod_two_lt_two hmem hlt
  · have hkpos : 0 < k := by omega
    cases k with
    | zero => omega
    | succ k =>
        have hk' : n < 2 * k := by omega
        simpa [Function.iterate_succ_apply'] using
          congrArg polyLaplacian
            (iter_polyLaplacian_eq_zero_of_homogeneous_lt hp hk')

theorem iter_polyLaplacian_rhoPoly_mul_formula
    {n k : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hk : 2 * k ≤ n) :
    polyLaplacian^[k] (polyLaplacian (rhoPoly * p)) =
      rhoPolyLaplacianCoeff n k • polyLaplacian^[k] p +
        rhoPoly * polyLaplacian^[k + 1] p := by
  induction k generalizing n p with
  | zero =>
      simpa [rhoPolyLaplacianCoeff_zero, Function.iterate_one, Algebra.smul_def] using
        polyLaplacian_rhoPoly_mul_of_homogeneous hp
  | succ k ih =>
      have hk' : 2 * k ≤ n := by omega
      have hdeg :
          polyLaplacian^[k + 1] p ∈
            MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2 * (k + 1)) := by
        exact iter_polyLaplacian_mem_homogeneousSubmodule hp (by omega)
      rw [Function.iterate_succ_apply', ih hp hk']
      rw [LinearMap.map_add, LinearMap.map_smul]
      rw [polyLaplacian_rhoPoly_mul_of_homogeneous hdeg]
      rw [Function.iterate_succ_apply']
      have hcoeffcast :
          (((4 * (n - 2 * (k + 1)) + 6 : ℕ) : ℝ)) =
            4 * ((n - 2 * (k + 1) : ℕ) : ℝ) + 6 := by
        norm_num
      have hsum :
          rhoPolyLaplacianCoeff n k • polyLaplacian ((⇑polyLaplacian)^[k] p) +
              (((4 * (n - 2 * (k + 1)) + 6 : ℕ) : ℝ)) •
                polyLaplacian ((⇑polyLaplacian)^[k] p) =
            rhoPolyLaplacianCoeff n (k + 1) • polyLaplacian ((⇑polyLaplacian)^[k] p) := by
        calc
          rhoPolyLaplacianCoeff n k • polyLaplacian ((⇑polyLaplacian)^[k] p) +
              (((4 * (n - 2 * (k + 1)) + 6 : ℕ) : ℝ)) •
                polyLaplacian ((⇑polyLaplacian)^[k] p) =
              (rhoPolyLaplacianCoeff n k +
                  (((4 * (n - 2 * (k + 1)) + 6 : ℕ) : ℝ))) •
                polyLaplacian ((⇑polyLaplacian)^[k] p) := by
                  exact
                    (add_smul (rhoPolyLaplacianCoeff n k)
                      (((4 * (n - 2 * (k + 1)) + 6 : ℕ) : ℝ))
                      (polyLaplacian ((⇑polyLaplacian)^[k] p))).symm
          _ = rhoPolyLaplacianCoeff n (k + 1) • polyLaplacian ((⇑polyLaplacian)^[k] p) := by
            congr 1
            rw [rhoPolyLaplacianCoeff_succ, hcoeffcast]
      have hsum' :
          rhoPolyLaplacianCoeff n k • polyLaplacian ((⇑polyLaplacian)^[k] p) +
              (4 * (n - 2 * (k + 1)) + 6) • polyLaplacian ((⇑polyLaplacian)^[k] p) =
            rhoPolyLaplacianCoeff n (k + 1) • polyLaplacian ((⇑polyLaplacian)^[k] p) := by
        simpa [Algebra.smul_def] using hsum
      rw [← add_assoc, hsum']
      simp [Function.iterate_succ_apply']
