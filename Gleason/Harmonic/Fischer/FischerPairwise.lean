import Gleason.Harmonic.Fischer.FischerBasic
import Gleason.Harmonic.Fischer.FischerDirect
import Gleason.Harmonic.Fischer.FischerBoundedClosure
import Gleason.Continuity.Auxiliary.FrameEven
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section

open Complex InnerProductSpace

private theorem sphereCoordMvEval_antipode_of_homogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (x : spherePoint3) :
    sphereCoordMvEval p (sphereAntipode x) = (-1 : ℝ) ^ n * sphereCoordMvEval p x := by
  calc
    sphereCoordMvEval p (sphereAntipode x)
        = MvPolynomial.eval (fun i => sphereCoordVec i (sphereAntipode x)) p := by
            rw [sphereCoordMvEval_apply]
    _ = MvPolynomial.eval (fun i => ambientCoordFun i (-x.1)) p := by
            congr
            funext i
            fin_cases i <;>
              simp [sphereAntipode_apply_val, sphereCoordVec, sphereCoordRe, sphereCoordIm,
                sphereCoordZ, ambientCoordFun, complexProjL, realProjL]
    _ = ambientCoordMvEval p ((-1 : ℝ) • x.1) := by
            rw [ambientCoordMvEval_apply]
            congr
            funext i
            simp [ambientCoordFun]
    _ = (-1 : ℝ) ^ n * ambientCoordMvEval p x.1 :=
          ambientCoordMvEval_smul_of_homogeneous hp (-1) x.1
    _ = (-1 : ℝ) ^ n * MvPolynomial.eval (fun i => sphereCoordVec i x) p := by
          rw [ambientCoordMvEval_apply]
          congr
          funext i
          fin_cases i <;>
            simp [sphereCoordVec, sphereCoordRe, sphereCoordIm, sphereCoordZ, ambientCoordFun,
              complexProjL, realProjL]
    _ = (-1 : ℝ) ^ n * sphereCoordMvEval p x := by rw [sphereCoordMvEval_apply]

private theorem rhoPoly_ne_zero : rhoPoly ≠ 0 := by
  intro h
  have hEval :=
    congrArg (fun f : C(spherePoint3, ℝ) => f sphereE1) (congrArg sphereCoordMvEval h)
  simpa [sphereCoordMvEval_rhoPoly] using hEval

private theorem rhoPoly_pow_ne_zero (k : ℕ) : rhoPoly ^ k ≠ 0 :=
  pow_ne_zero k rhoPoly_ne_zero

private theorem rhoPoly_pow_mem_homogeneousSubmodule (k : ℕ) :
    rhoPoly ^ k ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * k) := by
  induction k with
  | zero =>
      exact MvPolynomial.isHomogeneous_C (σ := Fin 3) (R := ℝ) (1 : ℝ)
  | succ k ih =>
      have hrho : rhoPoly ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 2 := by
        simpa [rhoPoly, add_assoc, add_left_comm, add_comm] using
          (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 0 2).add
            ((MvPolynomial.isHomogeneous_X_pow (R := ℝ) 1 2).add
              (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 2 2))
      simpa [pow_succ, two_mul, add_assoc, add_left_comm, add_comm] using
        ih.mul (show rhoPoly.IsHomogeneous 2 from hrho)

private theorem eq_zero_of_polyLaplacian_rhoPoly_pow_eq_zero_of_homogeneous
    {m k : ℕ} (hk : 1 ≤ k) {q : MvPolynomial (Fin 3) ℝ}
    (hq : q ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ m)
    (hΔ : polyLaplacian (rhoPoly ^ k * q) = 0) :
    q = 0 := by
  cases k with
  | zero =>
      cases hk
  | succ k =>
      have hzeroPow : rhoPoly ^ k * q = 0 := by
        refine eq_zero_of_polyLaplacian_rhoPoly_mul_eq_zero_of_homogeneous
          (n := m + 2 * k) ?_ ?_
        simpa [pow_succ, mul_assoc, two_mul, add_assoc, add_left_comm, add_comm] using
          (rhoPoly_pow_mem_homogeneousSubmodule k).mul hq
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hΔ
      exact (mul_eq_zero.mp hzeroPow).resolve_left (rhoPoly_pow_ne_zero k)

private theorem harmonicPolyHomogeneousImageSubmodule_disjoint_of_lt
    {m n : ℕ} (hmn : m < n) :
    Disjoint
      (harmonicPolyHomogeneousImageSubmodule n)
      (harmonicPolyHomogeneousImageSubmodule m) := by
  rw [Submodule.disjoint_def]
  intro f hfN hfM
  rcases hfN with ⟨p, hp, rfl⟩
  rcases hfM with ⟨q, hq, hres⟩
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · rcases Nat.even_or_odd m with hmEven | hmOdd
    · rcases hnEven with ⟨a, rfl⟩
      rcases hmEven with ⟨b, rfl⟩
      have hpHom : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * a) := by
        simpa [two_mul] using hp.1
      have hba : b < a := by omega
      let k : ℕ := a - b
      have hk : 1 ≤ k := by
        dsimp [k]
        omega
      have hnk : 2 * a = 2 * b + 2 * k := by
        dsimp [k]
        omega
      have hpq :
          sphereCoordMvEval p = sphereCoordMvEval (rhoPoly ^ k * q) := by
        rw [sphereCoordMvEval_rhoPoly_pow_mul]
        exact hres.symm
      have hdeg :
          rhoPoly ^ k * q ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * a) := by
        rw [hnk]
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using
          (rhoPoly_pow_mem_homogeneousSubmodule k).mul hq.1
      have hpeq : p = rhoPoly ^ k * q := by
        simpa [two_mul] using
          (eq_of_sphereCoordMvEval_eq_of_mem_homogeneousSubmodule
            (n := 2 * a) hpHom hdeg hpq)
      have hqzero : q = 0 := by
        refine eq_zero_of_polyLaplacian_rhoPoly_pow_eq_zero_of_homogeneous hk hq.1 ?_
        simpa [hpeq]
          using (show polyLaplacian p = 0 by
            simpa [harmonicPolyHomogeneousSubmodule, LinearMap.mem_ker] using hp.2)
      simpa [hqzero] using hres.symm
    · have hzero : sphereCoordMvEval p = 0 := by
        ext x
        have hpAnti := sphereCoordMvEval_antipode_of_homogeneous hp.1 x
        have hqAnti := sphereCoordMvEval_antipode_of_homogeneous hq.1 x
        rw [hnEven.neg_one_pow] at hpAnti
        rw [hmOdd.neg_one_pow] at hqAnti
        have hresAnti :
            sphereCoordMvEval q (sphereAntipode x) =
              sphereCoordMvEval p (sphereAntipode x) := by
          simpa using congrArg (fun g : C(spherePoint3, ℝ) => g (sphereAntipode x)) hres
        have hresX : sphereCoordMvEval q x = sphereCoordMvEval p x := by
          simpa using congrArg (fun g : C(spherePoint3, ℝ) => g x) hres
        have hEq : sphereCoordMvEval p x = -(sphereCoordMvEval p x) := by
          calc
            sphereCoordMvEval p x
                = sphereCoordMvEval p (sphereAntipode x) := by simpa [hpAnti]
            _ = sphereCoordMvEval q (sphereAntipode x) := by simpa using hresAnti.symm
            _ = -(sphereCoordMvEval q x) := by simpa using hqAnti
            _ = -(sphereCoordMvEval p x) := by rw [hresX]
        have hx0 : sphereCoordMvEval p x = 0 := by linarith
        simpa using hx0
      have hpzero : p = 0 :=
        eq_zero_of_sphereCoordMvEval_eq_zero_of_mem_homogeneousSubmodule hp.1 hzero
      simpa [hpzero]
  · rcases Nat.even_or_odd m with hmEven | hmOdd
    · have hzero : sphereCoordMvEval p = 0 := by
        ext x
        have hpAnti := sphereCoordMvEval_antipode_of_homogeneous hp.1 x
        have hqAnti := sphereCoordMvEval_antipode_of_homogeneous hq.1 x
        rw [hnOdd.neg_one_pow] at hpAnti
        rw [hmEven.neg_one_pow] at hqAnti
        have hresAnti :
            sphereCoordMvEval q (sphereAntipode x) =
              sphereCoordMvEval p (sphereAntipode x) := by
          simpa using congrArg (fun g : C(spherePoint3, ℝ) => g (sphereAntipode x)) hres
        have hresX : sphereCoordMvEval q x = sphereCoordMvEval p x := by
          simpa using congrArg (fun g : C(spherePoint3, ℝ) => g x) hres
        have hEq : sphereCoordMvEval p x = -(sphereCoordMvEval p x) := by
          calc
            sphereCoordMvEval p x
                = -sphereCoordMvEval p (sphereAntipode x) := by simpa [hpAnti]
            _ = -sphereCoordMvEval q (sphereAntipode x) := by rw [hresAnti.symm]
            _ = -(sphereCoordMvEval q x) := by simpa using congrArg Neg.neg hqAnti
            _ = -(sphereCoordMvEval p x) := by rw [hresX]
        have hx0 : sphereCoordMvEval p x = 0 := by linarith
        simpa using hx0
      have hpzero : p = 0 :=
        eq_zero_of_sphereCoordMvEval_eq_zero_of_mem_homogeneousSubmodule hp.1 hzero
      simpa [hpzero]
    · rcases hnOdd with ⟨a, rfl⟩
      rcases hmOdd with ⟨b, rfl⟩
      have hba : b < a := by omega
      let k : ℕ := a - b
      have hk : 1 ≤ k := by
        dsimp [k]
        omega
      have hnk : 2 * a + 1 = (2 * b + 1) + 2 * k := by
        dsimp [k]
        omega
      have hpq :
          sphereCoordMvEval p = sphereCoordMvEval (rhoPoly ^ k * q) := by
        rw [sphereCoordMvEval_rhoPoly_pow_mul]
        exact hres.symm
      have hdeg :
          rhoPoly ^ k * q ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * a + 1) := by
        rw [hnk]
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using
          (rhoPoly_pow_mem_homogeneousSubmodule k).mul hq.1
      have hpeq : p = rhoPoly ^ k * q :=
        eq_of_sphereCoordMvEval_eq_of_mem_homogeneousSubmodule
          (n := 2 * a + 1) hp.1 hdeg hpq
      have hqzero : q = 0 := by
        refine eq_zero_of_polyLaplacian_rhoPoly_pow_eq_zero_of_homogeneous hk hq.1 ?_
        simpa [hpeq]
          using (show polyLaplacian p = 0 by
            simpa [harmonicPolyHomogeneousSubmodule, LinearMap.mem_ker] using hp.2)
      simpa [hqzero] using hres.symm

theorem harmonicPolyHomogeneousImageSubmodule_disjoint_of_ne
    {n m : ℕ} (hnm : n ≠ m) :
    Disjoint
      (harmonicPolyHomogeneousImageSubmodule n)
      (harmonicPolyHomogeneousImageSubmodule m) := by
  rcases lt_or_gt_of_ne hnm with hnm' | hmn'
  · simpa [disjoint_comm] using
      (harmonicPolyHomogeneousImageSubmodule_disjoint_of_lt (m := n) (n := m) hnm')
  · exact harmonicPolyHomogeneousImageSubmodule_disjoint_of_lt hmn'

theorem boundedHarmonicPolyHomogeneousImageSubmodule_eq_finset_sup
    (N : ℕ) :
    boundedHarmonicPolyHomogeneousImageSubmodule N =
      (Finset.range (N + 1)).sup harmonicPolyHomogeneousImageSubmodule := by
  refine le_antisymm ?_ ?_
  · rw [boundedHarmonicPolyHomogeneousImageSubmodule]
    refine iSup_le ?_
    intro i
    exact Finset.le_sup (s := Finset.range (N + 1)) <| by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le i.2)
  · refine Finset.sup_le ?_
    intro i hi
    exact le_iSup (fun j : Set.Iic N => harmonicPolyHomogeneousImageSubmodule j.1)
      ⟨i, Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)⟩
