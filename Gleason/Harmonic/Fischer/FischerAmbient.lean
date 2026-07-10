import Gleason.Harmonic.Fischer.FischerDecomposition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section

open Complex InnerProductSpace
open scoped BigOperators

def ambientCoordFun : Fin 3 → WithLp 2 (ℂ × ℝ) → ℝ
  | 0 => fun p => (complexProjL p).re
  | 1 => fun p => (complexProjL p).im
  | 2 => fun p => realProjL p

def ambientCoordMvEval : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] (WithLp 2 (ℂ × ℝ) → ℝ) :=
  MvPolynomial.aeval ambientCoordFun

@[simp] lemma ambientCoordMvEval_X (i : Fin 3) :
    ambientCoordMvEval (MvPolynomial.X i) = ambientCoordFun i := by
  simp [ambientCoordMvEval]

@[simp] lemma ambientCoordFun_smul (i : Fin 3) (t : ℝ) (p : WithLp 2 (ℂ × ℝ)) :
    ambientCoordFun i (t • p) = t * ambientCoordFun i p := by
  fin_cases i <;>
    simp [ambientCoordFun, complexProjL, realProjL, map_smul]

theorem eval_smul_of_isHomogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous n) (t : ℝ) (r : Fin 3 → ℝ) :
    MvPolynomial.eval (fun i => t * r i) p = t ^ n * MvPolynomial.eval r p := by
  rw [← p.support_sum_monomial_coeff, map_sum, map_sum]
  trans ∑ d ∈ p.support, t ^ n * MvPolynomial.eval r ((MvPolynomial.monomial d) (MvPolynomial.coeff d p))
  · refine Finset.sum_congr rfl ?_
    intro d hd
    have hddeg : d.degree = n := by
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hd) (hp.coeff_eq_zero hne)
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    calc
      MvPolynomial.coeff d p * d.prod (fun n e => (t * r n) ^ e)
          = MvPolynomial.coeff d p *
              (d.prod (fun _ e => t ^ e) * d.prod (fun n e => r n ^ e)) := by
              simp_rw [mul_pow]
              rw [Finsupp.prod_mul]
      _ = t ^ n * (MvPolynomial.coeff d p * d.prod (fun n e => r n ^ e)) := by
            have hsum : ∑ i, d i = n := by
              simpa [Finsupp.degree_eq_sum] using hddeg
            rw [Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, hsum]
            ring
  · simpa using (Finset.mul_sum p.support
      (fun d => MvPolynomial.eval r ((MvPolynomial.monomial d) (MvPolynomial.coeff d p)))
      (t ^ n)).symm

@[simp] lemma ambientCoordMvEval_apply
    (p : MvPolynomial (Fin 3) ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    ambientCoordMvEval p x = MvPolynomial.eval (fun i => ambientCoordFun i x) p := by
  refine (MvPolynomial.induction_on
    (motive := fun p => ∀ x, ambientCoordMvEval p x = MvPolynomial.eval (fun i => ambientCoordFun i x) p)
    p ?_ ?_ ?_) x
  · intro r x
    simp [ambientCoordMvEval]
  · intro p q hp hq x
    rw [map_add, MvPolynomial.eval_add]
    simpa [Pi.add_apply] using congrArg₂ HAdd.hAdd (hp x) (hq x)
  · intro p i hp x
    rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    have hXi : ambientCoordMvEval (MvPolynomial.X i) x = ambientCoordFun i x := by
      simp [ambientCoordMvEval_X]
    simpa [Pi.mul_apply] using congrArg₂ HMul.hMul (hp x) hXi

@[simp] lemma sphereCoordMvEval_apply
    (p : MvPolynomial (Fin 3) ℝ) (x : spherePoint3) :
    sphereCoordMvEval p x = MvPolynomial.eval (fun i => sphereCoordVec i x) p := by
  refine (MvPolynomial.induction_on
    (motive := fun p => ∀ x, sphereCoordMvEval p x = MvPolynomial.eval (fun i => sphereCoordVec i x) p)
    p ?_ ?_ ?_) x
  · intro r x
    simp [sphereCoordMvEval]
  · intro p q hp hq x
    rw [map_add, MvPolynomial.eval_add]
    simpa [Pi.add_apply] using congrArg₂ HAdd.hAdd (hp x) (hq x)
  · intro p i hp x
    rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    have hXi : sphereCoordMvEval (MvPolynomial.X i) x = sphereCoordVec i x := by
      simp [sphereCoordMvEval]
    simpa [Pi.mul_apply] using congrArg₂ HMul.hMul (hp x) hXi

theorem ambientCoordMvEval_smul_of_homogeneous
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (t : ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    ambientCoordMvEval p (t • x) = t ^ n * ambientCoordMvEval p x := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp
  rw [ambientCoordMvEval_apply, ambientCoordMvEval_apply]
  simpa [ambientCoordFun_smul] using
    eval_smul_of_isHomogeneous hp t (fun i => ambientCoordFun i x)

@[simp] lemma sphereRestrictionLinear_ambientCoordFun (i : Fin 3) :
    sphereRestrictionLinear (ambientCoordFun i) = sphereCoordVec i := by
  funext x
  fin_cases i <;> rfl

theorem sphereRestrictionLinear_ambientCoordMvEval
    (p : MvPolynomial (Fin 3) ℝ) :
    sphereRestrictionLinear (ambientCoordMvEval p) = sphereCoordMvEval p := by
  ext x
  simp [sphereRestrictionLinear, ambientCoordMvEval_apply, sphereCoordMvEval_apply]
  have hcoords : (fun i => ambientCoordFun i x.1) = fun i => sphereCoordVec i x := by
    funext i
    fin_cases i <;> rfl
  rw [hcoords]
