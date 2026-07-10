import Gleason.Harmonic.HighDegree.EvenBoundedWitness
import Gleason.Harmonic.Zonal.NorthZonalProfileQuadratic
import Gleason.Harmonic.Auxiliary.PointConstraintFrame
import Gleason.Harmonic.Fischer.FischerAmbient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

open Complex InnerProductSpace
open scoped BigOperators

def meridianPosCoord (z : ℝ) : Fin 3 → ℝ
  | 0 => Real.sqrt (1 - z ^ 2)
  | 1 => 0
  | 2 => z

def meridianNegCoord (z : ℝ) : Fin 3 → ℝ
  | 0 => -Real.sqrt (1 - z ^ 2)
  | 1 => 0
  | 2 => z

def northMeridianPolynomial (p : MvPolynomial (Fin 3) ℝ) : Polynomial ℝ :=
  Finset.sum p.support fun d =>
    if d 1 = 0 ∧ Even (d 0) then
      Polynomial.C (p.coeff d) *
        ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2) *
        Polynomial.X ^ (d 2)
    else 0

@[simp] lemma meridianPosCoord_zero (z : ℝ) :
    meridianPosCoord z 0 = Real.sqrt (1 - z ^ 2) := rfl

@[simp] lemma meridianPosCoord_one (z : ℝ) :
    meridianPosCoord z 1 = 0 := rfl

@[simp] lemma meridianPosCoord_two (z : ℝ) :
    meridianPosCoord z 2 = z := rfl

@[simp] lemma meridianNegCoord_zero (z : ℝ) :
    meridianNegCoord z 0 = -Real.sqrt (1 - z ^ 2) := rfl

@[simp] lemma meridianNegCoord_one (z : ℝ) :
    meridianNegCoord z 1 = 0 := rfl

@[simp] lemma meridianNegCoord_two (z : ℝ) :
    meridianNegCoord z 2 = z := rfl

lemma sphereCoordVec_northSection_eq_meridianPosCoord
    (z : Set.Icc (-1 : ℝ) 1) :
    (fun i => sphereCoordVec i (northSection z)) = meridianPosCoord z.1 := by
  funext i
  fin_cases i <;>
    simp [sphereCoordVec, sphereCoordRe, sphereCoordIm, sphereCoordZ, northSection, meridianPosCoord]

lemma sphereCoordVec_northRotation_pi_northSection_eq_meridianNegCoord
    (z : Set.Icc (-1 : ℝ) 1) :
    (fun i => sphereCoordVec i (sphereMap (northRotation Real.pi) (northSection z))) =
      meridianNegCoord z.1 := by
  funext i
  fin_cases i <;>
    simp [sphereCoordVec, sphereCoordRe, sphereCoordIm, sphereCoordZ, northSection,
      northRotation_apply, sphereMap, meridianNegCoord]

private lemma meridianPosCoord_sq_zero (z : Set.Icc (-1 : ℝ) 1) :
    meridianPosCoord z.1 0 ^ 2 = 1 - z.1 ^ 2 := by
  have hnonneg : 0 ≤ 1 - z.1 ^ 2 := by
    nlinarith [z.2.1, z.2.2]
  simpa [meridianPosCoord] using Real.sq_sqrt hnonneg

private lemma meridianMonomial_average_eq
    (d : Fin 3 →₀ ℕ) (c : ℝ) (z : Set.Icc (-1 : ℝ) 1) :
    ((2 : ℝ)⁻¹) *
        (MvPolynomial.eval (meridianPosCoord z.1) (MvPolynomial.monomial d c) +
          MvPolynomial.eval (meridianNegCoord z.1) (MvPolynomial.monomial d c)) =
      (if d 1 = 0 ∧ Even (d 0) then
        (Polynomial.C c * ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2) *
          Polynomial.X ^ (d 2)).eval z.1
      else 0) := by
  by_cases h1 : d 1 = 0 ∧ Even (d 0)
  · rcases h1.2 with ⟨k, hk⟩
    rw [if_pos h1, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    have hpow :
        meridianPosCoord z.1 0 ^ d 0 = (1 - z.1 ^ 2) ^ k := by
      rw [hk, ← two_mul, pow_mul, meridianPosCoord_sq_zero]
    have hnegpow :
        meridianNegCoord z.1 0 ^ d 0 = (1 - z.1 ^ 2) ^ k := by
      rw [hk, ← two_mul, pow_mul]
      have hsq :
          meridianNegCoord z.1 0 ^ 2 = 1 - z.1 ^ 2 := by
        have hnonneg : 0 ≤ 1 - z.1 ^ 2 := by
          nlinarith [z.2.1, z.2.2]
        simpa [meridianNegCoord] using Real.sq_sqrt hnonneg
      rw [hsq]
    have hprodPos :
        d.prod (fun i n => meridianPosCoord z.1 i ^ n) =
          (1 - z.1 ^ 2) ^ k * z.1 ^ d 2 := by
      have hmid : meridianPosCoord z.1 1 ^ d 1 = 1 := by
        calc
          meridianPosCoord z.1 1 ^ d 1 = meridianPosCoord z.1 1 ^ 0 := by rw [h1.1]
          _ = 1 := by simp
      rw [Finsupp.prod_fintype]
      · rw [Fin.prod_univ_three]
        rw [hmid]
        rw [hpow]
        rw [meridianPosCoord_two]
        ring
      · intro i
        simp
    have hprodNeg :
        d.prod (fun i n => meridianNegCoord z.1 i ^ n) =
          (1 - z.1 ^ 2) ^ k * z.1 ^ d 2 := by
      have hmid : meridianNegCoord z.1 1 ^ d 1 = 1 := by
        calc
          meridianNegCoord z.1 1 ^ d 1 = meridianNegCoord z.1 1 ^ 0 := by rw [h1.1]
          _ = 1 := by simp
      rw [Finsupp.prod_fintype]
      · rw [Fin.prod_univ_three]
        rw [hmid]
        rw [hnegpow]
        rw [meridianNegCoord_two]
        ring
      · intro i
        simp
    rw [hprodPos, hprodNeg]
    have hkdiv : (k + k) / 2 = k := by omega
    have hpolyEval :
        (Polynomial.C c * ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2) *
          Polynomial.X ^ (d 2)).eval z.1 =
          c * ((1 - z.1 ^ 2) ^ k * z.1 ^ d 2) := by
      rw [hk, hkdiv]
      simp [Polynomial.eval_mul, Polynomial.eval_pow]
      ring
    have havg :
        ((2 : ℝ)⁻¹) * (c * ((1 - z.1 ^ 2) ^ k * z.1 ^ d 2) + c * ((1 - z.1 ^ 2) ^ k * z.1 ^ d 2)) =
          c * ((1 - z.1 ^ 2) ^ k * z.1 ^ d 2) := by
      ring
    rw [havg]
    exact hpolyEval.symm
  · rw [if_neg h1, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    by_cases hz1 : d 1 = 0
    · have hodd : Odd (d 0) := Nat.not_even_iff_odd.mp (by
          intro hEven
          exact h1 ⟨hz1, hEven⟩)
      have hneg :
          meridianNegCoord z.1 0 ^ d 0 = -(meridianPosCoord z.1 0 ^ d 0) := by
        rw [meridianNegCoord, meridianPosCoord]
        rw [show -Real.sqrt (1 - z.1 ^ 2) = (-1 : ℝ) * Real.sqrt (1 - z.1 ^ 2) by ring]
        rw [mul_pow, hodd.neg_one_pow]
        ring_nf
      have hprodPos :
          d.prod (fun i n => meridianPosCoord z.1 i ^ n) =
            meridianPosCoord z.1 0 ^ d 0 * z.1 ^ d 2 := by
        have hmid : meridianPosCoord z.1 1 ^ d 1 = 1 := by
          calc
            meridianPosCoord z.1 1 ^ d 1 = meridianPosCoord z.1 1 ^ 0 := by rw [hz1]
            _ = 1 := by simp
        rw [Finsupp.prod_fintype]
        · rw [Fin.prod_univ_three]
          rw [hmid]
          rw [meridianPosCoord_two]
          ring
        · intro i
          simp
      have hprodNeg :
          d.prod (fun i n => meridianNegCoord z.1 i ^ n) =
            meridianNegCoord z.1 0 ^ d 0 * z.1 ^ d 2 := by
        have hmid : meridianNegCoord z.1 1 ^ d 1 = 1 := by
          calc
            meridianNegCoord z.1 1 ^ d 1 = meridianNegCoord z.1 1 ^ 0 := by rw [hz1]
            _ = 1 := by simp
        rw [Finsupp.prod_fintype]
        · rw [Fin.prod_univ_three]
          rw [hmid]
          rw [meridianNegCoord_two]
          ring
        · intro i
          simp
      rw [hprodPos, hprodNeg, hneg]
      ring
    · have hpowZeroPos : meridianPosCoord z.1 1 ^ d 1 = 0 := by
        simp [meridianPosCoord, hz1]
      have hpowZeroNeg : meridianNegCoord z.1 1 ^ d 1 = 0 := by
        simp [meridianNegCoord, hz1]
      have hprodPos :
          d.prod (fun i n => meridianPosCoord z.1 i ^ n) = 0 := by
        have hmid : meridianPosCoord z.1 1 ^ d 1 = 0 := hpowZeroPos
        rw [Finsupp.prod_fintype]
        · rw [Fin.prod_univ_three]
          rw [hmid]
          ring
        · intro i
          simp
      have hprodNeg :
          d.prod (fun i n => meridianNegCoord z.1 i ^ n) = 0 := by
        have hmid : meridianNegCoord z.1 1 ^ d 1 = 0 := hpowZeroNeg
        rw [Finsupp.prod_fintype]
        · rw [Fin.prod_univ_three]
          rw [hmid]
          ring
        · intro i
          simp
      rw [hprodPos, hprodNeg]
      ring

theorem northMeridianPolynomial_eval
    (p : MvPolynomial (Fin 3) ℝ) (z : Set.Icc (-1 : ℝ) 1) :
    (northMeridianPolynomial p).eval z.1 =
      ((2 : ℝ)⁻¹) *
        (MvPolynomial.eval (meridianPosCoord z.1) p +
          MvPolynomial.eval (meridianNegCoord z.1) p) := by
  rw [northMeridianPolynomial, Polynomial.eval_finset_sum]
  trans Finset.sum p.support
      (fun d =>
        ((2 : ℝ)⁻¹) *
          (MvPolynomial.eval (meridianPosCoord z.1) (MvPolynomial.monomial d (p.coeff d)) +
            MvPolynomial.eval (meridianNegCoord z.1) (MvPolynomial.monomial d (p.coeff d))))
  · refine Finset.sum_congr rfl ?_
    intro d hd
    by_cases h : d 1 = 0 ∧ Even (d 0)
    · simpa [h, Polynomial.eval_zero, Polynomial.eval_mul, Polynomial.eval_pow] using
        (meridianMonomial_average_eq d (p.coeff d) z).symm
    · simpa [h, Polynomial.eval_zero, Polynomial.eval_mul, Polynomial.eval_pow] using
        (meridianMonomial_average_eq d (p.coeff d) z).symm
  calc
    _ = ((2 : ℝ)⁻¹) *
          (Finset.sum p.support
              (fun d => MvPolynomial.eval (meridianPosCoord z.1) (MvPolynomial.monomial d (p.coeff d))) +
            Finset.sum p.support
              (fun d => MvPolynomial.eval (meridianNegCoord z.1) (MvPolynomial.monomial d (p.coeff d)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = ((2 : ℝ)⁻¹) *
          (MvPolynomial.eval (meridianPosCoord z.1) p +
            MvPolynomial.eval (meridianNegCoord z.1) p) := by
          calc
            ((2 : ℝ)⁻¹) *
                (∑ d ∈ p.support, (MvPolynomial.eval (meridianPosCoord z.1))
                    (MvPolynomial.monomial d (p.coeff d)) +
                  ∑ d ∈ p.support, (MvPolynomial.eval (meridianNegCoord z.1))
                    (MvPolynomial.monomial d (p.coeff d))) =
                ((2 : ℝ)⁻¹) *
                  (MvPolynomial.eval (meridianPosCoord z.1)
                      (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d)) +
                    MvPolynomial.eval (meridianNegCoord z.1)
                      (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d))) := by
                  rw [← map_sum, ← map_sum]
            _ = ((2 : ℝ)⁻¹) *
                  (MvPolynomial.eval (meridianPosCoord z.1) p +
                    MvPolynomial.eval (meridianNegCoord z.1) p) := by
                  congr 2
                  · rw [p.support_sum_monomial_coeff]
                  · rw [p.support_sum_monomial_coeff]
