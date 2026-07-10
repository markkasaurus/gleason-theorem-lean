import Gleason.Harmonic.Profile.SquaredProfileScaling
import Mathlib.Algebra.Polynomial.Eval.Degree

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

def sqQuotientRescalePolynomial (a : unitIcc) (q : ℝ[X]) : ℝ[X] :=
  q.comp (C a.1 * X)

@[simp] theorem sqQuotientRescalePolynomial_coeff
    (a : unitIcc) (q : ℝ[X]) (n : ℕ) :
    (sqQuotientRescalePolynomial a q).coeff n = q.coeff n * a.1 ^ n := by
  simp [sqQuotientRescalePolynomial, Polynomial.comp_C_mul_X_coeff]

@[simp] theorem sqQuotientRescalePolynomial_eval
    (a : unitIcc) (q : ℝ[X]) (u : unitIcc) :
    (sqQuotientRescalePolynomial a q).eval u.1 = q.eval (a.1 * u.1) := by
  simp [sqQuotientRescalePolynomial, Polynomial.eval_comp]

theorem sqProfilePolynomialMap_X_mul_sqQuotientRescalePolynomial
    (a : unitIcc) (ha : 0 < a.1) (q : ℝ[X]) :
    sqProfilePolynomialMap (X * sqQuotientRescalePolynomial a q) =
      sqProfileRescale a ha (sqProfilePolynomialMap (X * q)) := by
  ext u
  rw [sqProfileRescale_apply]
  change ((X * sqQuotientRescalePolynomial a q : ℝ[X]).eval u.1) =
    ((X * q : ℝ[X]).eval (a.1 * u.1)) / a.1
  simp [sqQuotientRescalePolynomial_eval, Polynomial.eval_mul]
  have ha0 : (a.1 : ℝ) ≠ 0 := ne_of_gt ha
  field_simp [ha0]

theorem sqProfileLinearPart_X_mul_sqQuotientRescalePolynomial
    (a : unitIcc) (q : ℝ[X]) :
    sqProfileLinearPart (X * sqQuotientRescalePolynomial a q) =
      sqProfileLinearPart (X * q) := by
  ext u
  simp [sqProfileLinearPart, sqQuotientRescalePolynomial_coeff]

theorem dist_sqProfilePolynomialMap_X_mul_sqQuotientRescalePolynomial_le_div
    (a : unitIcc) (ha : 0 < a.1) (q : ℝ[X]) (r : C(unitIcc, ℝ)) :
    dist (sqProfilePolynomialMap (X * sqQuotientRescalePolynomial a q))
        (sqProfileRescale a ha r)
      ≤ dist (sqProfilePolynomialMap (X * q)) r / a.1 := by
  rw [sqProfilePolynomialMap_X_mul_sqQuotientRescalePolynomial]
  exact dist_sqProfileRescale_le_div a ha (sqProfilePolynomialMap (X * q)) r

lemma sqProfileTailAbsSum_X_mul
    (q : ℝ[X]) :
    sqProfileTailAbsSum (X * q) =
      Finset.sum (q.support.erase 0) (fun n => |q.coeff n|) := by
  classical
  unfold sqProfileTailAbsSum
  have hsupp : (X * q).support.filter (fun n => 2 ≤ n) =
      (q.support.erase 0).image Nat.succ := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnsupp, hn2⟩
      have hn0 : n ≠ 0 := by omega
      rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨m, rfl⟩
      have hmcoeff : q.coeff m ≠ 0 := by
        simpa [Polynomial.coeff_X_mul] using (mem_support_iff.mp hnsupp)
      exact Finset.mem_image.mpr
        ⟨m, Finset.mem_erase.mpr ⟨by omega, mem_support_iff.mpr hmcoeff⟩, rfl⟩
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
      rcases Finset.mem_erase.mp hm with ⟨hm0, hmsupp⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, by omega⟩
      exact mem_support_iff.mpr (by
        simpa [Polynomial.coeff_X_mul] using (mem_support_iff.mp hmsupp))
  rw [hsupp]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro n hn
    rw [Polynomial.coeff_X_mul]
  · intro i hi j hj hij
    exact Nat.succ.inj hij

theorem sqProfileTailAbsSum_X_mul_sqQuotientRescalePolynomial_le
    (a : unitIcc) (q : ℝ[X]) :
    sqProfileTailAbsSum (X * sqQuotientRescalePolynomial a q) ≤
      a.1 * sqProfileTailAbsSum (X * q) := by
  classical
  rw [sqProfileTailAbsSum_X_mul, sqProfileTailAbsSum_X_mul]
  calc
    Finset.sum ((sqQuotientRescalePolynomial a q).support.erase 0)
        (fun n => |(sqQuotientRescalePolynomial a q).coeff n|)
      ≤ Finset.sum ((sqQuotientRescalePolynomial a q).support.erase 0)
          (fun n => a.1 * |q.coeff n|) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            calc
              |(sqQuotientRescalePolynomial a q).coeff n|
                = |q.coeff n * a.1 ^ n| := by simp
              _ = |q.coeff n| * a.1 ^ n := by
                    rw [abs_mul, abs_of_nonneg (pow_nonneg a.2.1 _)]
              _ ≤ |q.coeff n| * a.1 := by
                    rcases Finset.mem_erase.mp hn with ⟨hn0, _⟩
                    rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨m, rfl⟩
                    have hpow : a.1 ^ (m + 1) ≤ a.1 := by
                      have hpow1 : a.1 ^ m ≤ 1 := pow_le_one₀ a.2.1 a.2.2
                      calc
                        a.1 ^ (m + 1) = a.1 ^ m * a.1 := by rw [pow_succ]
                        _ ≤ 1 * a.1 := by
                              exact mul_le_mul_of_nonneg_right hpow1 a.2.1
                        _ = a.1 := by simp
                    gcongr
              _ = a.1 * |q.coeff n| := by ring
    _ ≤ Finset.sum (q.support.erase 0) (fun n => a.1 * |q.coeff n|) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro n hn
            rcases Finset.mem_erase.mp hn with ⟨hn0, hnsupp⟩
            refine Finset.mem_erase.mpr ⟨hn0, ?_⟩
            exact mem_support_iff.mpr (by
              intro hzero
              have hscoeff : (sqQuotientRescalePolynomial a q).coeff n = q.coeff n * a.1 ^ n := by
                simp
              have : (sqQuotientRescalePolynomial a q).coeff n = 0 := by
                rw [hscoeff, hzero]
                simp
              exact (mem_support_iff.mp hnsupp) this)
          · intro n hn1 hn2
            exact mul_nonneg a.2.1 (abs_nonneg _)
    _ = a.1 * Finset.sum (q.support.erase 0) (fun n => |q.coeff n|) := by
          rw [Finset.mul_sum]
