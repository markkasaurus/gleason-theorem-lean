import Gleason.Harmonic.Zonal.NorthZonalMoments
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

noncomputable def northZonalScalarPolynomial (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => C (northZonalScalarCoeff n * a) * X ^ n

lemma coeff_northZonalScalarPolynomial (p : ℝ[X]) (n : ℕ) :
    (northZonalScalarPolynomial p).coeff n = northZonalScalarCoeff n * p.coeff n := by
  classical
  rw [northZonalScalarPolynomial, Polynomial.sum_def, finset_sum_coeff]
  by_cases hs : n ∈ p.support
  · rw [Finset.sum_eq_single_of_mem n hs]
    · rw [coeff_C_mul_X_pow]
      simp
    · intro m hm hmn
      rw [coeff_C_mul_X_pow]
      by_cases hnm : n = m
      · exact False.elim (hmn hnm.symm)
      · simp [hnm]
  · rw [Finset.sum_eq_zero]
    · have hpn : p.coeff n = 0 := by
        exact notMem_support_iff.mp hs
      simp [hpn]
    · intro m hm
      rw [coeff_C_mul_X_pow]
      by_cases hmn : n = m
      · subst hmn
        exact False.elim (hs hm)
      · simp [hmn]

lemma eval_northZonalScalarPolynomial (p : ℝ[X]) (r : ℝ) :
    (northZonalScalarPolynomial p).eval r =
      Finset.sum p.support (fun n => (northZonalScalarCoeff n * p.coeff n) * r ^ n) := by
  rw [northZonalScalarPolynomial, Polynomial.sum_def, Polynomial.eval_finset_sum]
  simp [mul_comm, mul_left_comm]

theorem northZonalScalarPolynomial_eq_of_eval_eq_on_Icc
    (p : ℝ[X])
    (hfix :
      ∀ r ∈ Set.Icc (0 : ℝ) 1,
        (northZonalScalarPolynomial p).eval r = p.eval r) :
    northZonalScalarPolynomial p = p := by
  let q : ℝ[X] := northZonalScalarPolynomial p - p
  have hsubset : Set.Icc (0 : ℝ) 1 ⊆ {x : ℝ | IsRoot q x} := by
    intro r hr
    change q.eval r = 0
    have hrw := hfix r hr
    simpa [q] using sub_eq_zero.mpr hrw
  have hinf : Set.Infinite {x : ℝ | IsRoot q x} := by
    exact (Set.Icc_infinite (a := (0 : ℝ)) (b := 1) (by norm_num)).mono hsubset
  have hq : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q hinf
  exact sub_eq_zero.mp hq

theorem coeff_eq_zero_of_northZonalScalarPolynomial_fixed
    (p : ℝ[X])
    (hfix : northZonalScalarPolynomial p = p)
    {n : ℕ} (h0 : n ≠ 0) (h2 : n ≠ 2) :
    p.coeff n = 0 := by
  have hcoeffEq :
      northZonalScalarCoeff n * p.coeff n = p.coeff n := by
    simpa [coeff_northZonalScalarPolynomial] using congrArg (fun q : ℝ[X] => q.coeff n) hfix
  cases Nat.even_or_odd n with
  | inl hEven =>
      rcases hEven with ⟨m, rfl⟩
      cases m with
      | zero =>
          exact False.elim (h0 rfl)
      | succ m =>
          cases m with
          | zero =>
              exact False.elim (h2 rfl)
          | succ m =>
              have hcoeffEq' :
                  northZonalScalarCoeff (2 * (m + 2)) * p.coeff (2 * (m + 2)) =
                    p.coeff (2 * (m + 2)) := by
                simpa [two_mul, add_assoc, add_left_comm, add_comm] using hcoeffEq
              have hlt :
                  northZonalScalarCoeff (2 * (m + 2)) < 1 := by
                exact northZonalScalarCoeff_even_gt_two_lt_one_aux m
              have hmul :
                  (northZonalScalarCoeff (2 * (m + 2)) - 1) * p.coeff (2 * (m + 2)) = 0 := by
                nlinarith [hcoeffEq']
              have hne : northZonalScalarCoeff (2 * (m + 2)) - 1 ≠ 0 := by
                linarith
              simpa [two_mul, add_assoc, add_left_comm, add_comm] using
                (mul_eq_zero.mp hmul).resolve_left hne
  | inr hOdd =>
      rcases hOdd with ⟨m, rfl⟩
      simpa [northZonalScalarCoeff_odd] using hcoeffEq.symm

theorem eq_C_mul_X_sq_of_northZonalScalarPolynomial_fixed_of_eval_zero
    (p : ℝ[X])
    (hfix : northZonalScalarPolynomial p = p)
    (hp0 : p.eval 0 = 0) :
    p = C (p.coeff 2) * X ^ 2 := by
  ext n
  by_cases h2 : n = 2
  · subst h2
    simp
  · by_cases h0 : n = 0
    · subst h0
      have hcoeff0 : p.coeff 0 = 0 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
      simp [hcoeff0, h2]
    · have hnz : p.coeff n = 0 :=
          coeff_eq_zero_of_northZonalScalarPolynomial_fixed p hfix h0 h2
      simp [hnz, h0, h2]

theorem eq_C_mul_X_sq_of_northZonalScalarPolynomial_eval_eq_on_Icc_of_eval_zero
    (p : ℝ[X])
    (hfix :
      ∀ r ∈ Set.Icc (0 : ℝ) 1,
        (northZonalScalarPolynomial p).eval r = p.eval r)
    (hp0 : p.eval 0 = 0) :
    p = C (p.coeff 2) * X ^ 2 := by
  have hfixed : northZonalScalarPolynomial p = p :=
    northZonalScalarPolynomial_eq_of_eval_eq_on_Icc p hfix
  exact eq_C_mul_X_sq_of_northZonalScalarPolynomial_fixed_of_eval_zero p hfixed hp0

theorem northZonalScalarPolynomial_ne_neg_of_coeff_ne_zero_of_even_gt_two
    (p : ℝ[X]) {n : ℕ}
    (hnEven : Even n) (hn : 2 < n)
    (hcoeff : p.coeff n ≠ 0) :
    northZonalScalarPolynomial p ≠ -p := by
  intro hneg
  have hcoeffEq :
      northZonalScalarCoeff n * p.coeff n = -p.coeff n := by
    simpa [coeff_northZonalScalarPolynomial] using
      congrArg (fun q : ℝ[X] => q.coeff n) hneg
  have hs : northZonalScalarCoeff n ≠ -1 := by
    rcases hnEven with ⟨k, hk⟩
    subst hk
    cases k with
    | zero =>
        omega
    | succ k =>
        cases k with
        | zero =>
            omega
        | succ k =>
            have hpos : 0 < northZonalScalarCoeff (2 * (k + 2)) := by
              exact northZonalScalarCoeff_even_pos (k + 2)
            have hpos' : 0 < northZonalScalarCoeff (k + 1 + 1 + (k + 1 + 1)) := by
              simpa [two_mul, add_assoc, add_left_comm, add_comm] using hpos
            linarith
  have hmul : (northZonalScalarCoeff n + 1) * p.coeff n = 0 := by
    linarith
  have hsplus : northZonalScalarCoeff n + 1 = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hcoeff
  apply hs
  linarith

theorem northZonalScalarPolynomial_eq_neg_iff_eq_zero
    (p : ℝ[X]) :
    northZonalScalarPolynomial p = -p ↔ p = 0 := by
  constructor
  · intro hneg
    ext n
    have hcoeffEq :
        northZonalScalarCoeff n * p.coeff n = -p.coeff n := by
      simpa [coeff_northZonalScalarPolynomial] using
        congrArg (fun q : ℝ[X] => q.coeff n) hneg
    have hs : northZonalScalarCoeff n ≠ -1 := by
      cases Nat.even_or_odd n with
      | inl hEven =>
          rcases hEven with ⟨k, hk⟩
          subst hk
          have hpos : 0 < northZonalScalarCoeff (2 * k) := by
            exact northZonalScalarCoeff_even_pos k
          have hpos' : 0 < northZonalScalarCoeff (k + k) := by
            simpa [two_mul, add_assoc, add_left_comm, add_comm] using hpos
          linarith
      | inr hOdd =>
          rcases hOdd with ⟨k, hk⟩
          subst hk
          simp [northZonalScalarCoeff_odd]
    have hmul : (northZonalScalarCoeff n + 1) * p.coeff n = 0 := by
      linarith
    have hsplus : northZonalScalarCoeff n + 1 ≠ 0 := by
      intro hs0
      apply hs
      linarith
    exact (mul_eq_zero.mp hmul).resolve_left hsplus
  · intro hp
    subst hp
    simp [northZonalScalarPolynomial]
