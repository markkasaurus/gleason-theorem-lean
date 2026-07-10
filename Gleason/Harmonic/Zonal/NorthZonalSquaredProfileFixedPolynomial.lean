import Gleason.Harmonic.Profile.SquaredProfileOperator
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

noncomputable def northZonalSqProfilePolynomial (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => C (northZonalScalarCoeff (2 * n) * a) * X ^ n

lemma coeff_northZonalSqProfilePolynomial (p : ℝ[X]) (n : ℕ) :
    (northZonalSqProfilePolynomial p).coeff n =
      northZonalScalarCoeff (2 * n) * p.coeff n := by
  classical
  rw [northZonalSqProfilePolynomial, Polynomial.sum_def, finset_sum_coeff]
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
    · have hpn : p.coeff n = 0 := notMem_support_iff.mp hs
      simp [hpn]
    · intro m hm
      rw [coeff_C_mul_X_pow]
      by_cases hmn : n = m
      · subst hmn
        exact False.elim (hs hm)
      · simp [hmn]

@[simp] lemma northZonalSqProfilePolynomial_C (a : ℝ) :
    northZonalSqProfilePolynomial (C a) = C (2 * a) := by
  ext n
  cases n with
  | zero =>
      simp [northZonalSqProfilePolynomial, northZonalScalarCoeff_zero]
  | succ n =>
      simp [coeff_northZonalSqProfilePolynomial]

@[simp] lemma northZonalSqProfilePolynomial_X :
    northZonalSqProfilePolynomial (X : ℝ[X]) = X := by
  ext n
  cases n with
  | zero =>
      simp [coeff_northZonalSqProfilePolynomial]
  | succ n =>
      cases n with
      | zero =>
          simp [coeff_northZonalSqProfilePolynomial, northZonalScalarCoeff_two]
      | succ n =>
          have hX : (X : ℝ[X]).coeff (Nat.succ (Nat.succ n)) = 0 := by
            simp [Polynomial.X, coeff_monomial]
          simp [coeff_northZonalSqProfilePolynomial, hX]

lemma eval_northZonalSqProfilePolynomial (p : ℝ[X]) (u : ℝ) :
    (northZonalSqProfilePolynomial p).eval u =
      Finset.sum p.support
        (fun n => (northZonalScalarCoeff (2 * n) * p.coeff n) * u ^ n) := by
  rw [northZonalSqProfilePolynomial, Polynomial.sum_def, Polynomial.eval_finset_sum]
  simp [mul_comm]

lemma northZonalSqProfileAverage_toContinuousMapOn
    (p : ℝ[X]) :
    northZonalSqProfileAverage (p.toContinuousMapOn unitIcc) =
      (northZonalSqProfilePolynomial p).toContinuousMapOn unitIcc := by
  ext u
  rw [northZonalSqProfileAverage_apply]
  change
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi, p.eval (sqMulCosSelfMap θ u).1) =
      (northZonalSqProfilePolynomial p).eval u.1
  rw [eval_northZonalSqProfilePolynomial]
  have hEval :
      (fun θ : ℝ => p.eval (sqMulCosSelfMap θ u).1) =
        (fun θ : ℝ =>
          Finset.sum p.support
            (fun n => p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))) := by
    funext θ
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [hEval]
  have hInt :
      ∀ i ∈ p.support,
        IntervalIntegrable
          (fun θ : ℝ => p.coeff i * ((sqMulCosSelfMap θ u).1 ^ i))
          volume 0 (2 * Real.pi) := by
    intro i hi
    have hcont :
        Continuous
          (fun θ : ℝ => p.coeff i * ((sqMulCosSelfMap θ u).1 ^ i)) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  rw [intervalIntegral.integral_finset_sum hInt]
  calc
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
        Finset.sum p.support
          (fun n =>
            ∫ θ in 0..2 * Real.pi, p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)))
      = Finset.sum p.support
          (fun n =>
            2 * (((2 * Real.pi)⁻¹ : ℝ) *
              (∫ θ in 0..2 * Real.pi, p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)))) := by
            calc
              2 * (((2 * Real.pi)⁻¹ : ℝ) *
                  Finset.sum p.support
                    (fun n =>
                      ∫ θ in 0..2 * Real.pi, p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)))
                = (2 * ((2 * Real.pi)⁻¹ : ℝ)) *
                    Finset.sum p.support
                      (fun n =>
                        ∫ θ in 0..2 * Real.pi, p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)) := by
                          ring
              _ = Finset.sum p.support
                    (fun n =>
                      (2 * ((2 * Real.pi)⁻¹ : ℝ)) *
                        (∫ θ in 0..2 * Real.pi, p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))) := by
                          rw [Finset.mul_sum]
              _ = Finset.sum p.support
                    (fun n =>
                      2 * (((2 * Real.pi)⁻¹ : ℝ) *
                        (∫ θ in 0..2 * Real.pi, p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)))) := by
                          refine Finset.sum_congr rfl ?_
                          intro n hn
                          ring
    _ = Finset.sum p.support
          (fun n => (northZonalScalarCoeff (2 * n) * p.coeff n) * u.1 ^ n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hstep1 :
                ∫ θ in 0..2 * Real.pi, p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n) =
                  p.coeff n * ∫ θ in 0..2 * Real.pi, ((sqMulCosSelfMap θ u).1 ^ n) := by
              rw [intervalIntegral.integral_const_mul]
            calc
              2 * (((2 * Real.pi)⁻¹ : ℝ) *
                  (∫ θ in 0..2 * Real.pi, p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)))
                = p.coeff n *
                    (2 * (((2 * Real.pi)⁻¹ : ℝ) *
                      ∫ θ in 0..2 * Real.pi, ((sqMulCosSelfMap θ u).1 ^ n))) := by
                        rw [hstep1]
                        ring
              _ = p.coeff n * (northZonalScalarCoeff (2 * n) * u.1 ^ n) := by
                    have hsq :
                        2 * (((2 * Real.pi)⁻¹ : ℝ) *
                          ∫ θ in 0..2 * Real.pi, ((sqMulCosSelfMap θ u).1 ^ n))
                          = northZonalScalarCoeff (2 * n) * u.1 ^ n := by
                      change
                        2 * (((2 * Real.pi)⁻¹ : ℝ) *
                          ∫ θ in 0..2 * Real.pi, (u.1 * Real.cos θ ^ 2) ^ n)
                          = northZonalScalarCoeff (2 * n) * u.1 ^ n
                      calc
                        2 * (((2 * Real.pi)⁻¹ : ℝ) *
                            ∫ θ in 0..2 * Real.pi, (u.1 * Real.cos θ ^ 2) ^ n)
                          = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
                              ∫ θ in 0..2 * Real.pi, u.1 ^ n * Real.cos θ ^ (2 * n)) := by
                                congr 2
                                apply intervalIntegral.integral_congr_ae
                                filter_upwards with θ hθ
                                rw [mul_pow]
                                ring
                        _ = northZonalScalarCoeff (2 * n) * u.1 ^ n := by
                              rw [intervalIntegral.integral_const_mul]
                              rw [northZonalScalarCoeff]
                              ring
                    rw [hsq]
              _ = (northZonalScalarCoeff (2 * n) * p.coeff n) * u.1 ^ n := by
                    ring

theorem northZonalSqProfilePolynomial_eq_of_eval_eq_on_Icc
    (p : ℝ[X])
    (hfix :
      ∀ u ∈ unitIcc,
        (northZonalSqProfilePolynomial p).eval u = p.eval u) :
    northZonalSqProfilePolynomial p = p := by
  let q : ℝ[X] := northZonalSqProfilePolynomial p - p
  have hsubset : unitIcc ⊆ {x : ℝ | IsRoot q x} := by
    intro u hu
    change q.eval u = 0
    have hu' := hfix u hu
    simpa [q] using sub_eq_zero.mpr hu'
  have hinf : Set.Infinite {x : ℝ | IsRoot q x} := by
    exact (Set.Icc_infinite (a := (0 : ℝ)) (b := 1) (by norm_num)).mono hsubset
  have hq : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q hinf
  exact sub_eq_zero.mp hq

theorem eq_C_mul_X_of_northZonalSqProfilePolynomial_fixed_of_eval_zero
    (p : ℝ[X])
    (hfix : northZonalSqProfilePolynomial p = p)
    (hp0 : p.eval 0 = 0) :
    p = C (p.coeff 1) * X := by
  ext n
  cases n with
  | zero =>
      have hcoeff0 : p.coeff 0 = 0 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
      simp [hcoeff0]
  | succ n =>
      cases n with
      | zero =>
          simp
      | succ n =>
          have hcoeffEq :
              northZonalScalarCoeff (2 * (n.succ.succ)) * p.coeff (n.succ.succ) =
                p.coeff (n.succ.succ) := by
            simpa [coeff_northZonalSqProfilePolynomial] using
              congrArg (fun q : ℝ[X] => q.coeff (n.succ.succ)) hfix
          have hlt :
              northZonalScalarCoeff (2 * (n + 2)) < 1 := by
            exact northZonalScalarCoeff_even_gt_two_lt_one_aux n
          have hlt' :
              northZonalScalarCoeff (2 * (n.succ.succ)) < 1 := by
            simpa [Nat.succ_eq_add_one, two_mul, add_assoc, add_left_comm, add_comm] using hlt
          have hmul :
              (northZonalScalarCoeff (2 * (n.succ.succ)) - 1) *
                p.coeff (n.succ.succ) = 0 := by
            nlinarith [hcoeffEq]
          have hne : northZonalScalarCoeff (2 * (n.succ.succ)) - 1 ≠ 0 := by
            linarith
          have hzero : p.coeff (n.succ.succ) = 0 :=
            (mul_eq_zero.mp hmul).resolve_left hne
          simp [hzero]

theorem eq_C_mul_X_of_northZonalSqProfilePolynomial_eval_eq_on_Icc_of_eval_zero
    (p : ℝ[X])
    (hfix :
      ∀ u ∈ unitIcc,
        (northZonalSqProfilePolynomial p).eval u = p.eval u)
    (hp0 : p.eval 0 = 0) :
    p = C (p.coeff 1) * X := by
  have hfixed : northZonalSqProfilePolynomial p = p :=
    northZonalSqProfilePolynomial_eq_of_eval_eq_on_Icc p hfix
  exact eq_C_mul_X_of_northZonalSqProfilePolynomial_fixed_of_eval_zero p hfixed hp0
