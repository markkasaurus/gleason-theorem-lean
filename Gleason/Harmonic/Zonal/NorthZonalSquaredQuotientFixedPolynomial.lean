import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientDynamics

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

theorem northZonalSqQuotientPolynomial_eq_C_of_fixed
    (p : ℝ[X])
    (hfix : northZonalSqQuotientPolynomial p = p) :
    northZonalSqQuotientPolynomial p = C (p.coeff 0) := by
  rw [hfix]
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      have hnpos : 0 < n.succ := Nat.succ_pos _
      have hcoeff :
          northZonalSqQuotientScalarCoeff n.succ * p.coeff n.succ = p.coeff n.succ := by
        have := congrArg (fun q : ℝ[X] => q.coeff n.succ) hfix
        simpa [coeff_northZonalSqQuotientPolynomial] using this
      have hpzero : p.coeff n.succ = 0 := by
        by_contra hp
        have hlam : northZonalSqQuotientScalarCoeff n.succ = 1 := by
          exact mul_right_cancel₀ hp (by simpa [one_mul] using hcoeff)
        exact (ne_of_lt (northZonalSqQuotientScalarCoeff_lt_one hnpos)) hlam
      simpa [hpzero]

theorem northZonalSqQuotientPolynomial_eq_zero_of_fixed_of_coeff_zero
    (p : ℝ[X])
    (hfix : northZonalSqQuotientPolynomial p = p)
    (hzero : p.coeff 0 = 0) :
    p = 0 := by
  have hconst := northZonalSqQuotientPolynomial_eq_C_of_fixed p hfix
  rw [hfix, hzero, C_0] at hconst
  exact hconst
