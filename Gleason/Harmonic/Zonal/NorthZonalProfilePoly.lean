import Gleason.Harmonic.Zonal.NorthZonalPolynomialOperator

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

lemma special_average_polynomial_eval
    (p : ℝ[X]) (r : Set.Icc (0 : ℝ) 1) :
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi, p.eval (r.1 * Real.cos θ)) =
      (northZonalScalarPolynomial p).eval r.1 := by
  rw [eval_northZonalScalarPolynomial]
  have hEval :
      (fun θ : ℝ => p.eval (r.1 * Real.cos θ)) =
        (fun θ : ℝ =>
          Finset.sum p.support (fun n => p.coeff n * (r.1 * Real.cos θ) ^ n)) := by
    funext θ
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [hEval]
  have hInt :
      ∀ i ∈ p.support,
        IntervalIntegrable (fun θ : ℝ => p.coeff i * (r.1 * Real.cos θ) ^ i)
          volume 0 (2 * Real.pi) := by
    intro i hi
    have hcont : Continuous (fun θ : ℝ => p.coeff i * (r.1 * Real.cos θ) ^ i) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  rw [intervalIntegral.integral_finset_sum hInt]
  simp_rw [intervalIntegral.integral_const_mul]
  calc
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
        Finset.sum p.support
          (fun n => p.coeff n * (∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n)))
      = Finset.sum p.support
          (fun n =>
            2 * (((2 * Real.pi)⁻¹ : ℝ) *
              (p.coeff n * (∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n)))) := by
            calc
              2 * (((2 * Real.pi)⁻¹ : ℝ) *
                  Finset.sum p.support
                    (fun n =>
                      p.coeff n * (∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n)))
                = (2 * ((2 * Real.pi)⁻¹ : ℝ)) *
                    Finset.sum p.support
                      (fun n =>
                        p.coeff n * (∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n)) := by ring
              _ = Finset.sum p.support
                    (fun n =>
                      (2 * ((2 * Real.pi)⁻¹ : ℝ)) *
                        (p.coeff n * (∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n))) := by
                          rw [Finset.mul_sum]
              _ = Finset.sum p.support
                    (fun n =>
                      2 * (((2 * Real.pi)⁻¹ : ℝ) *
                        (p.coeff n * (∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n)))) := by
                          refine Finset.sum_congr rfl ?_
                          intro n hn
                          ring
    _ = Finset.sum p.support (fun n => (northZonalScalarCoeff n * p.coeff n) * r.1 ^ n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          calc
            2 * (((2 * Real.pi)⁻¹ : ℝ) *
                (p.coeff n * ∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n))
              = p.coeff n *
                  (2 * (((2 * Real.pi)⁻¹ : ℝ) *
                    ∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n)) := by ring
            _ = p.coeff n * (northZonalScalarCoeff n * r.1 ^ n) := by
                  rw [monomial_special_average_eq_coeff_mul]
            _ = (northZonalScalarCoeff n * p.coeff n) * r.1 ^ n := by ring

theorem eq_C_mul_X_sq_of_centeredNorthZonalProfile_eq_polynomial
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (p : ℝ[X])
    (hpoly : ∀ z : Set.Icc (-1 : ℝ) 1,
      centeredNorthZonalProfile f z = p.eval z.1) :
    p = C (p.coeff 2) * X ^ 2 := by
  apply eq_C_mul_X_sq_of_northZonalScalarPolynomial_eval_eq_on_Icc_of_eval_zero
  · intro r hr
    let rr : Set.Icc (0 : ℝ) 1 := ⟨r, hr⟩
    have hconstraint :=
      centeredNorthZonalProfile_special_equation_of_mem_pointConstraint hfmem hfz rr
    have hfun :
        (fun θ : ℝ =>
          centeredNorthZonalProfile f ⟨rr.1 * Real.cos θ, mul_cos_mem_Icc rr θ⟩) =
        (fun θ : ℝ => p.eval (rr.1 * Real.cos θ)) := by
      funext θ
      simpa [rr] using hpoly ⟨rr.1 * Real.cos θ, mul_cos_mem_Icc rr θ⟩
    rw [hfun] at hconstraint
    rw [special_average_polynomial_eval p rr] at hconstraint
    have hpoly_rr :
        centeredNorthZonalProfile f (nonnegIccToIcc rr) = p.eval r := by
      simpa [rr, nonnegIccToIcc] using hpoly (nonnegIccToIcc rr)
    rw [hpoly_rr] at hconstraint
    exact hconstraint
  · simpa [centeredNorthZonalProfile_zero, zeroIcc] using (hpoly zeroIcc).symm

theorem centeredNorthZonalProfile_eq_quadratic_of_polynomial
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (p : ℝ[X])
    (hpoly : ∀ z : Set.Icc (-1 : ℝ) 1,
      centeredNorthZonalProfile f z = p.eval z.1) :
    ∀ z : Set.Icc (-1 : ℝ) 1,
      centeredNorthZonalProfile f z = p.coeff 2 * z.1 ^ 2 := by
  have hp :
      p = C (p.coeff 2) * X ^ 2 :=
    eq_C_mul_X_sq_of_centeredNorthZonalProfile_eq_polynomial hfmem hfz p hpoly
  intro z
  rw [hpoly z, hp]
  simp

theorem isNorthZonal_eq_const_add_sq_of_polynomial
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (p : ℝ[X])
    (hpoly : ∀ z : Set.Icc (-1 : ℝ) 1,
      centeredNorthZonalProfile f z = p.eval z.1) :
    ∀ x : spherePoint3,
      f x = f sphereE2 + p.coeff 2 * sphereCoordZ x ^ 2 := by
  intro x
  have hquad :=
    centeredNorthZonalProfile_eq_quadratic_of_polynomial hfmem hfz p hpoly
      ⟨sphereCoordZ x, snd_mem_Icc x⟩
  have hprof := northZonalProfile_eq_of_isNorthZonal hfz x
  calc
    f x = northZonalProfile f ⟨sphereCoordZ x, snd_mem_Icc x⟩ := by
      simpa [sphereCoordZ] using hprof.symm
    _ = centeredNorthZonalProfile f ⟨sphereCoordZ x, snd_mem_Icc x⟩ +
          northZonalProfile f zeroIcc := by
            simp [centeredNorthZonalProfile]
    _ = p.coeff 2 * sphereCoordZ x ^ 2 + f sphereE2 := by
          rw [hquad, northZonalProfile_zero_of_isNorthZonal hfz]
    _ = f sphereE2 + p.coeff 2 * sphereCoordZ x ^ 2 := by ring
