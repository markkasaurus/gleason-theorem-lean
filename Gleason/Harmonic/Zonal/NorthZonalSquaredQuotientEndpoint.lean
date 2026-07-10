import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientFixedContinuous
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileQuadratic

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

theorem northZonalSqQuotientAverage_fixed_of_sqProfile_factor
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (q : C(unitIcc, ℝ))
    (hq : ∀ u : unitIcc, sqCenteredNorthZonalProfile f u = u.1 * q u) :
    northZonalSqQuotientAverage q = q := by
  ext u
  by_cases hu0 : u.1 = 0
  · have huz : u = zeroUnitIcc := by
      apply Subtype.ext
      simp [zeroUnitIcc, hu0]
    subst huz
    rw [northZonalSqQuotientAverage_apply]
    have hfun :
        (fun θ : ℝ => Real.cos θ ^ 2 * q (sqMulCosSelfMap θ zeroUnitIcc)) =
          fun θ : ℝ => Real.cos θ ^ 2 * q zeroUnitIcc := by
      funext θ
      congr 1
      apply congrArg q
      apply Subtype.ext
      simp [sqMulCosSelfMap, zeroUnitIcc]
    rw [hfun]
    have hcosSq :
        ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 = Real.pi := by
      rw [integral_cos_sq]
      simp
    rw [intervalIntegral.integral_mul_const, hcosSq]
    field_simp [Real.pi_ne_zero]
  · have hu : 0 < u.1 := lt_of_le_of_ne u.2.1 (Ne.symm hu0)
    have hconstraint :=
      sqCenteredNorthZonalProfile_special_equation_of_mem_pointConstraint hfmem hfz u
    have hconstraint' :
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi, u.1 * (Real.cos θ ^ 2 * q (sqMulCosSelfMap θ u))) =
          u.1 * q u := by
      calc
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi, u.1 * (Real.cos θ ^ 2 * q (sqMulCosSelfMap θ u)))
            = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
                ∫ θ in 0..2 * Real.pi, sqCenteredNorthZonalProfile f (sqMulCosSelfMap θ u)) := by
                  congr 2
                  apply intervalIntegral.integral_congr_ae
                  filter_upwards with θ hθ
                  rw [hq (sqMulCosSelfMap θ u)]
                  simp [sqMulCosSelfMap]
                  ring
        _ = sqCenteredNorthZonalProfile f u := hconstraint
        _ = u.1 * q u := hq u
    have hmul :
        u.1 * northZonalSqQuotientAverage q u = u.1 * q u := by
      calc
        u.1 * northZonalSqQuotientAverage q u
            = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
                ∫ θ in 0..2 * Real.pi, u.1 * (Real.cos θ ^ 2 * q (sqMulCosSelfMap θ u))) := by
                  rw [northZonalSqQuotientAverage_apply, intervalIntegral.integral_const_mul]
                  ring
        _ = u.1 * q u := hconstraint'
    nlinarith

theorem mem_continuousSphereQuadraticSubmodule_of_isNorthZonal_pointConstraint_sqquotient_factor
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (q : C(unitIcc, ℝ))
    (hq : ∀ u : unitIcc, sqCenteredNorthZonalProfile f u = u.1 * q u) :
    f ∈ continuousSphereQuadraticSubmodule := by
  have hfix :
      northZonalSqQuotientAverage q = q :=
    northZonalSqQuotientAverage_fixed_of_sqProfile_factor hfmem hfz q hq
  have hconst :
      q = ContinuousMap.const _ (q zeroUnitIcc) :=
    northZonalSqQuotientAverage_eq_const_of_fixed q hfix
  let p : ℝ[X] := C (q zeroUnitIcc) * X
  have hpoly :
      ∀ u : unitIcc, sqCenteredNorthZonalProfile f u = p.eval u.1 := by
    intro u
    have hqu : q u = q zeroUnitIcc := by
      have := congrArg (fun g : C(unitIcc, ℝ) => g u) hconst
      simpa using this
    rw [hq u, hqu]
    simp [p]
    ring
  exact mem_continuousSphereQuadraticSubmodule_of_isNorthZonal_pointConstraint_sqPolynomial
    hfmem hfz p hpoly

theorem exists_quadraticMap_of_isNorthZonal_pointConstraint_sqquotient_factor
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (q : C(unitIcc, ℝ))
    (hq : ∀ u : unitIcc, sqCenteredNorthZonalProfile f u = u.1 * q u) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ,
      ∀ x : spherePoint3, f x = Q x.1 := by
  have hmem :
      f ∈ continuousSphereQuadraticSubmodule :=
    mem_continuousSphereQuadraticSubmodule_of_isNorthZonal_pointConstraint_sqquotient_factor
      hfmem hfz q hq
  exact hmem
