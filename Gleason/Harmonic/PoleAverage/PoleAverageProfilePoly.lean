import Gleason.Harmonic.Auxiliary.PoleAverage
import Gleason.Harmonic.HighDegree.EvenBoundedQ02
import Gleason.Harmonic.Zonal.NorthZonalProfilePoly

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

theorem poleAverageLinear_specialZPoint_eq_northMeridian_average
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g)
    (r : Set.Icc (0 : ℝ) 1) :
    poleAverageLinear g (specialZPoint r) =
      ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, (northMeridianPolynomial p).eval (r.1 * Real.cos θ) := by
  rw [poleAverageLinear_eq_greatCircleAverageLinear
      g (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)]
  rw [greatCircleAverageLinear_special_of_isNorthZonal hgz r]
  refine congrArg (((2 * Real.pi)⁻¹ : ℝ) * ·) ?_
  apply intervalIntegral.integral_congr_ae
  filter_upwards with θ hθ
  simpa using
    northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
      hgz hpEval ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩

theorem two_mul_poleAverageLinear_specialZPoint_eq_northZonalScalarPolynomial
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g)
    (r : Set.Icc (0 : ℝ) 1) :
    2 * poleAverageLinear g (specialZPoint r) =
      (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 := by
  rw [poleAverageLinear_specialZPoint_eq_northMeridian_average hgz hpEval r]
  exact special_average_polynomial_eval (northMeridianPolynomial p) r
