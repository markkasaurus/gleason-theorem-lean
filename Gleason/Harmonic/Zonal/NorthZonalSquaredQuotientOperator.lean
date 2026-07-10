import Gleason.Harmonic.Zonal.NorthZonalSquaredProfile
import Gleason.Harmonic.Zonal.NorthZonalMoments
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

abbrev unitIcc := Set.Icc (0 : ℝ) 1

def sqMulCosSelfMap (θ : ℝ) (u : unitIcc) : unitIcc :=
  ⟨u.1 * Real.cos θ ^ 2, mul_cos_sq_mem_Icc u θ⟩

@[simp] lemma sqMulCosSelfMap_val (θ : ℝ) (u : unitIcc) :
    (sqMulCosSelfMap θ u : ℝ) = u.1 * Real.cos θ ^ 2 := by
  rfl

def sqMulCosSelfContinuous (θ : ℝ) : C(unitIcc, unitIcc) :=
  ⟨sqMulCosSelfMap θ,
    Continuous.subtype_mk
      ((continuous_subtype_val : Continuous fun u : unitIcc => u.1).mul continuous_const)
      (fun u => mul_cos_sq_mem_Icc u θ)⟩

def northZonalSqQuotientOrbit (f : C(unitIcc, ℝ)) (θ : ℝ) : C(unitIcc, ℝ) :=
  (Real.cos θ ^ 2) • f.comp (sqMulCosSelfContinuous θ)

@[simp] lemma northZonalSqQuotientOrbit_apply
    (f : C(unitIcc, ℝ)) (θ : ℝ) (u : unitIcc) :
    northZonalSqQuotientOrbit f θ u =
      Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u) := by
  simp [northZonalSqQuotientOrbit, sqMulCosSelfContinuous]

lemma northZonalSqQuotientOrbitContinuous (f : C(unitIcc, ℝ)) :
    Continuous (fun θ : ℝ => northZonalSqQuotientOrbit f θ) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hcosSq : Continuous fun p : ℝ × unitIcc => Real.cos p.1 ^ 2 := by
    exact (Real.continuous_cos.comp continuous_fst).pow 2
  have harg : Continuous fun p : ℝ × unitIcc => sqMulCosSelfMap p.1 p.2 := by
    exact Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_snd).mul hcosSq)
      (fun p => mul_cos_sq_mem_Icc p.2 p.1)
  simpa [northZonalSqQuotientOrbit, sqMulCosSelfContinuous, smul_eq_mul] using
    hcosSq.mul (f.continuous.comp harg)

lemma northZonalSqQuotientOrbit_intervalIntegrable (f : C(unitIcc, ℝ)) :
    IntervalIntegrable (fun θ : ℝ => northZonalSqQuotientOrbit f θ)
      volume 0 (2 * Real.pi) := by
  exact (northZonalSqQuotientOrbitContinuous f).intervalIntegrable 0 (2 * Real.pi)

def northZonalSqQuotientAverage (f : C(unitIcc, ℝ)) : C(unitIcc, ℝ) :=
  (2 * ((2 * Real.pi)⁻¹ : ℝ)) •
    ∫ θ in 0..2 * Real.pi, northZonalSqQuotientOrbit f θ

@[simp] theorem northZonalSqQuotientAverage_apply (f : C(unitIcc, ℝ)) (u : unitIcc) :
    northZonalSqQuotientAverage f u =
      2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u)) := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hInt :
      Integrable (fun θ : ℝ => northZonalSqQuotientOrbit f θ)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    exact (northZonalSqQuotientOrbitContinuous f).integrableOn_Ioc
  rw [northZonalSqQuotientAverage, ContinuousMap.smul_apply, smul_eq_mul]
  rw [intervalIntegral_eq_integral_uIoc]
  simp [hpi]
  rw [ContinuousMap.integral_apply hInt u]
  simp [intervalIntegral_eq_integral_uIoc, hpi, northZonalSqQuotientOrbit,
    sqMulCosSelfContinuous]
  ring_nf

theorem norm_northZonalSqQuotientAverage_le (f : C(unitIcc, ℝ)) :
    ‖northZonalSqQuotientAverage f‖ ≤ ‖f‖ := by
  haveI : Nonempty unitIcc := ⟨⟨0, by constructor <;> norm_num⟩⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := northZonalSqQuotientAverage f) (M := ‖f‖)).2 ?_
  intro u
  rw [northZonalSqQuotientAverage_apply]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hcosSqInt : ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 = Real.pi := by
    rw [integral_cos_sq]
    simp
  have hInt1 :
      IntervalIntegrable
        (fun θ : ℝ => ‖Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u)‖)
        volume 0 (2 * Real.pi) := by
    have hcont :
        Continuous (fun θ : ℝ => ‖Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u)‖) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  have hInt2 :
      IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ 2 * ‖f‖) volume 0 (2 * Real.pi) := by
    have hcont : Continuous (fun θ : ℝ => Real.cos θ ^ 2 * ‖f‖) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  calc
    ‖2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u))‖
      = (2 * (2 * Real.pi)⁻¹) *
          ‖∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u)‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            rw [abs_of_pos, abs_of_pos]
            · ring
            · positivity
            · positivity
    _ ≤ (2 * (2 * Real.pi)⁻¹) *
          ∫ θ in 0..2 * Real.pi, ‖Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u)‖ := by
          gcongr
          exact intervalIntegral.norm_integral_le_integral_norm hpi.le
    _ ≤ (2 * (2 * Real.pi)⁻¹) * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * ‖f‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine intervalIntegral.integral_mono_on hpi.le hInt1 hInt2 ?_
          intro θ hθ
          calc
            ‖Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u)‖
              = |Real.cos θ ^ 2| * ‖f (sqMulCosSelfMap θ u)‖ := by
                  rw [norm_mul]
                  simp
            _ ≤ Real.cos θ ^ 2 * ‖f‖ := by
                  rw [abs_of_nonneg (sq_nonneg (Real.cos θ))]
                  gcongr
                  exact f.norm_coe_le_norm (sqMulCosSelfMap θ u)
    _ = ‖f‖ := by
          rw [intervalIntegral.integral_mul_const, hcosSqInt]
          field_simp [Real.pi_ne_zero]

def northZonalSqQuotientScalarCoeff (n : ℕ) : ℝ :=
  northZonalScalarCoeff (2 * n + 2)

@[simp] lemma northZonalSqQuotientScalarCoeff_zero :
    northZonalSqQuotientScalarCoeff 0 = 1 := by
  simp [northZonalSqQuotientScalarCoeff]

lemma northZonalSqQuotientScalarCoeff_lt_one {n : ℕ} (hn : 0 < n) :
    northZonalSqQuotientScalarCoeff n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨k, rfl⟩
  simpa [northZonalSqQuotientScalarCoeff, two_mul, add_assoc, add_left_comm, add_comm] using
    northZonalScalarCoeff_even_gt_two_lt_one_aux k

lemma northZonalSqQuotientScalarCoeff_nonneg (n : ℕ) :
    0 ≤ northZonalSqQuotientScalarCoeff n := by
  exact le_of_lt (northZonalScalarCoeff_even_pos (n + 1))

noncomputable def northZonalSqQuotientPolynomial (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => C (northZonalSqQuotientScalarCoeff n * a) * X ^ n

lemma coeff_northZonalSqQuotientPolynomial (p : ℝ[X]) (n : ℕ) :
    (northZonalSqQuotientPolynomial p).coeff n =
      northZonalSqQuotientScalarCoeff n * p.coeff n := by
  classical
  rw [northZonalSqQuotientPolynomial, Polynomial.sum_def, finset_sum_coeff]
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

lemma eval_northZonalSqQuotientPolynomial (p : ℝ[X]) (u : ℝ) :
    (northZonalSqQuotientPolynomial p).eval u =
      Finset.sum p.support
        (fun n => (northZonalSqQuotientScalarCoeff n * p.coeff n) * u ^ n) := by
  rw [northZonalSqQuotientPolynomial, Polynomial.sum_def, Polynomial.eval_finset_sum]
  simp [mul_comm, mul_left_comm]

lemma northZonalSqQuotientAverage_toContinuousMapOn
    (p : ℝ[X]) :
    northZonalSqQuotientAverage (p.toContinuousMapOn (Set.Icc (0 : ℝ) 1)) =
      (northZonalSqQuotientPolynomial p).toContinuousMapOn (Set.Icc (0 : ℝ) 1) := by
  ext u
  rw [northZonalSqQuotientAverage_apply]
  change
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * p.eval (sqMulCosSelfMap θ u).1) =
      (northZonalSqQuotientPolynomial p).eval u.1
  rw [eval_northZonalSqQuotientPolynomial]
  have hEval :
      (fun θ : ℝ => Real.cos θ ^ 2 * p.eval (sqMulCosSelfMap θ u).1) =
        (fun θ : ℝ =>
          Finset.sum p.support
            (fun n => Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)))) := by
    funext θ
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  rw [hEval]
  have hInt :
      ∀ i ∈ p.support,
        IntervalIntegrable
          (fun θ : ℝ => Real.cos θ ^ 2 * (p.coeff i * ((sqMulCosSelfMap θ u).1 ^ i)))
          volume 0 (2 * Real.pi) := by
    intro i hi
    have hcont :
        Continuous
          (fun θ : ℝ => Real.cos θ ^ 2 * (p.coeff i * ((sqMulCosSelfMap θ u).1 ^ i))) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  rw [intervalIntegral.integral_finset_sum hInt]
  calc
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
        Finset.sum p.support
          (fun n =>
            ∫ θ in 0..2 * Real.pi,
              Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))))
      = Finset.sum p.support
          (fun n =>
            2 * (((2 * Real.pi)⁻¹ : ℝ) *
              (∫ θ in 0..2 * Real.pi,
                Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))))) := by
            calc
              2 * (((2 * Real.pi)⁻¹ : ℝ) *
                  Finset.sum p.support
                    (fun n =>
                      ∫ θ in 0..2 * Real.pi,
                        Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))))
                = (2 * ((2 * Real.pi)⁻¹ : ℝ)) *
                    Finset.sum p.support
                      (fun n =>
                        ∫ θ in 0..2 * Real.pi,
                          Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))) := by ring
              _ = Finset.sum p.support
                    (fun n =>
                      (2 * ((2 * Real.pi)⁻¹ : ℝ)) *
                        (∫ θ in 0..2 * Real.pi,
                          Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)))) := by
                            rw [Finset.mul_sum]
              _ = Finset.sum p.support
                    (fun n =>
                      2 * (((2 * Real.pi)⁻¹ : ℝ) *
                        (∫ θ in 0..2 * Real.pi,
                          Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))))) := by
                            refine Finset.sum_congr rfl ?_
                            intro n hn
                            ring
    _ = Finset.sum p.support
          (fun n => (northZonalSqQuotientScalarCoeff n * p.coeff n) * u.1 ^ n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hstep1 :
              ∫ θ in 0..2 * Real.pi,
                Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n)) =
                  p.coeff n *
                    ∫ θ in 0..2 * Real.pi,
                      ((sqMulCosSelfMap θ u).1 ^ n * Real.cos θ ^ 2) := by
            have hrew :
                (fun θ : ℝ =>
                  Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))) =
                  (fun θ : ℝ =>
                    p.coeff n * (((sqMulCosSelfMap θ u).1 ^ n) * Real.cos θ ^ 2)) := by
                      funext θ
                      ring
            rw [hrew, intervalIntegral.integral_const_mul]
          have hstep2 :
              ∫ θ in 0..2 * Real.pi,
                ((sqMulCosSelfMap θ u).1 ^ n * Real.cos θ ^ 2) =
                  ∫ θ in 0..2 * Real.pi, (u.1 * Real.cos θ ^ 2) ^ n * Real.cos θ ^ 2 := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with θ
            simp [sqMulCosSelfMap]
          calc
            2 * (((2 * Real.pi)⁻¹ : ℝ) *
                (∫ θ in 0..2 * Real.pi,
                  Real.cos θ ^ 2 * (p.coeff n * ((sqMulCosSelfMap θ u).1 ^ n))))
              = p.coeff n *
                  (2 * (((2 * Real.pi)⁻¹ : ℝ) *
                    ∫ θ in 0..2 * Real.pi,
                      ((sqMulCosSelfMap θ u).1 ^ n * Real.cos θ ^ 2))) := by
                        rw [hstep1]
                        ring
            _ = p.coeff n *
                  (2 * (((2 * Real.pi)⁻¹ : ℝ) *
                    ∫ θ in 0..2 * Real.pi, (u.1 * Real.cos θ ^ 2) ^ n * Real.cos θ ^ 2)) := by
                      rw [hstep2]
            _ = p.coeff n * (northZonalSqQuotientScalarCoeff n * u.1 ^ n) := by
                  rw [show (fun θ : ℝ => (u.1 * Real.cos θ ^ 2) ^ n * Real.cos θ ^ 2) =
                      (fun θ : ℝ => u.1 ^ n * Real.cos θ ^ (2 * n + 2)) by
                        funext θ
                        ring_nf]
                  rw [intervalIntegral.integral_const_mul]
                  have hone :
                      2 * (((2 * Real.pi)⁻¹ : ℝ) *
                        ∫ θ in 0..2 * Real.pi, ((1 : ℝ) * Real.cos θ) ^ (2 * n + 2)) =
                          northZonalScalarCoeff (2 * n + 2) * (1 : ℝ) ^ (2 * n + 2) := by
                    simpa using monomial_special_average_eq_coeff_mul (2 * n + 2)
                      (⟨(1 : ℝ), by constructor <;> norm_num⟩ : unitIcc)
                  have hcos :
                      2 * (((2 * Real.pi)⁻¹ : ℝ) *
                        ∫ θ in 0..2 * Real.pi, Real.cos θ ^ (2 * n + 2)) =
                          northZonalScalarCoeff (2 * n + 2) := by
                    simpa using hone
                  calc
                    p.coeff n *
                        (2 * (((2 * Real.pi)⁻¹ : ℝ) *
                          (u.1 ^ n * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ (2 * n + 2))))
                      = p.coeff n *
                          (u.1 ^ n *
                            (2 * (((2 * Real.pi)⁻¹ : ℝ) *
                              ∫ θ in 0..2 * Real.pi, Real.cos θ ^ (2 * n + 2)))) := by
                                ring
                    _ = p.coeff n *
                          (u.1 ^ n * northZonalScalarCoeff (2 * n + 2)) := by
                                rw [hcos]
                    _ = p.coeff n * (northZonalSqQuotientScalarCoeff n * u.1 ^ n) := by
                                simp [northZonalSqQuotientScalarCoeff, mul_assoc, mul_comm]
            _ = (northZonalSqQuotientScalarCoeff n * p.coeff n) * u.1 ^ n := by ring
