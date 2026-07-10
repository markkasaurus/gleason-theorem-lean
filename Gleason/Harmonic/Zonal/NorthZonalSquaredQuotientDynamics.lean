import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientOperator

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

@[simp] lemma northZonalSqQuotientAverage_const (c : ℝ) :
    northZonalSqQuotientAverage (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
  ext u
  rw [northZonalSqQuotientAverage_apply]
  have hcosSqInt : ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 = Real.pi := by
    rw [integral_cos_sq]
    simp
  have hconst :
      (fun θ : ℝ =>
        Real.cos θ ^ 2 * (ContinuousMap.const unitIcc c) (sqMulCosSelfMap θ u)) =
        (fun θ : ℝ => Real.cos θ ^ 2 * c) := by
    funext θ
    simp
  rw [hconst]
  rw [intervalIntegral.integral_mul_const, hcosSqInt]
  field_simp [Real.pi_ne_zero]
  simp

@[simp] lemma northZonalSqQuotientScalarCoeff_one :
    northZonalSqQuotientScalarCoeff 1 = (3 / 4 : ℝ) := by
  rw [northZonalSqQuotientScalarCoeff]
  rw [show 2 * 1 + 2 = 2 * 1 + 2 by norm_num, northZonalScalarCoeff_even_succ]
  rw [northZonalScalarCoeff_two]
  norm_num

lemma northZonalSqQuotientScalarCoeff_succ (n : ℕ) :
    northZonalSqQuotientScalarCoeff (n + 1) =
      (((2 * n + 3 : ℕ) : ℝ) / (((2 * n + 4 : ℕ) : ℝ))) *
        northZonalSqQuotientScalarCoeff n := by
  simpa [northZonalSqQuotientScalarCoeff, two_mul, add_assoc, add_left_comm, add_comm] using
    northZonalScalarCoeff_even_succ (n + 1)

lemma northZonalSqQuotientScalarCoeff_le_three_quarters {n : ℕ} (hn : 0 < n) :
    northZonalSqQuotientScalarCoeff n ≤ (3 / 4 : ℝ) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨k, rfl⟩
  induction k with
  | zero =>
      simp [northZonalSqQuotientScalarCoeff_one]
  | succ k hk =>
      rw [northZonalSqQuotientScalarCoeff_succ]
      have hk' : northZonalSqQuotientScalarCoeff (k + 1) ≤ (3 / 4 : ℝ) := by
        exact hk (Nat.succ_pos _)
      have hfac_nonneg :
          0 ≤ (((2 * (k + 1) + 3 : ℕ) : ℝ) / (((2 * (k + 1) + 4 : ℕ) : ℝ))) := by
        positivity
      have hfac_le_one :
          (((2 * (k + 1) + 3 : ℕ) : ℝ) / (((2 * (k + 1) + 4 : ℕ) : ℝ))) ≤ 1 := by
        have hden : (0 : ℝ) < (((2 * (k + 1) + 4 : ℕ) : ℝ)) := by positivity
        have hnum :
            (((2 * (k + 1) + 3 : ℕ) : ℝ)) ≤ (((2 * (k + 1) + 4 : ℕ) : ℝ)) := by
          norm_num
        exact (div_le_one hden).2 hnum
      calc
        (((2 * (k + 1) + 3 : ℕ) : ℝ) / (((2 * (k + 1) + 4 : ℕ) : ℝ))) *
            northZonalSqQuotientScalarCoeff (k + 1)
          ≤ 1 * northZonalSqQuotientScalarCoeff (k + 1) := by
              gcongr
              exact northZonalSqQuotientScalarCoeff_nonneg (k + 1)
        _ ≤ (3 / 4 : ℝ) := by simpa using hk'

lemma coeff_iter_northZonalSqQuotientPolynomial
    (p : ℝ[X]) (m n : ℕ) :
    ((northZonalSqQuotientPolynomial^[m]) p).coeff n =
      northZonalSqQuotientScalarCoeff n ^ m * p.coeff n := by
  induction m generalizing p with
  | zero =>
      simp
  | succ m hm =>
      rw [Function.iterate_succ_apply', coeff_northZonalSqQuotientPolynomial, hm]
      ring

lemma northZonalSqQuotientAverage_sub
    (f g : C(unitIcc, ℝ)) :
    northZonalSqQuotientAverage (f - g) =
      northZonalSqQuotientAverage f - northZonalSqQuotientAverage g := by
  ext u
  rw [northZonalSqQuotientAverage_apply, ContinuousMap.sub_apply,
    northZonalSqQuotientAverage_apply, northZonalSqQuotientAverage_apply]
  have hf :
      IntervalIntegrable
        (fun θ : ℝ => Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u))
        volume 0 (2 * Real.pi) := by
    have hcont :
        Continuous (fun θ : ℝ => Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u)) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  have hg :
      IntervalIntegrable
        (fun θ : ℝ => Real.cos θ ^ 2 * g (sqMulCosSelfMap θ u))
        volume 0 (2 * Real.pi) := by
    have hcont :
        Continuous (fun θ : ℝ => Real.cos θ ^ 2 * g (sqMulCosSelfMap θ u)) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  have hsub :
      (fun θ : ℝ => Real.cos θ ^ 2 * (f - g) (sqMulCosSelfMap θ u)) =
        (fun θ : ℝ =>
          Real.cos θ ^ 2 * f (sqMulCosSelfMap θ u) -
            Real.cos θ ^ 2 * g (sqMulCosSelfMap θ u)) := by
    funext θ
    simp
    ring
  rw [hsub, intervalIntegral.integral_sub hf hg]
  ring

theorem dist_northZonalSqQuotientAverage_le
    (f g : C(unitIcc, ℝ)) :
    dist (northZonalSqQuotientAverage f) (northZonalSqQuotientAverage g) ≤ dist f g := by
  simpa [dist_eq_norm, northZonalSqQuotientAverage_sub] using
    norm_northZonalSqQuotientAverage_le (f - g)
