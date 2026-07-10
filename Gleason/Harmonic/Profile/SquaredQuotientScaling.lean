import Gleason.Harmonic.Profile.SquaredProfileScaling
import Gleason.Harmonic.Profile.SquaredProfileScalingPoly
import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientAlmostFixedContinuous

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

def sqScaleContinuous (a : unitIcc) : C(unitIcc, unitIcc) :=
  ⟨sqScaleMap a,
    Continuous.subtype_mk
      (by
        simpa [sqScaleMap] using
          ((continuous_const : Continuous fun _ : unitIcc => a.1).mul continuous_subtype_val))
      (fun u => (sqScaleMap a u).2)⟩

def sqQuotientRescale (a : unitIcc) (f : C(unitIcc, ℝ)) : C(unitIcc, ℝ) :=
  f.comp (sqScaleContinuous a)

@[simp] theorem sqQuotientRescale_apply (a : unitIcc) (f : C(unitIcc, ℝ)) (u : unitIcc) :
    sqQuotientRescale a f u = f (sqScaleMap a u) := by
  rfl

lemma northZonalSqQuotientAverage_sqQuotientRescale
    (a : unitIcc) (f : C(unitIcc, ℝ)) :
    northZonalSqQuotientAverage (sqQuotientRescale a f) =
      sqQuotientRescale a (northZonalSqQuotientAverage f) := by
  ext u
  rw [northZonalSqQuotientAverage_apply, sqQuotientRescale_apply, northZonalSqQuotientAverage_apply]
  congr 2
  apply intervalIntegral.integral_congr_ae
  filter_upwards with θ
  simp [sqQuotientRescale_apply, sqScaleMap_sqMulCosSelfMap]

theorem sqQuotientRescale_fixed
    (a : unitIcc) {f : C(unitIcc, ℝ)}
    (hfix : northZonalSqQuotientAverage f = f) :
    northZonalSqQuotientAverage (sqQuotientRescale a f) = sqQuotientRescale a f := by
  rw [northZonalSqQuotientAverage_sqQuotientRescale, hfix]

theorem sqQuotientRescale_const
    (a : unitIcc) (c : ℝ) :
    sqQuotientRescale a (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
  ext u
  simp [sqQuotientRescale_apply]

theorem dist_sqQuotientRescale_le
    (a : unitIcc) (f g : C(unitIcc, ℝ)) :
    dist (sqQuotientRescale a f) (sqQuotientRescale a g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := sqQuotientRescale a f - sqQuotientRescale a g)
    (M := ‖f - g‖)).2 ?_
  intro u
  rw [ContinuousMap.sub_apply, sqQuotientRescale_apply, sqQuotientRescale_apply, Real.norm_eq_abs]
  simpa [ContinuousMap.sub_apply, Real.norm_eq_abs] using
    (f - g).norm_coe_le_norm (sqScaleMap a u)

theorem sqQuotientRescalePolynomial_toContinuousMapOn
    (a : unitIcc) (q : ℝ[X]) :
    (sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc =
      sqQuotientRescale a (q.toContinuousMapOn unitIcc) := by
  ext u
  simp [sqQuotientRescale_apply, sqQuotientRescalePolynomial_eval]

theorem northZonalSqQuotientAverage_sqQuotientRescalePolynomial_toContinuousMapOn
    (a : unitIcc) (q : ℝ[X]) :
    northZonalSqQuotientAverage
        ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc) =
      (sqQuotientRescalePolynomial a (northZonalSqQuotientPolynomial q)).toContinuousMapOn unitIcc := by
  rw [sqQuotientRescalePolynomial_toContinuousMapOn, northZonalSqQuotientAverage_sqQuotientRescale,
    northZonalSqQuotientAverage_toContinuousMapOn, sqQuotientRescalePolynomial_toContinuousMapOn]

theorem dist_sqQuotientRescalePolynomial_iterate_const_le
    (a : unitIcc) (q : ℝ[X]) (m : ℕ) :
    dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
        (ContinuousMap.const _ (q.coeff 0))
      ≤ (3 / 4 : ℝ) ^ m * polyTailAbsSum (sqQuotientRescalePolynomial a q) +
          dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
            ((northZonalSqQuotientAverage^[m])
              ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)) := by
  calc
    dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
        (ContinuousMap.const _ (q.coeff 0))
      ≤ dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
          ((northZonalSqQuotientAverage^[m])
            ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)) +
        dist ((northZonalSqQuotientAverage^[m])
            ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc))
          (ContinuousMap.const _ (q.coeff 0)) := by
            exact dist_triangle _ _ _
    _ ≤ dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
          ((northZonalSqQuotientAverage^[m])
            ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)) +
        (3 / 4 : ℝ) ^ m * polyTailAbsSum (sqQuotientRescalePolynomial a q) := by
            gcongr
            simpa [dist_eq_norm] using
              norm_iterate_northZonalSqQuotientAverage_polynomial_sub_const_le
                (sqQuotientRescalePolynomial a q) m
    _ = (3 / 4 : ℝ) ^ m * polyTailAbsSum (sqQuotientRescalePolynomial a q) +
        dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
          ((northZonalSqQuotientAverage^[m])
            ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)) := by
            ring

theorem polyTailAbsSum_sqQuotientRescalePolynomial_le
    (a : unitIcc) (q : ℝ[X]) :
    polyTailAbsSum (sqQuotientRescalePolynomial a q) ≤ a.1 * polyTailAbsSum q := by
  classical
  unfold polyTailAbsSum
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
    _ = a.1 * polyTailAbsSum q := by
          simp [polyTailAbsSum, Finset.mul_sum]

theorem dist_sqQuotientRescalePolynomial_const_le_of_almost_fixed
    (a : unitIcc) (q : ℝ[X]) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (halmost :
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
        (q.toContinuousMapOn unitIcc) ≤ δ)
    (m : ℕ) :
    dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
        (ContinuousMap.const _ (q.coeff 0))
      ≤
        (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
          (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q) := by
  have hcoeff0 :
      (sqQuotientRescalePolynomial a q).coeff 0 = q.coeff 0 := by
    simp
  have halmostRescaled :
      dist
          (northZonalSqQuotientAverage
            ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc))
          ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
        ≤ δ := by
    rw [sqQuotientRescalePolynomial_toContinuousMapOn]
    change dist
        (northZonalSqQuotientAverage (sqQuotientRescale a (q.toContinuousMapOn unitIcc)))
        (sqQuotientRescale a (q.toContinuousMapOn unitIcc))
      ≤ δ
    rw [northZonalSqQuotientAverage_sqQuotientRescale]
    calc
      dist (sqQuotientRescale a (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc)))
            (sqQuotientRescale a (q.toContinuousMapOn unitIcc))
        ≤ dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
            (q.toContinuousMapOn unitIcc) :=
          dist_sqQuotientRescale_le a
            (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
            (q.toContinuousMapOn unitIcc)
      _ ≤ δ := halmost
  calc
    dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
        (ContinuousMap.const _ (q.coeff 0))
      = dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
          (ContinuousMap.const _ ((sqQuotientRescalePolynomial a q).coeff 0)) := by
            simp [hcoeff0]
    _ ≤
        (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
          (3 / 4 : ℝ) ^ m * polyTailAbsSum (sqQuotientRescalePolynomial a q) :=
        northZonalSqQuotientPolynomial_near_const_of_almost_fixed_iterate
          (sqQuotientRescalePolynomial a q) hδ halmostRescaled m
    _ ≤
        (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
          (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q) := by
            gcongr
            exact polyTailAbsSum_sqQuotientRescalePolynomial_le a q

theorem abs_sqQuotientRescalePolynomial_eval_sub_eval_le_of_almost_fixed
    (a : unitIcc) (q : ℝ[X]) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (halmost :
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
        (q.toContinuousMapOn unitIcc) ≤ δ)
    (m : ℕ) (u v : unitIcc) :
    |(sqQuotientRescalePolynomial a q).eval u.1 -
        (sqQuotientRescalePolynomial a q).eval v.1|
      ≤
        2 *
          ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
            (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
  have hconst :
      dist ((sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
          (ContinuousMap.const _ (q.coeff 0))
        ≤
          (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
            (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q) :=
    dist_sqQuotientRescalePolynomial_const_le_of_almost_fixed a q hδ halmost m
  have hu :
      |(sqQuotientRescalePolynomial a q).eval u.1 - q.coeff 0|
        ≤
          (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
            (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q) := by
    have hpt :=
      ContinuousMap.dist_apply_le_dist
        (f := (sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
        (g := ContinuousMap.const _ (q.coeff 0)) u
    simpa [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs] using hpt.trans hconst
  have hv :
      |(sqQuotientRescalePolynomial a q).eval v.1 - q.coeff 0|
        ≤
          (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
            (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q) := by
    have hpt :=
      ContinuousMap.dist_apply_le_dist
        (f := (sqQuotientRescalePolynomial a q).toContinuousMapOn unitIcc)
        (g := ContinuousMap.const _ (q.coeff 0)) v
    simpa [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs] using hpt.trans hconst
  calc
    |(sqQuotientRescalePolynomial a q).eval u.1 -
        (sqQuotientRescalePolynomial a q).eval v.1|
      ≤ |(sqQuotientRescalePolynomial a q).eval u.1 - q.coeff 0| +
          |(sqQuotientRescalePolynomial a q).eval v.1 - q.coeff 0| := by
            have htri :=
              abs_sub_le ((sqQuotientRescalePolynomial a q).eval u.1) (q.coeff 0)
                ((sqQuotientRescalePolynomial a q).eval v.1)
            calc
              |(sqQuotientRescalePolynomial a q).eval u.1 -
                  (sqQuotientRescalePolynomial a q).eval v.1|
                ≤ |(sqQuotientRescalePolynomial a q).eval u.1 - q.coeff 0| +
                    |q.coeff 0 - (sqQuotientRescalePolynomial a q).eval v.1| := by
                      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htri
              _ =
                  |(sqQuotientRescalePolynomial a q).eval u.1 - q.coeff 0| +
                    |(sqQuotientRescalePolynomial a q).eval v.1 - q.coeff 0| := by
                      congr 1
                      exact abs_sub_comm _ _
    _ ≤
        ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
          (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) +
        ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
          (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
            gcongr
    _ = 2 *
        ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
          (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
            ring
