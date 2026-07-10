import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientFixedPolynomial
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section
set_option maxHeartbeats 400000

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

def zeroUnitIcc : unitIcc := ⟨0, by constructor <;> norm_num⟩

def polyTailAbsSum (p : ℝ[X]) : ℝ :=
  Finset.sum (p.support.erase 0) fun n => |p.coeff n|

lemma norm_toContinuousMapOn_sub_const_le_polyTailAbsSum
    (p : ℝ[X]) :
    ‖p.toContinuousMapOn (Set.Icc (0 : ℝ) 1) - ContinuousMap.const _ (p.coeff 0)‖
      ≤ polyTailAbsSum p := by
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := p.toContinuousMapOn (Set.Icc (0 : ℝ) 1) - ContinuousMap.const _ (p.coeff 0))
    (M := polyTailAbsSum p)).2 ?_
  intro u
  rw [ContinuousMap.sub_apply, ContinuousMap.const_apply]
  rw [Real.norm_eq_abs]
  have huabs : |u.1| ≤ 1 := by
    simpa [abs_of_nonneg u.2.1] using u.2.2
  have hsplit :
      p.eval u.1 - p.coeff 0 =
        Finset.sum (p.support.erase 0) fun n => p.coeff n * u.1 ^ n := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    by_cases h0 : 0 ∈ p.support
    · rw [Finset.sum_eq_add_sum_diff_singleton h0]
      simp [Finset.sdiff_singleton_eq_erase]
    · have hp0 : p.coeff 0 = 0 := notMem_support_iff.mp h0
      simp [h0, hp0]
  simp [hsplit, polyTailAbsSum]
  calc
    |Finset.sum (p.support.erase 0) (fun n => p.coeff n * u.1 ^ n)|
      ≤ Finset.sum (p.support.erase 0) (fun n => |p.coeff n * u.1 ^ n|) := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (p.support.erase 0) (fun n => |p.coeff n|) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          calc
            |p.coeff n * u.1 ^ n| = |p.coeff n| * |u.1 ^ n| := by rw [abs_mul]
            _ ≤ |p.coeff n| * 1 := by
                  gcongr
                  rw [abs_pow]
                  exact pow_le_one₀ (abs_nonneg u.1) huabs
            _ = |p.coeff n| := by ring

lemma iterate_northZonalSqQuotientAverage_toContinuousMapOn
    (p : ℝ[X]) (m : ℕ) :
    (northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn (Set.Icc (0 : ℝ) 1)) =
      ((northZonalSqQuotientPolynomial^[m]) p).toContinuousMapOn (Set.Icc (0 : ℝ) 1) := by
  induction m generalizing p with
  | zero =>
      simp
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hm,
        northZonalSqQuotientAverage_toContinuousMapOn]

lemma support_iter_northZonalSqQuotientPolynomial_subset
    (p : ℝ[X]) (m : ℕ) :
    ((northZonalSqQuotientPolynomial^[m]) p).support ⊆ p.support := by
  intro n hn
  by_contra hp
  have hp0 : p.coeff n = 0 := notMem_support_iff.mp hp
  have hcoeff := coeff_iter_northZonalSqQuotientPolynomial p m n
  have hiter : ((northZonalSqQuotientPolynomial^[m]) p).coeff n = 0 := by
    simpa [hp0] using hcoeff
  exact (notMem_support_iff.mpr hiter) hn

lemma polyTailAbsSum_iterate_le
    (p : ℝ[X]) (m : ℕ) :
    polyTailAbsSum ((northZonalSqQuotientPolynomial^[m]) p)
      ≤ (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
  classical
  unfold polyTailAbsSum
  have hsubset :
      (((northZonalSqQuotientPolynomial^[m]) p).support.erase 0) ⊆ p.support.erase 0 := by
    intro n hn
    rcases Finset.mem_erase.mp hn with ⟨hn0, hns⟩
    refine Finset.mem_erase.mpr ⟨hn0, support_iter_northZonalSqQuotientPolynomial_subset p m hns⟩
  calc
    Finset.sum (((northZonalSqQuotientPolynomial^[m]) p).support.erase 0)
        (fun n => |((northZonalSqQuotientPolynomial^[m]) p).coeff n|)
      ≤ Finset.sum (((northZonalSqQuotientPolynomial^[m]) p).support.erase 0)
          (fun n => (3 / 4 : ℝ) ^ m * |p.coeff n|) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            rcases Finset.mem_erase.mp hn with ⟨hn0, _⟩
            have hnpos : 0 < n := Nat.pos_iff_ne_zero.mpr hn0
            calc
              |((northZonalSqQuotientPolynomial^[m]) p).coeff n|
                = |northZonalSqQuotientScalarCoeff n ^ m * p.coeff n| := by
                    rw [coeff_iter_northZonalSqQuotientPolynomial]
              _ = northZonalSqQuotientScalarCoeff n ^ m * |p.coeff n| := by
                    rw [abs_mul, abs_of_nonneg (pow_nonneg (northZonalSqQuotientScalarCoeff_nonneg n) _)]
              _ ≤ (3 / 4 : ℝ) ^ m * |p.coeff n| := by
                    have hpow :
                        northZonalSqQuotientScalarCoeff n ^ m ≤ (3 / 4 : ℝ) ^ m := by
                      exact pow_le_pow_left₀
                        (northZonalSqQuotientScalarCoeff_nonneg n)
                        (northZonalSqQuotientScalarCoeff_le_three_quarters hnpos)
                        m
                    gcongr
    _ ≤ Finset.sum (p.support.erase 0) (fun n => (3 / 4 : ℝ) ^ m * |p.coeff n|) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro n hn1 hn2; positivity)
    _ = (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
          simp [polyTailAbsSum, Finset.mul_sum]

lemma norm_iterate_northZonalSqQuotientAverage_polynomial_sub_const_le
    (p : ℝ[X]) (m : ℕ) :
    ‖(northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn (Set.Icc (0 : ℝ) 1))
        - ContinuousMap.const _ (p.coeff 0)‖
      ≤ (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
  let q : ℝ[X] := (northZonalSqQuotientPolynomial^[m]) p
  rw [iterate_northZonalSqQuotientAverage_toContinuousMapOn]
  have hq0 : q.coeff 0 = p.coeff 0 := by
    simp [q, coeff_iter_northZonalSqQuotientPolynomial]
  have hnorm : ‖q.toContinuousMapOn (Set.Icc (0 : ℝ) 1) - ContinuousMap.const _ (q.coeff 0)‖
      ≤ polyTailAbsSum q :=
    norm_toContinuousMapOn_sub_const_le_polyTailAbsSum q
  rw [hq0] at hnorm
  exact hnorm.trans (polyTailAbsSum_iterate_le p m)

lemma dist_iterate_northZonalSqQuotientAverage_le
    (f g : C(unitIcc, ℝ)) (m : ℕ) :
    dist ((northZonalSqQuotientAverage^[m]) f) ((northZonalSqQuotientAverage^[m]) g) ≤ dist f g := by
  induction m generalizing f g with
  | zero =>
      simp
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (dist_northZonalSqQuotientAverage_le _ _).trans (hm _ _)

theorem northZonalSqQuotientAverage_eq_const_of_fixed
    (f : C(unitIcc, ℝ))
    (hfix : northZonalSqQuotientAverage f = f) :
    f = ContinuousMap.const _ (f zeroUnitIcc) := by
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  let c : C(unitIcc, ℝ) := ContinuousMap.const _ (f zeroUnitIcc)
  by_contra hne
  have hdpos : 0 < dist f c := by
    exact dist_pos.mpr hne
  let ε : ℝ := dist f c / 4
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f ε hε
  let pMap : C(unitIcc, ℝ) := p.toContinuousMapOn (Set.Icc (0 : ℝ) 1)
  have hpf : dist pMap f < ε := by
    simpa [pMap, dist_eq_norm] using hp
  have hfp : dist f pMap < ε := by
    simpa [dist_comm] using hpf
  let A : ℝ := polyTailAbsSum p + 1
  have hA : 0 < A := by
    have hnonneg : 0 ≤ polyTailAbsSum p := by
      unfold polyTailAbsSum
      exact Finset.sum_nonneg (by intro n hn; exact abs_nonneg _)
    dsimp [A]
    linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε / A by positivity)
    (by norm_num : (3 / 4 : ℝ) < 1)
  have hiter_fix : (northZonalSqQuotientAverage^[m]) f = f := by
    simpa using Function.iterate_fixed hfix m
  have htail : (3 / 4 : ℝ) ^ m * polyTailAbsSum p < ε := by
    have hAstep : (3 / 4 : ℝ) ^ m * A < ε := by
      have hmul := mul_lt_mul_of_pos_right hm hA
      have hdivmul : (ε / A) * A = ε := by
        field_simp [ne_of_gt hA]
      calc
        (3 / 4 : ℝ) ^ m * A < (ε / A) * A := hmul
        _ = ε := hdivmul
    have hAle : polyTailAbsSum p ≤ A := by
      dsimp [A]
      linarith
    exact lt_of_le_of_lt (by gcongr) hAstep
  have hpoly :
      dist ((northZonalSqQuotientAverage^[m]) pMap) (ContinuousMap.const _ (p.coeff 0)) < ε := by
    have hnorm :=
      norm_iterate_northZonalSqQuotientAverage_polynomial_sub_const_le p m
    exact lt_of_le_of_lt (by simpa [dist_eq_norm, pMap] using hnorm) htail
  have hfirst :
      dist f ((northZonalSqQuotientAverage^[m]) pMap) < ε := by
    have hle :
        dist ((northZonalSqQuotientAverage^[m]) f)
          ((northZonalSqQuotientAverage^[m]) pMap) ≤ dist f pMap :=
      dist_iterate_northZonalSqQuotientAverage_le f pMap m
    exact lt_of_le_of_lt (by simpa [hiter_fix] using hle) hfp
  have hp0eval : p.coeff 0 = pMap zeroUnitIcc := by
    change p.coeff 0 = p.eval 0
    simpa using p.coeff_zero_eq_eval_zero
  have hconstle :
      dist (ContinuousMap.const _ (p.coeff 0)) c ≤
        dist (p.coeff 0) (f zeroUnitIcc) := by
    haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
    rw [dist_eq_norm, dist_eq_norm]
    refine (ContinuousMap.norm_le_of_nonempty
      (f := ContinuousMap.const _ (p.coeff 0) - c)
      (M := ‖p.coeff 0 - f zeroUnitIcc‖)).2 ?_
    intro x
    simp [c]
  have hpointle :
      dist (p.coeff 0) (f zeroUnitIcc) ≤ dist pMap f := by
    rw [hp0eval]
    exact ContinuousMap.dist_apply_le_dist (f := pMap) (g := f) zeroUnitIcc
  have hthird_le :
      dist (ContinuousMap.const _ (p.coeff 0)) c ≤ dist pMap f := by
    exact hconstle.trans hpointle
  have hthird :
      dist (ContinuousMap.const _ (p.coeff 0)) c < ε := by
    exact lt_of_le_of_lt hthird_le hpf
  have htri1 :=
    dist_triangle f ((northZonalSqQuotientAverage^[m]) pMap) c
  have htri2 :=
    dist_triangle ((northZonalSqQuotientAverage^[m]) pMap) (ContinuousMap.const _ (p.coeff 0)) c
  have hsum : dist f c < 3 * ε := by
    nlinarith [htri1, htri2, hfirst, hpoly, hthird]
  have hstrict : 3 * ε < dist f c := by
    dsimp [ε]
    nlinarith [hdpos]
  exact (not_lt_of_ge hstrict.le) hsum
