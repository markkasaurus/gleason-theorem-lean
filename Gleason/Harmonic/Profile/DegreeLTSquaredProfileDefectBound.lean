import Gleason.Harmonic.Profile.DegreeLTSquaredProfileTailBound

noncomputable section

open Complex InnerProductSpace Polynomial

theorem sqProfileTailAbsSum_le_four_mul_sqProfileTailAbsSum_defect
    (p : ℝ[X]) :
    sqProfileTailAbsSum p ≤
      4 * sqProfileTailAbsSum (northZonalSqProfilePolynomial p - p) := by
  classical
  let d : ℝ[X] := northZonalSqProfilePolynomial p - p
  have hsubset :
      p.support.filter (fun n => 2 ≤ n) ⊆
        d.support.filter (fun n => 2 ≤ n) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hns, hn2⟩
    have hpcoeffnz : p.coeff n ≠ 0 := mem_support_iff.mp hns
    have hcoeff :
        d.coeff n = (northZonalScalarCoeff (2 * n) - 1) * p.coeff n := by
      simp [d, coeff_northZonalSqProfilePolynomial]
      ring
    have hlt : northZonalScalarCoeff (2 * n) < 1 := by
      rcases Nat.exists_eq_add_of_le hn2 with ⟨k, rfl⟩
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using
        northZonalScalarCoeff_even_gt_two_lt_one_aux k
    have hne : northZonalScalarCoeff (2 * n) - 1 ≠ 0 := by
      linarith
    have hdcoeffnz : d.coeff n ≠ 0 := by
      rw [hcoeff]
      exact mul_ne_zero hne hpcoeffnz
    exact Finset.mem_filter.mpr ⟨mem_support_iff.mpr hdcoeffnz, hn2⟩
  calc
    sqProfileTailAbsSum p
      = Finset.sum (p.support.filter fun n => 2 ≤ n) (fun n => |p.coeff n|) := by
          rfl
    _ ≤ Finset.sum (p.support.filter fun n => 2 ≤ n)
          (fun n => 4 * |d.coeff n|) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            have hn2 : 2 ≤ n := (Finset.mem_filter.mp hn).2
            have hcoeff :
                d.coeff n = (northZonalScalarCoeff (2 * n) - 1) * p.coeff n := by
              simp [d, coeff_northZonalSqProfilePolynomial]
              ring
            have hcoeffAbs :
                |d.coeff n| =
                  (1 - northZonalScalarCoeff (2 * n)) * |p.coeff n| := by
              rw [hcoeff, abs_mul, abs_of_nonpos]
              · ring
              · linarith [northZonalSqProfileScalarCoeff_le_three_quarters hn2]
            have hquarter :
                (1 / 4 : ℝ) ≤ 1 - northZonalScalarCoeff (2 * n) := by
              linarith [northZonalSqProfileScalarCoeff_le_three_quarters hn2]
            have hnonneg : 0 ≤ |p.coeff n| := abs_nonneg _
            have hmul :
                (1 / 4 : ℝ) * |p.coeff n| ≤ |d.coeff n| := by
              rw [hcoeffAbs]
              gcongr
            nlinarith
    _ ≤ Finset.sum (d.support.filter fun n => 2 ≤ n)
          (fun n => 4 * |d.coeff n|) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
            intro n hn1 hn2
            positivity
    _ = 4 * sqProfileTailAbsSum d := by
          simp [sqProfileTailAbsSum, Finset.mul_sum, d]

theorem norm_sqProfilePolynomialMap_sub_linear_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
    {N : ℕ} {p : ℝ[X]}
    (hpdeg : p ∈ Polynomial.degreeLT ℝ N)
    (hp0 : p.eval 0 = 0) :
    ‖sqProfilePolynomialMap p - sqProfileLinearPart p‖ ≤
      4 * degreeLTSqProfileTailBoundConst N * sqProfilePolynomialDefect p := by
  let d : ℝ[X] := northZonalSqProfilePolynomial p - p
  have hTdeg : northZonalSqProfilePolynomial p ∈ Polynomial.degreeLT ℝ N := by
    rw [Polynomial.mem_degreeLT]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro n hn
    have hpcoeff :
        p.coeff n = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hpdeg) n hn
    simp [coeff_northZonalSqProfilePolynomial, hpcoeff]
  have hddeg : d ∈ Polynomial.degreeLT ℝ N := by
    exact Submodule.sub_mem _ hTdeg hpdeg
  have htaild :
      sqProfileTailAbsSum d ≤
        degreeLTSqProfileTailBoundConst N * ‖d.toContinuousMapOn unitIcc‖ :=
    sqProfileTailAbsSum_le_degreeLTSqProfileTailBoundConst_mul_norm hddeg
  have hmapd :
      d.toContinuousMapOn unitIcc =
        northZonalSqProfileAverage (sqProfilePolynomialMap p) -
          sqProfilePolynomialMap p := by
    ext u
    simp [d, sqProfilePolynomialMap, northZonalSqProfileAverage_toContinuousMapOn]
  calc
    ‖sqProfilePolynomialMap p - sqProfileLinearPart p‖
      ≤ sqProfileTailAbsSum p := by
          simpa [sqProfilePolynomialMap, sqProfileLinearPart] using
            norm_toContinuousMapOn_sub_linear_le_sqProfileTailAbsSum p hp0
    _ ≤ 4 * sqProfileTailAbsSum d := sqProfileTailAbsSum_le_four_mul_sqProfileTailAbsSum_defect p
    _ ≤ 4 * (degreeLTSqProfileTailBoundConst N * ‖d.toContinuousMapOn unitIcc‖) := by
          gcongr
    _ = 4 * degreeLTSqProfileTailBoundConst N * sqProfilePolynomialDefect p := by
          rw [hmapd]
          simp [sqProfilePolynomialDefect, dist_eq_norm, mul_assoc]

theorem sqProfileTailAbsSum_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
    {N : ℕ} {p : ℝ[X]}
    (hpdeg : p ∈ Polynomial.degreeLT ℝ N) :
    sqProfileTailAbsSum p ≤
      4 * degreeLTSqProfileTailBoundConst N * sqProfilePolynomialDefect p := by
  let d : ℝ[X] := northZonalSqProfilePolynomial p - p
  have hTdeg : northZonalSqProfilePolynomial p ∈ Polynomial.degreeLT ℝ N := by
    rw [Polynomial.mem_degreeLT]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro n hn
    have hpcoeff :
        p.coeff n = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hpdeg) n hn
    simp [coeff_northZonalSqProfilePolynomial, hpcoeff]
  have hddeg : d ∈ Polynomial.degreeLT ℝ N := by
    exact Submodule.sub_mem _ hTdeg hpdeg
  have htaild :
      sqProfileTailAbsSum d ≤
        degreeLTSqProfileTailBoundConst N * ‖d.toContinuousMapOn unitIcc‖ :=
    sqProfileTailAbsSum_le_degreeLTSqProfileTailBoundConst_mul_norm hddeg
  have hmapd :
      d.toContinuousMapOn unitIcc =
        northZonalSqProfileAverage (sqProfilePolynomialMap p) -
          sqProfilePolynomialMap p := by
    ext u
    simp [d, sqProfilePolynomialMap, northZonalSqProfileAverage_toContinuousMapOn]
  calc
    sqProfileTailAbsSum p
      ≤ 4 * sqProfileTailAbsSum d := sqProfileTailAbsSum_le_four_mul_sqProfileTailAbsSum_defect p
    _ ≤ 4 * (degreeLTSqProfileTailBoundConst N * ‖d.toContinuousMapOn unitIcc‖) := by
          gcongr
    _ = 4 * degreeLTSqProfileTailBoundConst N * sqProfilePolynomialDefect p := by
          rw [hmapd]
          simp [sqProfilePolynomialDefect, dist_eq_norm, mul_assoc]

theorem norm_sqProfilePolynomialMap_X_mul_sub_linear_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
    {N : ℕ} {q : ℝ[X]}
    (hqdeg : q ∈ Polynomial.degreeLT ℝ N) :
    ‖sqProfilePolynomialMap (X * q) - sqProfileLinearPart (X * q)‖ ≤
      4 * degreeLTSqProfileTailBoundConst (N + 1) * sqProfilePolynomialDefect (X * q) := by
  refine
    norm_sqProfilePolynomialMap_sub_linear_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
      (N := N + 1) ?_ ?_
  · rw [Polynomial.mem_degreeLT]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro n hn
    by_cases h0 : n = 0
    · subst h0
      simp
    · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨m, rfl⟩
      have hm : N ≤ m := by omega
      have hzero : q.coeff m = 0 := by
        exact (Polynomial.degree_lt_iff_coeff_zero _ _).1
          ((Polynomial.mem_degreeLT).1 hqdeg) m hm
      rw [Polynomial.coeff_X_mul, hzero]
  · simp

theorem sqProfileTailAbsSum_X_mul_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
    {N : ℕ} {q : ℝ[X]}
    (hqdeg : q ∈ Polynomial.degreeLT ℝ N) :
    sqProfileTailAbsSum (X * q) ≤
      4 * degreeLTSqProfileTailBoundConst (N + 1) * sqProfilePolynomialDefect (X * q) := by
  refine
    sqProfileTailAbsSum_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
      (N := N + 1) ?_
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
  intro n hn
  by_cases h0 : n = 0
  · subst h0
    simp
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨m, rfl⟩
    have hm : N ≤ m := by omega
    have hzero : q.coeff m = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1
        ((Polynomial.mem_degreeLT).1 hqdeg) m hm
    rw [Polynomial.coeff_X_mul, hzero]
