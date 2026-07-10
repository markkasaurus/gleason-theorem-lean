import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileFixedPolynomial

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

@[simp] lemma northZonalSqProfileScalarCoeff_one :
    northZonalScalarCoeff 2 = (1 : ℝ) := by
  simpa using northZonalScalarCoeff_two

lemma northZonalSqProfileScalarCoeff_succ (n : ℕ) :
    northZonalScalarCoeff (2 * (n + 1)) =
      (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ) : ℝ))) *
        northZonalScalarCoeff (2 * n) := by
  simpa [two_mul, add_assoc, add_left_comm, add_comm] using
    northZonalScalarCoeff_even_succ n

lemma northZonalSqProfileScalarCoeff_le_three_quarters {n : ℕ} (hn : 2 ≤ n) :
    northZonalScalarCoeff (2 * n) ≤ (3 / 4 : ℝ) := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  induction k with
  | zero =>
      calc
        northZonalScalarCoeff (2 * (2 + 0))
          = northZonalScalarCoeff 4 := by norm_num
        _ = (3 / 4 : ℝ) := by
              rw [show 4 = 2 * (1 + 1) by norm_num, northZonalSqProfileScalarCoeff_succ,
                northZonalScalarCoeff_two]
              norm_num
        _ ≤ (3 / 4 : ℝ) := le_rfl
  | succ k hk =>
      rw [show 2 * (2 + (k + 1)) = 2 * ((k + 2) + 1) by ring_nf,
        northZonalSqProfileScalarCoeff_succ]
      have hk' : northZonalScalarCoeff (2 * (k + 2)) ≤ (3 / 4 : ℝ) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hk (by omega)
      have hfac_nonneg :
          0 ≤ (((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ))) := by
        positivity
      have hfac_le_one :
          (((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ))) ≤ 1 := by
        have hden : (0 : ℝ) < (((2 * (k + 2) + 2 : ℕ) : ℝ)) := by positivity
        have hnum :
            (((2 * (k + 2) + 1 : ℕ) : ℝ)) ≤ (((2 * (k + 2) + 2 : ℕ) : ℝ)) := by
          norm_num
        exact (div_le_one hden).2 hnum
      calc
        (((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ))) *
            northZonalScalarCoeff (2 * (k + 2))
          ≤ 1 * northZonalScalarCoeff (2 * (k + 2)) := by
              gcongr
              exact northZonalScalarCoeff_even_pos (k + 2) |>.le
        _ ≤ (3 / 4 : ℝ) := by simpa using hk'

lemma coeff_iter_northZonalSqProfilePolynomial
    (p : ℝ[X]) (m n : ℕ) :
    ((northZonalSqProfilePolynomial^[m]) p).coeff n =
      northZonalScalarCoeff (2 * n) ^ m * p.coeff n := by
  induction m generalizing p with
  | zero =>
      simp
  | succ m hm =>
      rw [Function.iterate_succ_apply', coeff_northZonalSqProfilePolynomial, hm]
      ring

def sqProfileTailAbsSum (p : ℝ[X]) : ℝ :=
  Finset.sum (p.support.filter fun n => 2 ≤ n) fun n => |p.coeff n|

def sqProfilePolynomialMap (p : ℝ[X]) : C(unitIcc, ℝ) :=
  p.toContinuousMapOn unitIcc

def sqProfileLinearPart (p : ℝ[X]) : C(unitIcc, ℝ) :=
  (C (p.coeff 1) * X).toContinuousMapOn unitIcc

def sqProfilePolynomialDefect (p : ℝ[X]) : ℝ :=
  dist (northZonalSqProfileAverage (sqProfilePolynomialMap p)) (sqProfilePolynomialMap p)

set_option maxHeartbeats 800000 in
lemma norm_toContinuousMapOn_sub_linear_le_sqProfileTailAbsSum
    (p : ℝ[X]) (hp0 : p.eval 0 = 0) :
    ‖p.toContinuousMapOn (Set.Icc (0 : ℝ) 1) - (C (p.coeff 1) * X).toContinuousMapOn (Set.Icc (0 : ℝ) 1)‖
      ≤ sqProfileTailAbsSum p := by
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := p.toContinuousMapOn (Set.Icc (0 : ℝ) 1) -
      (C (p.coeff 1) * X).toContinuousMapOn (Set.Icc (0 : ℝ) 1))
    (M := sqProfileTailAbsSum p)).2 ?_
  intro u
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  have huabs : |u.1| ≤ 1 := by
    simpa [abs_of_nonneg u.2.1] using u.2.2
  have hpcoeff0 : p.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
  have hsplit :
      p.eval u.1 - (C (p.coeff 1) * X : ℝ[X]).eval u.1 =
        Finset.sum (p.support.filter fun n => 2 ≤ n) fun n => p.coeff n * u.1 ^ n := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [show (C (p.coeff 1) * X : ℝ[X]).eval u.1 = p.coeff 1 * u.1 by simp]
    classical
    have hsum_split :
        Finset.sum p.support (fun x => p.coeff x * u.1 ^ x) =
          Finset.sum (p.support.filter fun x => 2 ≤ x) (fun x => p.coeff x * u.1 ^ x) +
          Finset.sum (p.support.filter fun x => ¬ 2 ≤ x) (fun x => p.coeff x * u.1 ^ x) := by
      symm
      exact Finset.sum_filter_add_sum_filter_not p.support (fun x => 2 ≤ x)
        (fun x => p.coeff x * u.1 ^ x)
    have hlow :
        Finset.sum (p.support.filter fun x => ¬ 2 ≤ x) (fun x => p.coeff x * u.1 ^ x) =
          p.coeff 0 * u.1 ^ 0 + p.coeff 1 * u.1 ^ 1 := by
      have h01 :
          p.support.filter (fun x => ¬ 2 ≤ x) = p.support.filter (fun x => x = 0 ∨ x = 1) := by
        apply Finset.ext
        intro n
        simp
        omega
      rw [h01]
      have h0 : 0 ∉ p.support := by
        exact notMem_support_iff.mpr hpcoeff0
      by_cases h1 : 1 ∈ p.support
      · rw [show p.support.filter (fun x => x = 0 ∨ x = 1) = {1} by
            apply Finset.ext
            intro n
            constructor
            · intro hn
              rcases Finset.mem_filter.mp hn with ⟨hs, hn01⟩
              rcases hn01 with rfl | rfl
              · exact False.elim (h0 hs)
              · simp
            · intro hn
              rcases Finset.mem_singleton.mp hn with rfl
              exact Finset.mem_filter.mpr ⟨h1, Or.inr rfl⟩]
        simp [hpcoeff0]
      · rw [show p.support.filter (fun x => x = 0 ∨ x = 1) = ∅ by
            apply Finset.ext
            intro n
            constructor
            · intro hn
              rcases Finset.mem_filter.mp hn with ⟨hs, hn01⟩
              rcases hn01 with hzero | hone
              · exact False.elim (h0 (hzero ▸ hs))
              · exact False.elim (h1 (hone ▸ hs))
            · intro hn
              exact False.elim (Finset.notMem_empty n hn)]
        simp [hpcoeff0, notMem_support_iff.mp h1]
    calc
      Finset.sum p.support (fun n => p.coeff n * u.1 ^ n) - p.coeff 1 * u.1
        = Finset.sum (p.support.filter fun n => 2 ≤ n) (fun n => p.coeff n * u.1 ^ n) +
            (p.coeff 0 * u.1 ^ 0 + p.coeff 1 * u.1 ^ 1) - p.coeff 1 * u.1 := by
              rw [hsum_split, hlow]
      _ = Finset.sum (p.support.filter fun n => 2 ≤ n) (fun n => p.coeff n * u.1 ^ n) := by
            simp [hpcoeff0]
  change |p.eval u.1 - ((C (p.coeff 1) * X : ℝ[X]).eval u.1)| ≤ sqProfileTailAbsSum p
  rw [hsplit]
  simp [sqProfileTailAbsSum]
  calc
    |Finset.sum (p.support.filter fun n => 2 ≤ n) (fun n => p.coeff n * u.1 ^ n)|
      ≤ Finset.sum (p.support.filter fun n => 2 ≤ n) (fun n => |p.coeff n * u.1 ^ n|) := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum (p.support.filter fun n => 2 ≤ n) (fun n => |p.coeff n|) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          calc
            |p.coeff n * u.1 ^ n| = |p.coeff n| * |u.1 ^ n| := by rw [abs_mul]
            _ ≤ |p.coeff n| * 1 := by
                  gcongr
                  rw [abs_pow]
                  exact pow_le_one₀ (abs_nonneg u.1) huabs
            _ = |p.coeff n| := by ring

lemma sqProfileTailAbsSum_iterate_le
    (p : ℝ[X]) (m : ℕ) :
    sqProfileTailAbsSum ((northZonalSqProfilePolynomial^[m]) p)
      ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
  classical
  unfold sqProfileTailAbsSum
  calc
    Finset.sum (((northZonalSqProfilePolynomial^[m]) p).support.filter fun n => 2 ≤ n)
        (fun n => |((northZonalSqProfilePolynomial^[m]) p).coeff n|)
      ≤ Finset.sum (((northZonalSqProfilePolynomial^[m]) p).support.filter fun n => 2 ≤ n)
          (fun n => (3 / 4 : ℝ) ^ m * |p.coeff n|) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            have hn2 : 2 ≤ n := by
              exact (Finset.mem_filter.mp hn).2
            calc
              |((northZonalSqProfilePolynomial^[m]) p).coeff n|
                = |northZonalScalarCoeff (2 * n) ^ m * p.coeff n| := by
                    rw [coeff_iter_northZonalSqProfilePolynomial]
              _ = northZonalScalarCoeff (2 * n) ^ m * |p.coeff n| := by
                    rw [abs_mul, abs_of_nonneg (pow_nonneg (northZonalScalarCoeff_even_pos n |>.le) _)]
              _ ≤ (3 / 4 : ℝ) ^ m * |p.coeff n| := by
                    have hpow :
                        northZonalScalarCoeff (2 * n) ^ m ≤ (3 / 4 : ℝ) ^ m := by
                      exact pow_le_pow_left₀
                        (northZonalScalarCoeff_even_pos n |>.le)
                        (northZonalSqProfileScalarCoeff_le_three_quarters hn2)
                        m
                    gcongr
    _ ≤ Finset.sum (p.support.filter fun n => 2 ≤ n) (fun n => (3 / 4 : ℝ) ^ m * |p.coeff n|) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro n hn
            have hn_support : n ∈ ((northZonalSqProfilePolynomial^[m]) p).support := (Finset.mem_filter.mp hn).1
            have hcoeff_nonzero :
                ((northZonalSqProfilePolynomial^[m]) p).coeff n ≠ 0 :=
              mem_support_iff.mp hn_support
            have hpcoeff_nonzero : p.coeff n ≠ 0 := by
              intro hp0
              have hcoeff :
                  ((northZonalSqProfilePolynomial^[m]) p).coeff n = 0 := by
                simpa [hp0] using coeff_iter_northZonalSqProfilePolynomial p m n
              exact hcoeff_nonzero hcoeff
            exact Finset.mem_filter.mpr ⟨mem_support_iff.mpr hpcoeff_nonzero, (Finset.mem_filter.mp hn).2⟩
          · intro n hn1 hn2
            positivity
    _ = (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
          simp [sqProfileTailAbsSum, Finset.mul_sum]

@[simp] lemma northZonalSqProfileAverage_C_mul_X (a : ℝ) :
    northZonalSqProfileAverage ((C a * X).toContinuousMapOn unitIcc) =
      (C a * X).toContinuousMapOn unitIcc := by
  have hpoly : northZonalSqProfilePolynomial (C a * X : ℝ[X]) = C a * X := by
    ext n
    cases n with
    | zero =>
        simp [coeff_northZonalSqProfilePolynomial]
    | succ n =>
        cases n with
        | zero =>
            simp [coeff_northZonalSqProfilePolynomial, northZonalScalarCoeff_two]
        | succ n =>
            simp [coeff_northZonalSqProfilePolynomial]
  rw [northZonalSqProfileAverage_toContinuousMapOn]
  simp [hpoly]

lemma iterate_northZonalSqProfileAverage_toContinuousMapOn
    (p : ℝ[X]) (m : ℕ) :
    (northZonalSqProfileAverage^[m]) (p.toContinuousMapOn unitIcc) =
      ((northZonalSqProfilePolynomial^[m]) p).toContinuousMapOn unitIcc := by
  induction m generalizing p with
  | zero =>
      simp
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hm,
        northZonalSqProfileAverage_toContinuousMapOn]

lemma norm_iterate_northZonalSqProfileAverage_polynomial_sub_linear_le
    (p : ℝ[X]) (m : ℕ) (hp0 : p.eval 0 = 0) :
    ‖(northZonalSqProfileAverage^[m]) (p.toContinuousMapOn (Set.Icc (0 : ℝ) 1)) -
        (C (p.coeff 1) * X).toContinuousMapOn (Set.Icc (0 : ℝ) 1)‖
      ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
  let q : ℝ[X] := (northZonalSqProfilePolynomial^[m]) p
  have hpcoeff0 : p.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
  have hq0 : q.eval 0 = 0 := by
    rw [show q = (northZonalSqProfilePolynomial^[m]) p by rfl, ← Polynomial.coeff_zero_eq_eval_zero]
    simp [coeff_iter_northZonalSqProfilePolynomial, hpcoeff0]
  have hq1 : q.coeff 1 = p.coeff 1 := by
    simp [q, coeff_iter_northZonalSqProfilePolynomial, northZonalScalarCoeff_two]
  rw [iterate_northZonalSqProfileAverage_toContinuousMapOn]
  have hnorm :
      ‖q.toContinuousMapOn (Set.Icc (0 : ℝ) 1) -
          (C (q.coeff 1) * X).toContinuousMapOn (Set.Icc (0 : ℝ) 1)‖
        ≤ sqProfileTailAbsSum q :=
    norm_toContinuousMapOn_sub_linear_le_sqProfileTailAbsSum q hq0
  rw [hq1] at hnorm
  exact hnorm.trans (sqProfileTailAbsSum_iterate_le p m)

lemma dist_iterate_northZonalSqProfileAverage_le
    (r s : C(unitIcc, ℝ)) (m : ℕ) :
    dist ((northZonalSqProfileAverage^[m]) r) ((northZonalSqProfileAverage^[m]) s) ≤
      2 ^ m * dist r s := by
  induction m generalizing r s with
  | zero =>
      simp
  | succ m hm =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        dist (northZonalSqProfileAverage ((northZonalSqProfileAverage^[m]) r))
            (northZonalSqProfileAverage ((northZonalSqProfileAverage^[m]) s))
          ≤ 2 * dist ((northZonalSqProfileAverage^[m]) r) ((northZonalSqProfileAverage^[m]) s) := by
              exact dist_northZonalSqProfileAverage_le _ _
        _ ≤ 2 * (2 ^ m * dist r s) := by
              exact mul_le_mul_of_nonneg_left (hm _ _) (by positivity)
        _ = 2 ^ (m + 1) * dist r s := by ring

lemma dist_northZonalSqProfileAverage_iterate_succ_le
    (r : C(unitIcc, ℝ)) (m : ℕ) :
    dist ((northZonalSqProfileAverage^[m]) r)
        ((northZonalSqProfileAverage^[m.succ]) r)
      ≤ 2 ^ m * dist (northZonalSqProfileAverage r) r := by
  have hiter :
      northZonalSqProfileAverage ((northZonalSqProfileAverage^[m]) r) =
        (northZonalSqProfileAverage^[m]) (northZonalSqProfileAverage r) := by
    induction m with
    | zero =>
        simp
    | succ m hm =>
        simp [Function.iterate_succ_apply', hm]
  rw [show (northZonalSqProfileAverage^[m.succ]) r =
      northZonalSqProfileAverage ((northZonalSqProfileAverage^[m]) r) by
        rw [Function.iterate_succ_apply'],
      hiter]
  simpa [dist_comm] using
    dist_iterate_northZonalSqProfileAverage_le r (northZonalSqProfileAverage r) m

lemma dist_polynomial_to_iterate_northZonalSqProfileAverage_le_of_almost_fixed
    (p : ℝ[X]) (m : ℕ) :
    dist (sqProfilePolynomialMap p)
        ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
      ≤
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) *
          sqProfilePolynomialDefect p := by
  induction m with
  | zero =>
      simp [sqProfilePolynomialMap, sqProfilePolynomialDefect]
  | succ m hm =>
      calc
        dist (sqProfilePolynomialMap p)
            ((northZonalSqProfileAverage^[m.succ]) (sqProfilePolynomialMap p))
          ≤ dist (sqProfilePolynomialMap p)
                ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p)) +
              dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
                ((northZonalSqProfileAverage^[m.succ]) (sqProfilePolynomialMap p)) := by
                  exact dist_triangle _ _ _
        _ ≤
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) *
                sqProfilePolynomialDefect p +
              2 ^ m * sqProfilePolynomialDefect p := by
                    gcongr
                    exact dist_northZonalSqProfileAverage_iterate_succ_le
                      (sqProfilePolynomialMap p) m
        _ =
            (Finset.sum (Finset.range m.succ) fun j => (2 : ℝ) ^ j) *
              sqProfilePolynomialDefect p := by
                  rw [Finset.sum_range_succ]
                  ring

set_option maxHeartbeats 4000000 in
lemma norm_polynomial_sub_linear_le_of_sqprofile_almost_fixed
    (p : ℝ[X]) (m : ℕ) (hp0 : p.eval 0 = 0) :
    ‖sqProfilePolynomialMap p - sqProfileLinearPart p‖
      ≤
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) *
            sqProfilePolynomialDefect p +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
  have hiter :
      dist (sqProfilePolynomialMap p)
          ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
        ≤
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) *
            sqProfilePolynomialDefect p :=
    dist_polynomial_to_iterate_northZonalSqProfileAverage_le_of_almost_fixed p m
  have hiter' :
      ‖sqProfilePolynomialMap p -
          (northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p)‖
        ≤
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) *
            sqProfilePolynomialDefect p := by
    simpa [dist_eq_norm] using hiter
  have hlin :
      ‖(northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p) -
          sqProfileLinearPart p‖
        ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
    simpa [sqProfilePolynomialMap, sqProfileLinearPart, dist_eq_norm] using
      norm_iterate_northZonalSqProfileAverage_polynomial_sub_linear_le p m hp0
  calc
    ‖sqProfilePolynomialMap p - sqProfileLinearPart p‖
      = ‖(sqProfilePolynomialMap p -
            (northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p)) +
          (((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p)) -
            sqProfileLinearPart p)‖ := by
              abel_nf
    _ ≤
        ‖sqProfilePolynomialMap p -
            (northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p)‖ +
          ‖((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p)) -
            sqProfileLinearPart p‖ := by
              exact norm_add_le _ _
    _ ≤
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) *
            sqProfilePolynomialDefect p +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
              exact add_le_add hiter' hlin
