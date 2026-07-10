import Gleason.Harmonic.HighDegree.HighEvenUnionProfilePolyApprox
import Gleason.Harmonic.HighDegree.EvenBoundedPolyDegree
import Gleason.Harmonic.HighDegree.HighEvenBoundedClosure
import Mathlib.Algebra.Polynomial.Inductions

noncomputable section

open Complex InnerProductSpace Polynomial

lemma coeff_evenPolynomialSqFactor (r : ℝ[X]) (k : ℕ) :
    (evenPolynomialSqFactor r).coeff k = r.coeff (2 * k) := by
  classical
  rw [evenPolynomialSqFactor, finset_sum_coeff]
  by_cases hs : 2 * k ∈ r.support
  · rw [Finset.sum_eq_single_of_mem (2 * k) hs]
    · rw [if_pos (even_two_mul k)]
      rw [coeff_C_mul_X_pow]
      simp
    · intro m hm hmne
      by_cases hEven : Even m
      · rcases hEven with ⟨j, rfl⟩
        have hEven' : Even (j + j) := ⟨j, by omega⟩
        rw [if_pos hEven', coeff_C_mul_X_pow]
        have hdiv : (j + j) / 2 = j := by omega
        rw [hdiv]
        by_cases hj : j = k
        · subst hj
          exact False.elim (hmne (by omega))
        · have hkj : ¬ k = j := by simpa [eq_comm] using hj
          simp [hkj]
      · rw [if_neg hEven]
        simp
  · rw [Finset.sum_eq_zero]
    · have hcoeff : r.coeff (2 * k) = 0 := by
        exact notMem_support_iff.mp hs
      simp [hcoeff]
    · intro m hm
      by_cases hEven : Even m
      · rcases hEven with ⟨j, rfl⟩
        have hEven' : Even (j + j) := ⟨j, by omega⟩
        rw [if_pos hEven', coeff_C_mul_X_pow]
        have hdiv : (j + j) / 2 = j := by omega
        rw [hdiv]
        by_cases hj : j = k
        · subst hj
          exact False.elim (hs (by simpa [two_mul] using hm))
        · have hkj : ¬ k = j := by simpa [eq_comm] using hj
          simp [hkj]
      · rw [if_neg hEven]
        simp

private lemma degree_one_sub_X_sq_le_two :
    (((1 : ℝ[X]) - X ^ 2).degree : WithBot ℕ) ≤ 2 := by
  calc
    (((1 : ℝ[X]) - X ^ 2).degree : WithBot ℕ)
        ≤ max (1 : ℝ[X]).degree (X ^ 2).degree := Polynomial.degree_sub_le _ _
    _ ≤ 2 := by
        refine max_le ?_ ?_
        · exact le_trans Polynomial.degree_C_le (by norm_num)
        · simpa using (Polynomial.degree_X_pow_le 2 : (X ^ 2 : ℝ[X]).degree ≤ 2)

private lemma degree_northMeridianSummand_le
    {N : ℕ} (d : Fin 3 →₀ ℕ) (c : ℝ)
    (hdeg : d.sum (fun _ e => e) ≤ 2 * N)
    (hcond : d 1 = 0 ∧ Even (d 0)) :
    (((Polynomial.C c * ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2) *
        Polynomial.X ^ (d 2)).degree : WithBot ℕ) ≤ 2 * N) := by
  rcases hcond.2 with ⟨k, hk⟩
  have hsum : 2 * k + d 2 ≤ 2 * N := by
    have hdeg' : d 0 + d 1 + d 2 ≤ 2 * N := by
      rw [Finsupp.sum_fintype _ _ (by intro i; rfl), Fin.sum_univ_three] at hdeg
      simpa using hdeg
    have hdeg'' : (k + k) + 0 + d 2 ≤ 2 * N := by
      simpa [hcond.1, hk] using hdeg'
    omega
  have hpow0 :
      ((((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ k).degree : WithBot ℕ) ≤ 2 * k := by
    calc
      ((((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ k).degree : WithBot ℕ)
          ≤ k • (((1 : Polynomial ℝ) - Polynomial.X ^ 2).degree : WithBot ℕ) :=
            Polynomial.degree_pow_le _ _
      _ ≤ k • (2 : WithBot ℕ) := by
            exact nsmul_le_nsmul_right degree_one_sub_X_sq_le_two k
      _ = 2 * k := by simp [nsmul_eq_mul, mul_comm]
  have hkdiv : (d 0 / 2) = k := by
    rw [hk]
    omega
  have hpow :
      ((((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2)).degree : WithBot ℕ) ≤ 2 * k := by
    rw [hkdiv]
    exact hpow0
  let a : Polynomial ℝ :=
    Polynomial.C c * ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2)
  let b : Polynomial ℝ := Polynomial.X ^ (d 2)
  have hmul1 :
      ((a.degree : WithBot ℕ)) ≤
        (Polynomial.C c).degree +
          (((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2)).degree := by
    dsimp [a]
    exact Polynomial.degree_mul_le _ _
  have hmul2 :
      (((a * b).degree : WithBot ℕ)) ≤ a.degree + b.degree := by
    exact Polynomial.degree_mul_le a b
  calc
    ((Polynomial.C c * ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2) *
        Polynomial.X ^ (d 2)).degree : WithBot ℕ)
        ≤ a.degree + b.degree := by
          simpa [a, b]
            using hmul2
    _ ≤ ((Polynomial.C c).degree +
          (((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2)).degree) +
          b.degree := by
            exact add_le_add hmul1 le_rfl
    _ ≤ 0 + (2 * k) + b.degree := by
          have hCpow :
              (Polynomial.C c).degree +
                  (((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ (d 0 / 2)).degree ≤
                0 + (2 * k) := by
            exact add_le_add Polynomial.degree_C_le hpow
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_right hCpow (b.degree : WithBot ℕ)
    _ ≤ 0 + (2 * k) + d 2 := by
          gcongr
          exact (Polynomial.degree_X_pow_le (d 2) :
            (b : ℝ[X]).degree ≤ d 2)
    _ = 2 * k + d 2 := by norm_num
    _ ≤ 2 * N := by exact_mod_cast hsum

theorem northMeridianPolynomial_mem_degreeLE_of_mem_restrictTotalDegree
    {N : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ (2 * N)) :
    northMeridianPolynomial p ∈ Polynomial.degreeLE ℝ (2 * N) := by
  classical
  rw [northMeridianPolynomial]
  refine Submodule.sum_mem _ ?_
  intro d hd
  by_cases hcond : d 1 = 0 ∧ Even (d 0)
  · have htot : p.totalDegree ≤ 2 * N :=
      (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := 2 * N) p).1 hp
    have hsupp : d.sum (fun _ e => e) ≤ 2 * N := le_trans (MvPolynomial.le_totalDegree hd) htot
    rw [if_pos hcond]
    exact (Polynomial.mem_degreeLE).2 (degree_northMeridianSummand_le d (p.coeff d) hsupp hcond)
  · rw [if_neg hcond]
    exact Submodule.zero_mem _

theorem evenPolynomialSqFactor_mem_degreeLT_of_mem_degreeLE
    {N : ℕ} {r : ℝ[X]}
    (hr : r ∈ Polynomial.degreeLE ℝ (2 * N)) :
    evenPolynomialSqFactor r ∈ Polynomial.degreeLT ℝ (N + 1) := by
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
  intro n hn
  have hdeg : r.degree ≤ (2 * N : WithBot ℕ) := (Polynomial.mem_degreeLE).1 hr
  have hlt : r.degree < (2 * n : WithBot ℕ) := by
    have hnat : 2 * N < 2 * n := by nlinarith
    exact lt_of_le_of_lt hdeg (by exact_mod_cast hnat)
  have hzero : r.coeff (2 * n) = 0 := Polynomial.coeff_eq_zero_of_degree_lt hlt
  simpa [coeff_evenPolynomialSqFactor] using hzero

theorem exists_sqquotient_poly_degree_of_mem_highEvenBounded_of_isNorthZonal
    {N : ℕ} {h : C(spherePoint3, ℝ)}
    (hhN : h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hhz : IsNorthZonal h) :
    ∃ q : ℝ[X],
      q ∈ Polynomial.degreeLT ℝ N ∧
      ∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1 := by
  have hhEven :
      h ∈ evenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
      N hhN
  rcases exists_even_mvPolynomial_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule_degree hhEven with
    ⟨p, hpdeg, hpEval, hpEven⟩
  let r : ℝ[X] :=
    northMeridianPolynomial p - Polynomial.C ((northMeridianPolynomial p).eval 0)
  let p0 : ℝ[X] := evenPolynomialSqFactor r
  have hrdeg :
      r ∈ Polynomial.degreeLE ℝ (2 * N) := by
    have hmer :
        northMeridianPolynomial p ∈ Polynomial.degreeLE ℝ (2 * N) :=
      northMeridianPolynomial_mem_degreeLE_of_mem_restrictTotalDegree hpdeg
    have hconst :
        Polynomial.C ((northMeridianPolynomial p).eval 0) ∈ Polynomial.degreeLE ℝ (2 * N) := by
      exact (Polynomial.mem_degreeLE).2 (le_trans Polynomial.degree_C_le (by norm_num))
    exact Submodule.sub_mem _ hmer hconst
  have hp0deg : p0 ∈ Polynomial.degreeLT ℝ (N + 1) :=
    evenPolynomialSqFactor_mem_degreeLT_of_mem_degreeLE hrdeg
  have hp0eval :
      ∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = p0.eval u.1 := by
    let r0 : ℝ[X] :=
      northMeridianPolynomial p - Polynomial.C ((northMeridianPolynomial p).eval 0)
    have hr0 : r0 = r := by rfl
    have hcomp :
        r0.comp (-Polynomial.X) = r0 :=
      centeredNorthZonalPolynomial_comp_neg_X_eq_self_of_isNorthZonal_of_even_mvPolynomial
        hhz hpEval hpEven
    intro u
    have hcenter :
        centeredNorthZonalProfile h
          ⟨Real.sqrt u.1, by
            constructor
            · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
              nlinarith
            · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
              have hle : Real.sqrt u.1 ≤ 1 := by
                nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
              simpa using hle⟩ =
        r0.eval (Real.sqrt u.1) := by
      simpa [r0] using
        centeredNorthZonalProfile_eq_northMeridianPolynomial_sub_const_of_isNorthZonal
          hhz hpEval
          ⟨Real.sqrt u.1, by
            constructor
            · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
              nlinarith
            · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
              have hle : Real.sqrt u.1 ≤ 1 := by
                nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
              simpa using hle⟩
    rw [sqCenteredNorthZonalProfile_apply, hcenter]
    have hsimp :
        p0.eval u.1 = r0.eval (Real.sqrt u.1) := by
      have :=
        evenPolynomialSqFactor_eval_sq_of_comp_neg_X_eq_self hcomp (Real.sqrt u.1)
      simpa [p0, r0, Real.sq_sqrt u.2.1] using this
    simpa [hsimp] using hsimp.symm
  refine ⟨p0.divX, ?_, ?_⟩
  · rw [Polynomial.mem_degreeLT]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro n hn
    have hn1 : N + 1 ≤ n + 1 := by omega
    have hcoeff0 : p0.coeff (n + 1) = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hp0deg) (n + 1) hn1
    simpa [Polynomial.coeff_divX] using hcoeff0
  · intro u
    have hdivxEval :
        (Polynomial.X * p0.divX + Polynomial.C (p0.coeff 0)).eval u.1 = p0.eval u.1 := by
      exact congrArg (fun s : ℝ[X] => s.eval u.1) (Polynomial.X_mul_divX_add p0)
    have hp00eval : p0.eval 0 = 0 := by
      calc
        p0.eval 0 = p0.eval zeroUnitIcc.1 := by simp [zeroUnitIcc]
        _ = sqCenteredNorthZonalProfile h zeroUnitIcc := by
              symm
              simpa using hp0eval zeroUnitIcc
        _ = 0 := by
              rw [sqCenteredNorthZonalProfile_apply]
              have hzero :
                  (⟨Real.sqrt (↑zeroUnitIcc), by
                    constructor
                    · nlinarith [Real.sqrt_nonneg (↑zeroUnitIcc)]
                    · have hsq : (Real.sqrt (↑zeroUnitIcc)) ^ 2 = (↑zeroUnitIcc : ℝ) :=
                        Real.sq_sqrt zeroUnitIcc.2.1
                      nlinarith [zeroUnitIcc.2.2, Real.sqrt_nonneg (↑zeroUnitIcc), hsq]⟩
                    : Set.Icc (-1 : ℝ) 1) = zeroIcc := by
                  apply Subtype.ext
                  simp [zeroUnitIcc, zeroIcc]
              rw [hzero]
              exact centeredNorthZonalProfile_zero h
    have hp00 : p0.coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hp00eval
    have hdivxEval' :
        p0.eval u.1 = u.1 * (p0.divX).eval u.1 + p0.coeff 0 := by
      have htmp :
          p0.eval u.1 = (Polynomial.X * p0.divX + Polynomial.C (p0.coeff 0)).eval u.1 :=
        hdivxEval.symm
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at htmp
      simpa using htmp
    calc
      sqCenteredNorthZonalProfile h u = p0.eval u.1 := hp0eval u
      _ = u.1 * (p0.divX).eval u.1 + p0.coeff 0 := hdivxEval'
      _ = u.1 * (p0.divX).eval u.1 := by simp [hp00]
