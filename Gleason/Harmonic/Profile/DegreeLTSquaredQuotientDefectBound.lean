import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientFixedContinuous
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileDynamics
import Gleason.Harmonic.Profile.SquaredProfileOperator
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Constructions

noncomputable section

open Complex InnerProductSpace Polynomial

def degreeLTQuotientMapLinear (N : ℕ) :
    Polynomial.degreeLT ℝ N →ₗ[ℝ] C(unitIcc, ℝ) where
  toFun p := (p : ℝ[X]).toContinuousMapOn unitIcc
  map_add' p q := by
    ext u
    simp
  map_smul' a p := by
    ext u
    simp

lemma degreeLTQuotientMapLinear_injective (N : ℕ) :
    Function.Injective (degreeLTQuotientMapLinear N) := by
  intro p q hpq
  apply Subtype.ext
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.Icc (0 : ℝ) 1) ?_
    (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num))
  intro x hx
  have hx' : x ∈ unitIcc := hx
  have hval := congrArg (fun f : C(unitIcc, ℝ) => f ⟨x, hx'⟩) hpq
  simpa [degreeLTQuotientMapLinear] using hval

def finDegreeLTQuotientMapLinear (N : ℕ) :
    (Fin N → ℝ) →ₗ[ℝ] C(unitIcc, ℝ) :=
  (degreeLTQuotientMapLinear N).comp
    ((Polynomial.degreeLTEquiv ℝ N).symm : (Fin N → ℝ) →ₗ[ℝ] _)

lemma finDegreeLTQuotientMapLinear_injective (N : ℕ) :
    Function.Injective (finDegreeLTQuotientMapLinear N) := by
  intro v w hvw
  apply (Polynomial.degreeLTEquiv ℝ N).symm.injective
  exact degreeLTQuotientMapLinear_injective N hvw

def finDegreeLTQuotientMapCLM (N : ℕ) :
    (Fin N → ℝ) →L[ℝ] C(unitIcc, ℝ) :=
  { toLinearMap := finDegreeLTQuotientMapLinear N
    cont := (finDegreeLTQuotientMapLinear N).continuous_of_finiteDimensional }

def degreeLTSqMulMapLinear (N : ℕ) :
    Polynomial.degreeLT ℝ N →ₗ[ℝ] C(unitIcc, ℝ) where
  toFun p := sqMulContinuousMap ((p : ℝ[X]).toContinuousMapOn unitIcc)
  map_add' p q := by
    ext u
    simp [sqMulContinuousMap_apply, mul_add]
  map_smul' a p := by
    ext u
    simp [sqMulContinuousMap_apply]
    ring

lemma degreeLTSqMulMapLinear_injective (N : ℕ) :
    Function.Injective (degreeLTSqMulMapLinear N) := by
  intro p q hpq
  apply Subtype.ext
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.Ioc (0 : ℝ) 1) ?_
    (Set.Ioc_infinite (show (0 : ℝ) < 1 by norm_num))
  intro x hx
  have hx' : x ∈ unitIcc := by
    exact ⟨le_of_lt hx.1, hx.2⟩
  have hval := congrArg (fun f : C(unitIcc, ℝ) => f ⟨x, hx'⟩) hpq
  have hx0 : (x : ℝ) ≠ 0 := ne_of_gt hx.1
  have hval' : x * (p : ℝ[X]).eval x = x * (q : ℝ[X]).eval x := by
    simpa [degreeLTSqMulMapLinear, sqMulContinuousMap_apply] using hval
  exact mul_left_cancel₀ hx0 hval'

def finDegreeLTSqMulMapLinear (N : ℕ) :
    (Fin N → ℝ) →ₗ[ℝ] C(unitIcc, ℝ) :=
  (degreeLTSqMulMapLinear N).comp
    ((Polynomial.degreeLTEquiv ℝ N).symm : (Fin N → ℝ) →ₗ[ℝ] _)

lemma finDegreeLTSqMulMapLinear_injective (N : ℕ) :
    Function.Injective (finDegreeLTSqMulMapLinear N) := by
  intro v w hvw
  apply (Polynomial.degreeLTEquiv ℝ N).symm.injective
  exact degreeLTSqMulMapLinear_injective N hvw

def finDegreeLTSqMulMapCLM (N : ℕ) :
    (Fin N → ℝ) →L[ℝ] C(unitIcc, ℝ) :=
  { toLinearMap := finDegreeLTSqMulMapLinear N
    cont := (finDegreeLTSqMulMapLinear N).continuous_of_finiteDimensional }

noncomputable def degreeLTPolyTailBoundConst (N : ℕ) : ℝ := by
  let T := finDegreeLTQuotientMapLinear N
  let K : NNReal :=
    Classical.choose (LinearMap.exists_antilipschitzWith T
      (LinearMap.ker_eq_bot.mpr (finDegreeLTQuotientMapLinear_injective N)))
  exact N * (K : ℝ)

noncomputable def degreeLTSqMulNormConst (N : ℕ) : ℝ := by
  let S := finDegreeLTSqMulMapLinear N
  let T := finDegreeLTQuotientMapCLM N
  let hantiData :=
    LinearMap.exists_antilipschitzWith S
      (LinearMap.ker_eq_bot.mpr (finDegreeLTSqMulMapLinear_injective N))
  let K : NNReal := Classical.choose hantiData
  exact ‖T‖ * (K : ℝ)

theorem polyTailAbsSum_le_degreeLTPolyTailBoundConst_mul_norm
    {N : ℕ} {p : ℝ[X]} (hp : p ∈ Polynomial.degreeLT ℝ N) :
    polyTailAbsSum p
      ≤ degreeLTPolyTailBoundConst N * ‖p.toContinuousMapOn unitIcc‖ := by
  classical
  let pN : Polynomial.degreeLT ℝ N := ⟨p, hp⟩
  let v : Fin N → ℝ := Polynomial.degreeLTEquiv ℝ N pN
  let T := finDegreeLTQuotientMapLinear N
  let Tclm := finDegreeLTQuotientMapCLM N
  let hantiData :=
    LinearMap.exists_antilipschitzWith T
      (LinearMap.ker_eq_bot.mpr (finDegreeLTQuotientMapLinear_injective N))
  let K : NNReal := Classical.choose hantiData
  have hanti : AntilipschitzWith K T := (Classical.choose_spec hantiData).2
  have hbound :
      ‖v‖ ≤ (K : ℝ) * ‖Tclm v‖ := by
    simpa [Tclm, T] using ContinuousLinearMap.bound_of_antilipschitz Tclm hanti v
  have hsubset :
      p.support.erase 0 ⊆ Finset.range N := by
    intro n hn
    rcases Finset.mem_erase.mp hn with ⟨_, hns⟩
    have hcoeffnz : p.coeff n ≠ 0 := mem_support_iff.mp hns
    have hnlt : n < N := by
      by_contra hnot
      have hzero : p.coeff n = 0 := by
        exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hp) n
          (Nat.le_of_not_gt hnot)
      exact hcoeffnz hzero
    exact Finset.mem_range.mpr hnlt
  calc
    polyTailAbsSum p
      = Finset.sum (p.support.erase 0) (fun n => |p.coeff n|) := by
          rfl
    _ ≤ Finset.sum (Finset.range N) (fun n => |p.coeff n|) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro n hn1 hn2
          exact abs_nonneg _
    _ = ∑ i : Fin N, ‖v i‖ := by
          rw [← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [v, pN, Polynomial.degreeLTEquiv]
    _ = ((∑ i : Fin N, ‖v i‖₊) : ℝ) := by simp
    _ ≤ ((N • ‖v‖₊ : NNReal) : ℝ) := by
          have hsumNN : ∑ i, ‖v i‖₊ ≤ Fintype.card (Fin N) • ‖v‖₊ :=
            Pi.sum_nnnorm_apply_le_nnnorm v
          exact_mod_cast (by simpa using hsumNN)
    _ = N • ‖v‖ := by simp [nsmul_eq_mul]
    _ ≤ N • ((K : ℝ) * ‖Tclm v‖) := by
          simpa using nsmul_le_nsmul_right hbound N
    _ = (N : ℝ) * ((K : ℝ) * ‖Tclm v‖) := by
          simp [nsmul_eq_mul]
    _ = degreeLTPolyTailBoundConst N * ‖p.toContinuousMapOn unitIcc‖ := by
          have hTclm :
              Tclm v = p.toContinuousMapOn unitIcc := by
            ext u
            simp [Tclm, finDegreeLTQuotientMapCLM, finDegreeLTQuotientMapLinear,
              degreeLTQuotientMapLinear, v, pN]
          have hconst : degreeLTPolyTailBoundConst N = N * (K : ℝ) := by
            simp [degreeLTPolyTailBoundConst, T, K]
          rw [hconst, hTclm]
          ring

theorem polyTailAbsSum_le_four_mul_polyTailAbsSum_defect
    (p : ℝ[X]) :
    polyTailAbsSum p ≤
      4 * polyTailAbsSum (northZonalSqQuotientPolynomial p - p) := by
  classical
  let d : ℝ[X] := northZonalSqQuotientPolynomial p - p
  have hsubset :
      p.support.erase 0 ⊆ d.support.erase 0 := by
    intro n hn
    rcases Finset.mem_erase.mp hn with ⟨hn0, hns⟩
    have hpcoeffnz : p.coeff n ≠ 0 := mem_support_iff.mp hns
    have hcoeff :
        d.coeff n = (northZonalSqQuotientScalarCoeff n - 1) * p.coeff n := by
      simp [d, coeff_northZonalSqQuotientPolynomial]
      ring
    have hnpos : 0 < n := Nat.pos_iff_ne_zero.mpr hn0
    have hlt : northZonalSqQuotientScalarCoeff n < 1 :=
      northZonalSqQuotientScalarCoeff_lt_one hnpos
    have hne : northZonalSqQuotientScalarCoeff n - 1 ≠ 0 := by
      linarith
    have hdcoeffnz : d.coeff n ≠ 0 := by
      rw [hcoeff]
      exact mul_ne_zero hne hpcoeffnz
    exact Finset.mem_erase.mpr ⟨hn0, mem_support_iff.mpr hdcoeffnz⟩
  calc
    polyTailAbsSum p
      = Finset.sum (p.support.erase 0) (fun n => |p.coeff n|) := by
          rfl
    _ ≤ Finset.sum (p.support.erase 0) (fun n => 4 * |d.coeff n|) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          rcases Finset.mem_erase.mp hn with ⟨hn0, _⟩
          have hnpos : 0 < n := Nat.pos_iff_ne_zero.mpr hn0
          have hcoeff :
              d.coeff n = (northZonalSqQuotientScalarCoeff n - 1) * p.coeff n := by
            simp [d, coeff_northZonalSqQuotientPolynomial]
            ring
          have hcoeffAbs :
              |d.coeff n| =
                (1 - northZonalSqQuotientScalarCoeff n) * |p.coeff n| := by
            rw [hcoeff, abs_mul, abs_of_nonpos]
            · ring
            · linarith [northZonalSqQuotientScalarCoeff_lt_one hnpos]
          have hquarter :
              (1 / 4 : ℝ) ≤ 1 - northZonalSqQuotientScalarCoeff n := by
            linarith [northZonalSqQuotientScalarCoeff_le_three_quarters hnpos]
          have hmul :
              (1 / 4 : ℝ) * |p.coeff n| ≤ |d.coeff n| := by
            rw [hcoeffAbs]
            gcongr
          nlinarith [abs_nonneg (p.coeff n)]
    _ ≤ Finset.sum (d.support.erase 0) (fun n => 4 * |d.coeff n|) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro n hn1 hn2
          positivity
    _ = 4 * polyTailAbsSum d := by
          simp [polyTailAbsSum, Finset.mul_sum, d]

theorem norm_toContinuousMapOn_sub_const_le_four_mul_degreeLTPolyTailBoundConst_mul_defect
    {N : ℕ} {p : ℝ[X]}
    (hpdeg : p ∈ Polynomial.degreeLT ℝ N) :
    ‖p.toContinuousMapOn unitIcc - ContinuousMap.const _ (p.coeff 0)‖ ≤
      4 * degreeLTPolyTailBoundConst N *
        dist (northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc))
          (p.toContinuousMapOn unitIcc) := by
  let d : ℝ[X] := northZonalSqQuotientPolynomial p - p
  have hTdeg : northZonalSqQuotientPolynomial p ∈ Polynomial.degreeLT ℝ N := by
    rw [Polynomial.mem_degreeLT]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro n hn
    have hpcoeff :
        p.coeff n = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hpdeg) n hn
    simp [coeff_northZonalSqQuotientPolynomial, hpcoeff]
  have hddeg : d ∈ Polynomial.degreeLT ℝ N := by
    exact Submodule.sub_mem _ hTdeg hpdeg
  have htaild :
      polyTailAbsSum d ≤
        degreeLTPolyTailBoundConst N * ‖d.toContinuousMapOn unitIcc‖ :=
    polyTailAbsSum_le_degreeLTPolyTailBoundConst_mul_norm hddeg
  have hmapd :
      d.toContinuousMapOn unitIcc =
        northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc) -
          p.toContinuousMapOn unitIcc := by
    ext u
    simp [d, northZonalSqQuotientAverage_toContinuousMapOn]
  calc
    ‖p.toContinuousMapOn unitIcc - ContinuousMap.const _ (p.coeff 0)‖
      ≤ polyTailAbsSum p := norm_toContinuousMapOn_sub_const_le_polyTailAbsSum p
    _ ≤ 4 * polyTailAbsSum d := polyTailAbsSum_le_four_mul_polyTailAbsSum_defect p
    _ ≤ 4 * (degreeLTPolyTailBoundConst N * ‖d.toContinuousMapOn unitIcc‖) := by
          gcongr
    _ = 4 * degreeLTPolyTailBoundConst N *
          dist (northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc))
            (p.toContinuousMapOn unitIcc) := by
          rw [hmapd]
          simp [dist_eq_norm, mul_assoc]

lemma norm_sqMulContinuousMap_le (q : C(unitIcc, ℝ)) :
    ‖sqMulContinuousMap q‖ ≤ ‖q‖ := by
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := sqMulContinuousMap q) (M := ‖q‖)).2 ?_
  intro u
  rw [sqMulContinuousMap_apply]
  calc
    ‖u.1 * q u‖ = |u.1| * ‖q u‖ := by
      rw [norm_mul, Real.norm_eq_abs]
    _ ≤ 1 * ‖q‖ := by
      gcongr
      · simpa [abs_of_nonneg u.2.1] using u.2.2
      · exact q.norm_coe_le_norm u
    _ = ‖q‖ := by ring

theorem sqProfilePolynomialDefect_X_mul_le_quotientDefect
    (q : ℝ[X]) :
    sqProfilePolynomialDefect (X * q) ≤
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
        (q.toContinuousMapOn unitIcc) := by
  have hsqMul :
      sqProfilePolynomialMap (X * q) = sqMulContinuousMap (q.toContinuousMapOn unitIcc) := by
    ext u
    simp [sqProfilePolynomialMap, sqMulContinuousMap_apply]
  have havg :
      northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)) =
        sqMulContinuousMap (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc)) := by
    rw [hsqMul, northZonalSqProfileAverage_sqMulContinuousMap]
  have hsub :
      northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)) -
          sqProfilePolynomialMap (X * q) =
        sqMulContinuousMap
          (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) -
            q.toContinuousMapOn unitIcc) := by
    ext u
    rw [havg, hsqMul]
    simp [sqMulContinuousMap_apply]
    ring
  rw [sqProfilePolynomialDefect, dist_eq_norm, hsub, dist_eq_norm]
  exact norm_sqMulContinuousMap_le
    (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) -
      q.toContinuousMapOn unitIcc)

theorem norm_toContinuousMapOn_le_degreeLTSqMulNormConst_mul_norm_sqMul
    {N : ℕ} {p : ℝ[X]} (hp : p ∈ Polynomial.degreeLT ℝ N) :
    ‖p.toContinuousMapOn unitIcc‖ ≤
      degreeLTSqMulNormConst N *
        ‖sqMulContinuousMap (p.toContinuousMapOn unitIcc)‖ := by
  classical
  let pN : Polynomial.degreeLT ℝ N := ⟨p, hp⟩
  let v : Fin N → ℝ := Polynomial.degreeLTEquiv ℝ N pN
  let S := finDegreeLTSqMulMapLinear N
  let Sclm := finDegreeLTSqMulMapCLM N
  let Tclm := finDegreeLTQuotientMapCLM N
  let hantiData :=
    LinearMap.exists_antilipschitzWith S
      (LinearMap.ker_eq_bot.mpr (finDegreeLTSqMulMapLinear_injective N))
  let K : NNReal := Classical.choose hantiData
  have hanti : AntilipschitzWith K S := (Classical.choose_spec hantiData).2
  have hboundS :
      ‖v‖ ≤ (K : ℝ) * ‖Sclm v‖ := by
    simpa [Sclm, S] using ContinuousLinearMap.bound_of_antilipschitz Sclm hanti v
  have hboundT :
      ‖Tclm v‖ ≤ ‖Tclm‖ * ‖v‖ := by
    simpa using Tclm.le_opNorm v
  have hT :
      Tclm v = p.toContinuousMapOn unitIcc := by
    ext u
    simp [Tclm, finDegreeLTQuotientMapCLM, finDegreeLTQuotientMapLinear,
      degreeLTQuotientMapLinear, v, pN]
  calc
    ‖p.toContinuousMapOn unitIcc‖ = ‖Tclm v‖ := by rw [hT]
    _ ≤ ‖Tclm‖ * ‖v‖ := hboundT
    _ ≤ ‖Tclm‖ * ((K : ℝ) * ‖Sclm v‖) := by
      gcongr
    _ = degreeLTSqMulNormConst N *
          ‖sqMulContinuousMap (p.toContinuousMapOn unitIcc)‖ := by
      have hS :
          Sclm v = sqMulContinuousMap (p.toContinuousMapOn unitIcc) := by
        ext u
        simp [Sclm, finDegreeLTSqMulMapCLM, finDegreeLTSqMulMapLinear,
          degreeLTSqMulMapLinear, v, pN, sqMulContinuousMap_apply]
      have hconst : degreeLTSqMulNormConst N = ‖Tclm‖ * (K : ℝ) := by
        simp [degreeLTSqMulNormConst, S, Tclm, hantiData, K]
      rw [hS, hconst]
      ring

theorem norm_quotientDefect_le_degreeLTSqMulNormConst_mul_sqprofileDefect
    {N : ℕ} {q : ℝ[X]} (hqdeg : q ∈ Polynomial.degreeLT ℝ N) :
    dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
        (q.toContinuousMapOn unitIcc) ≤
      degreeLTSqMulNormConst N * sqProfilePolynomialDefect (X * q) := by
  let d : ℝ[X] := northZonalSqQuotientPolynomial q - q
  have hTdeg : northZonalSqQuotientPolynomial q ∈ Polynomial.degreeLT ℝ N := by
    rw [Polynomial.mem_degreeLT]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro n hn
    have hqcoeff :
        q.coeff n = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hqdeg) n hn
    simp [coeff_northZonalSqQuotientPolynomial, hqcoeff]
  have hddeg : d ∈ Polynomial.degreeLT ℝ N := by
    exact Submodule.sub_mem _ hTdeg hqdeg
  have hmapd :
      d.toContinuousMapOn unitIcc =
        northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) -
          q.toContinuousMapOn unitIcc := by
    ext u
    simp [d, northZonalSqQuotientAverage_toContinuousMapOn]
  have hsqMul :
      sqMulContinuousMap (d.toContinuousMapOn unitIcc) =
        northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)) -
          sqProfilePolynomialMap (X * q) := by
    ext u
    have hsqp :
        sqProfilePolynomialMap (X * q) = sqMulContinuousMap (q.toContinuousMapOn unitIcc) := by
      ext v
      simp [sqProfilePolynomialMap, sqMulContinuousMap_apply]
    rw [hsqp, northZonalSqProfileAverage_sqMulContinuousMap]
    simp [hmapd, sqMulContinuousMap_apply]
    ring
  calc
    dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
        (q.toContinuousMapOn unitIcc)
      = ‖d.toContinuousMapOn unitIcc‖ := by
          rw [dist_eq_norm, ← hmapd]
    _ ≤ degreeLTSqMulNormConst N * ‖sqMulContinuousMap (d.toContinuousMapOn unitIcc)‖ :=
          norm_toContinuousMapOn_le_degreeLTSqMulNormConst_mul_norm_sqMul hddeg
    _ = degreeLTSqMulNormConst N * sqProfilePolynomialDefect (X * q) := by
          rw [hsqMul, sqProfilePolynomialDefect, dist_eq_norm]
