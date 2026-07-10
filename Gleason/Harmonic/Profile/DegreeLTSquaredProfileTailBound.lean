import Gleason.Harmonic.HighDegree.HighEvenBoundedSquaredQuotientDegree
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileDynamics
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Constructions

noncomputable section

open Complex InnerProductSpace Polynomial

def degreeLTSqProfileMapLinear (N : ℕ) :
    Polynomial.degreeLT ℝ N →ₗ[ℝ] C(unitIcc, ℝ) where
  toFun p := (p : ℝ[X]).toContinuousMapOn unitIcc
  map_add' p q := by
    ext u
    simp
  map_smul' a p := by
    ext u
    simp

lemma degreeLTSqProfileMapLinear_injective (N : ℕ) :
    Function.Injective (degreeLTSqProfileMapLinear N) := by
  intro p q hpq
  apply Subtype.ext
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.Icc (0 : ℝ) 1) ?_
    (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num))
  intro x hx
  have hx' : x ∈ unitIcc := hx
  have hval := congrArg (fun f : C(unitIcc, ℝ) => f ⟨x, hx'⟩) hpq
  simpa [degreeLTSqProfileMapLinear] using hval

def finDegreeLTSqProfileMapLinear (N : ℕ) :
    (Fin N → ℝ) →ₗ[ℝ] C(unitIcc, ℝ) :=
  (degreeLTSqProfileMapLinear N).comp ((Polynomial.degreeLTEquiv ℝ N).symm : (Fin N → ℝ) →ₗ[ℝ] _)

lemma finDegreeLTSqProfileMapLinear_injective (N : ℕ) :
    Function.Injective (finDegreeLTSqProfileMapLinear N) := by
  intro v w hvw
  apply (Polynomial.degreeLTEquiv ℝ N).symm.injective
  exact degreeLTSqProfileMapLinear_injective N hvw

def finDegreeLTSqProfileMapCLM (N : ℕ) :
    (Fin N → ℝ) →L[ℝ] C(unitIcc, ℝ) :=
  { toLinearMap := finDegreeLTSqProfileMapLinear N
    cont := (finDegreeLTSqProfileMapLinear N).continuous_of_finiteDimensional }

noncomputable def degreeLTSqProfileTailBoundConst (N : ℕ) : ℝ := by
  let T := finDegreeLTSqProfileMapLinear N
  let K : NNReal :=
    Classical.choose (LinearMap.exists_antilipschitzWith T
      (LinearMap.ker_eq_bot.mpr (finDegreeLTSqProfileMapLinear_injective N)))
  exact N * (K : ℝ)

theorem sqProfileTailAbsSum_le_degreeLTSqProfileTailBoundConst_mul_norm
    {N : ℕ} {p : ℝ[X]} (hp : p ∈ Polynomial.degreeLT ℝ N) :
    sqProfileTailAbsSum p
      ≤ degreeLTSqProfileTailBoundConst N * ‖p.toContinuousMapOn unitIcc‖ := by
  classical
  let pN : Polynomial.degreeLT ℝ N := ⟨p, hp⟩
  let v : Fin N → ℝ := Polynomial.degreeLTEquiv ℝ N pN
  let T := finDegreeLTSqProfileMapLinear N
  let Tclm := finDegreeLTSqProfileMapCLM N
  let hantiData :=
    LinearMap.exists_antilipschitzWith T
      (LinearMap.ker_eq_bot.mpr (finDegreeLTSqProfileMapLinear_injective N))
  let K : NNReal := Classical.choose hantiData
  have hanti : AntilipschitzWith K T := (Classical.choose_spec hantiData).2
  have hbound :
      ‖v‖ ≤ (K : ℝ) * ‖Tclm v‖ := by
    simpa [Tclm, T] using ContinuousLinearMap.bound_of_antilipschitz Tclm hanti v
  have hsubset :
      p.support.filter (fun n => 2 ≤ n) ⊆ Finset.range N := by
    intro n hn
    have hnsupp : n ∈ p.support := (Finset.mem_filter.mp hn).1
    have hcoeffnz : p.coeff n ≠ 0 := mem_support_iff.mp hnsupp
    have hnlt : n < N := by
      by_contra hnot
      have hzero : p.coeff n = 0 := by
        exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hp) n
          (Nat.le_of_not_gt hnot)
      exact hcoeffnz hzero
    exact Finset.mem_range.mpr hnlt
  calc
    sqProfileTailAbsSum p
      = Finset.sum (p.support.filter fun n => 2 ≤ n) (fun n => |p.coeff n|) := by
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
          simpa using (show ((∑ i, ‖v i‖₊ : NNReal) : ℝ) ≤ ((N • ‖v‖₊ : NNReal) : ℝ) by
            exact_mod_cast (by simpa using hsumNN))
    _ = N • ‖v‖ := by simp [nsmul_eq_mul]
    _ ≤ N • ((K : ℝ) * ‖Tclm v‖) := by
          simpa using nsmul_le_nsmul_right hbound N
    _ = (N : ℝ) * ((K : ℝ) * ‖Tclm v‖) := by
          simp [nsmul_eq_mul, mul_assoc]
    _ = degreeLTSqProfileTailBoundConst N * ‖p.toContinuousMapOn unitIcc‖ := by
          have hTclm :
              Tclm v = p.toContinuousMapOn unitIcc := by
            ext u
            simp [Tclm, finDegreeLTSqProfileMapCLM, T, finDegreeLTSqProfileMapLinear,
              degreeLTSqProfileMapLinear, v, pN]
          have hconst : degreeLTSqProfileTailBoundConst N = N * (K : ℝ) := by
            simp [degreeLTSqProfileTailBoundConst, T, hantiData, K]
          rw [hconst, hTclm]
          ring

theorem sqProfileTailAbsSum_X_mul_le_degreeLTSqProfileTailBoundConst_mul_norm
    {N : ℕ} {q : ℝ[X]} (hq : q ∈ Polynomial.degreeLT ℝ N) :
    sqProfileTailAbsSum (X * q)
      ≤ degreeLTSqProfileTailBoundConst (N + 1) * ‖(X * q : ℝ[X]).toContinuousMapOn unitIcc‖ := by
  apply sqProfileTailAbsSum_le_degreeLTSqProfileTailBoundConst_mul_norm
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
  intro n hn
  by_cases h0 : n = 0
  · subst h0
    simp
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨m, rfl⟩
    have hm : N ≤ m := by omega
    have hzero : q.coeff m = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hq) m hm
    rw [Polynomial.coeff_X_mul, hzero]

theorem exists_sqquotient_poly_degree_and_tail_bound_of_mem_highEvenBounded_of_isNorthZonal
    {N : ℕ} {h : C(spherePoint3, ℝ)}
    (hhN : h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hhz : IsNorthZonal h) :
    ∃ q : ℝ[X],
      q ∈ Polynomial.degreeLT ℝ N ∧
      (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
      sqProfileTailAbsSum (X * q)
        ≤ degreeLTSqProfileTailBoundConst (N + 1) * ‖sqCenteredNorthZonalContinuousMap h‖ := by
  rcases exists_sqquotient_poly_degree_of_mem_highEvenBounded_of_isNorthZonal hhN hhz with
    ⟨q, hqdeg, hqeval⟩
  have hmap :
      sqCenteredNorthZonalContinuousMap h = (X * q : ℝ[X]).toContinuousMapOn unitIcc := by
    ext u
    change sqCenteredNorthZonalProfile h u = (X * q).eval u.1
    rw [hqeval u]
    simp
  refine ⟨q, hqdeg, hqeval, ?_⟩
  calc
    sqProfileTailAbsSum (X * q)
      ≤ degreeLTSqProfileTailBoundConst (N + 1) * ‖(X * q : ℝ[X]).toContinuousMapOn unitIcc‖ := by
          exact sqProfileTailAbsSum_X_mul_le_degreeLTSqProfileTailBoundConst_mul_norm hqdeg
    _ = degreeLTSqProfileTailBoundConst (N + 1) * ‖sqCenteredNorthZonalContinuousMap h‖ := by
          rw [← hmap]
