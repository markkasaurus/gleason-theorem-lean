import Gleason.Harmonic.HighDegree.HighEvenUnionProfileApprox
import Gleason.Harmonic.HighDegree.EvenBoundedPolyDegree
import Gleason.Harmonic.HighDegree.HighEvenBoundedClosure
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

noncomputable section

open Complex InnerProductSpace Polynomial

def evenPolynomialSqFactor (r : ℝ[X]) : ℝ[X] :=
  Finset.sum r.support fun n =>
    if Even n then Polynomial.C (r.coeff n) * Polynomial.X ^ (n / 2) else 0

lemma sphereMap_southFlip_eq_northRotation_pi_sphereAntipode
    (x : spherePoint3) :
    sphereMap southFlip x = sphereMap (northRotation Real.pi) (sphereAntipode x) := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [sphereMap, southFlip_apply, northRotation_apply, sphereAntipode, Circle.coe_exp,
    Complex.exp_pi_mul_I]

lemma spherePrecomp_southFlip_eq_self_of_isNorthZonal_of_antipode_even
    {g : C(spherePoint3, ℝ)}
    (hgz : IsNorthZonal g)
    (hanti : ∀ x : spherePoint3, g (sphereAntipode x) = g x) :
    spherePrecomp southFlip g = g := by
  ext x
  have hrot :
      g (sphereMap (northRotation Real.pi) (sphereAntipode x)) = g (sphereAntipode x) := by
    simpa [spherePrecomp_apply] using
      congrArg (fun f : C(spherePoint3, ℝ) => f (sphereAntipode x)) (hgz Real.pi)
  calc
    spherePrecomp southFlip g x = g (sphereMap southFlip x) := by rfl
    _ = g (sphereMap (northRotation Real.pi) (sphereAntipode x)) := by
          rw [sphereMap_southFlip_eq_northRotation_pi_sphereAntipode]
    _ = g (sphereAntipode x) := hrot
    _ = g x := hanti x

lemma centeredNorthZonalProfile_even_of_isNorthZonal_of_antipode_even
    {g : C(spherePoint3, ℝ)}
    (hgz : IsNorthZonal g)
    (hanti : ∀ x : spherePoint3, g (sphereAntipode x) = g x)
    (z : Set.Icc (-1 : ℝ) 1) :
    centeredNorthZonalProfile g (negIcc z) = centeredNorthZonalProfile g z := by
  have hsouth : spherePrecomp southFlip g = g :=
    spherePrecomp_southFlip_eq_self_of_isNorthZonal_of_antipode_even hgz hanti
  have hprof := congrArg (fun f : C(spherePoint3, ℝ) => centeredNorthZonalProfile f z) hsouth
  simpa using hprof

lemma coeff_eq_zero_of_comp_neg_X_eq_self_of_odd
    {r : ℝ[X]} (hcomp : r.comp (-Polynomial.X) = r)
    {n : ℕ} (hn : Odd n) :
    r.coeff n = 0 := by
  have hnegX : (-Polynomial.X : ℝ[X]) = Polynomial.C (-1) * Polynomial.X := by
    calc
      (-Polynomial.X : ℝ[X]) = (-1 : ℝ[X]) * Polynomial.X := by simp
      _ = Polynomial.C (-1) * Polynomial.X := by simp
  have hcoeff0 := congrArg (fun q : ℝ[X] => q.coeff n) hcomp
  rw [hnegX] at hcoeff0
  have hcoeff' :
      r.coeff n * (-1 : ℝ) ^ n = r.coeff n := by
    change (r.comp (Polynomial.C (-1) * Polynomial.X)).coeff n = r.coeff n at hcoeff0
    rw [Polynomial.comp_C_mul_X_coeff] at hcoeff0
    simpa [mul_comm] using hcoeff0
  have hneg : -r.coeff n = r.coeff n := by
    simpa [hn.neg_one_pow, mul_comm] using hcoeff'
  linarith

lemma evenPolynomialSqFactor_eval_sq_of_comp_neg_X_eq_self
    {r : ℝ[X]} (hcomp : r.comp (-Polynomial.X) = r) (x : ℝ) :
    (evenPolynomialSqFactor r).eval (x ^ 2) = r.eval x := by
  rw [evenPolynomialSqFactor, Polynomial.eval_finset_sum, Polynomial.eval_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hEven : Even n
  · rcases hEven with ⟨k, rfl⟩
    have hdiv : (k + k) / 2 = k := by omega
    rw [if_pos ⟨k, by omega⟩, hdiv]
    calc
      (Polynomial.C (r.coeff (k + k)) * Polynomial.X ^ k).eval (x ^ 2)
          = r.coeff (k + k) * (x ^ 2) ^ k := by
              rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      _ = r.coeff (k + k) * x ^ (2 * k) := by
            rw [show x ^ 2 = x ^ (2 : ℕ) by simp, ← pow_mul]
      _ = r.coeff (k + k) * x ^ (k + k) := by
            simp [two_mul]
  · have hodd : Odd n := Nat.not_even_iff_odd.mp hEven
    have hzero : r.coeff n = 0 :=
      coeff_eq_zero_of_comp_neg_X_eq_self_of_odd hcomp hodd
    rw [if_neg hEven, hzero]
    simp only [Polynomial.eval_zero, zero_mul]

theorem centeredNorthZonalPolynomial_comp_neg_X_eq_self_of_isNorthZonal_of_even_mvPolynomial
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g)
    (hpEven : sphereCoordPolyAntipode p = p) :
    let r : ℝ[X] :=
      northMeridianPolynomial p - Polynomial.C ((northMeridianPolynomial p).eval 0)
    r.comp (-Polynomial.X) = r := by
  let r : ℝ[X] :=
    northMeridianPolynomial p - Polynomial.C ((northMeridianPolynomial p).eval 0)
  have hanti :
      ∀ x : spherePoint3, g (sphereAntipode x) = g x := by
    have hEval :
        sphereCoordMvEval p = sphereAntipodeAlgHom (sphereCoordMvEval p) := by
      calc
        sphereCoordMvEval p = sphereCoordMvEval (sphereCoordPolyAntipode p) := by
          rw [hpEven]
        _ = sphereAntipodeAlgHom (sphereCoordMvEval p) := sphereCoordMvEval_polyAntipode p
    intro x
    simpa [hpEval, sphereAntipodeAlgHom_apply] using
      (congrArg (fun f : C(spherePoint3, ℝ) => f x) hEval).symm
  have hcenterEven :
      ∀ z : Set.Icc (-1 : ℝ) 1, r.eval (-z.1) = r.eval z.1 := by
    intro z
    have hcent :
        centeredNorthZonalProfile g (negIcc z) = centeredNorthZonalProfile g z :=
      centeredNorthZonalProfile_even_of_isNorthZonal_of_antipode_even hgz hanti z
    have hz := centeredNorthZonalProfile_eq_northMeridianPolynomial_sub_const_of_isNorthZonal hgz hpEval z
    have hnegz :=
      centeredNorthZonalProfile_eq_northMeridianPolynomial_sub_const_of_isNorthZonal hgz hpEval (negIcc z)
    calc
      r.eval (-z.1) = centeredNorthZonalProfile g (negIcc z) := by
        simpa [r, negIcc_val] using hnegz.symm
      _ = centeredNorthZonalProfile g z := hcent
      _ = r.eval z.1 := by
        simpa [r] using hz
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.Icc (-1 : ℝ) 1) ?_ (Set.Icc_infinite (show (-1 : ℝ) < 1 by norm_num))
  intro x hx
  calc
    (r.comp (-Polynomial.X)).eval x = r.eval (-x) := by
      rw [Polynomial.eval_comp]
      simp
    _ = r.eval x := hcenterEven ⟨x, hx⟩

theorem exists_sqCenteredNorthZonalPolynomial_of_isNorthZonal_of_even_mvPolynomial
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g)
    (hpEven : sphereCoordPolyAntipode p = p) :
    ∃ q : ℝ[X], ∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile g u = q.eval u.1 := by
  let r : ℝ[X] :=
    northMeridianPolynomial p - Polynomial.C ((northMeridianPolynomial p).eval 0)
  let q : ℝ[X] := evenPolynomialSqFactor r
  have hcomp : r.comp (-Polynomial.X) = r :=
    centeredNorthZonalPolynomial_comp_neg_X_eq_self_of_isNorthZonal_of_even_mvPolynomial
      hgz hpEval hpEven
  refine ⟨q, ?_⟩
  intro u
  have hcenter :
      centeredNorthZonalProfile g
        ⟨Real.sqrt u.1, by
          constructor
          · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
            nlinarith
          · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
            have hle : Real.sqrt u.1 ≤ 1 := by
              nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
            simpa using hle⟩ =
      r.eval (Real.sqrt u.1) := by
    simpa [r] using
      centeredNorthZonalProfile_eq_northMeridianPolynomial_sub_const_of_isNorthZonal
        hgz hpEval
        ⟨Real.sqrt u.1, by
          constructor
          · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
            nlinarith
          · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
            have hle : Real.sqrt u.1 ≤ 1 := by
              nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
            simpa using hle⟩
  rw [sqCenteredNorthZonalProfile_apply, hcenter]
  simpa [q, Real.sq_sqrt u.2.1] using
    (evenPolynomialSqFactor_eval_sq_of_comp_neg_X_eq_self hcomp (Real.sqrt u.1)).symm

theorem exists_fixed_northZonal_profile_poly_approx_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = q.eval u.1) ∧
          ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < ε := by
  rcases exists_fixed_northZonal_profile_approx_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, ?_⟩
  intro ε hε
  rcases happ hε with ⟨h, hhHigh, hhz, hdist⟩
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M, highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hhHigh
  rcases (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp hhHigh with
    ⟨N, hhN⟩
  have hhEven :
      h ∈ evenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule N hhN
  rcases exists_even_mvPolynomial_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule hhEven with
    ⟨p, hpEval, hpEven⟩
  rcases exists_sqCenteredNorthZonalPolynomial_of_isNorthZonal_of_even_mvPolynomial hhz hpEval hpEven with
    ⟨q, hq⟩
  exact ⟨h, q, hhHigh, hhz, hq, hdist⟩
