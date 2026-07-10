import Gleason.Harmonic.Sphere.S2DistinguishedSquaredProfilePoly
import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientFixedPolynomial
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileQuadratic
import Gleason.Harmonic.Profile.LowProfileVanishing

noncomputable section

open Complex InnerProductSpace Polynomial

namespace GleasonS2Bridge

open SphericalHarmonics

private lemma centeredNorthZonalProfile_eq_sqquotient_const_of_even
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hnEven : Even n)
    (hgz : IsNorthZonal g)
    {c : ℝ}
    (hq : ∀ u : unitIcc, sqCenteredNorthZonalProfile g u = u.1 * c) :
    ∀ z : Set.Icc (-1 : ℝ) 1, centeredNorthZonalProfile g z = c * z.1 ^ 2 := by
  intro z
  have hsq :
      sqCenteredNorthZonalProfile g ⟨z.1 ^ 2, sq_mem_Icc z⟩ = c * z.1 ^ 2 := by
    calc
      sqCenteredNorthZonalProfile g ⟨z.1 ^ 2, sq_mem_Icc z⟩
          = (⟨z.1 ^ 2, sq_mem_Icc z⟩ : unitIcc).1 * c := hq ⟨z.1 ^ 2, sq_mem_Icc z⟩
      _ = c * z.1 ^ 2 := by ring
  rw [sqCenteredNorthZonalProfile_eq_absProfile] at hsq
  by_cases hz : 0 ≤ z.1
  · have habs : absIcc z = z := by
      apply Subtype.ext
      simp [absIcc, abs_of_nonneg hz]
    simpa [habs] using hsq
  · have hpar :=
      sphereRestriction_sphereNeg_of_mem_continuousHarmonicSphereDegreeSubmodule hg
    have hanti : ∀ x : spherePoint3, g (sphereAntipode x) = g x := by
      intro x
      have hx : sphereNeg x = sphereAntipode x := by
        apply Subtype.ext
        simp [sphereNeg, sphereAntipode]
      have hpow : (-1 : ℝ) ^ n = 1 := by
        rcases hnEven with ⟨k, rfl⟩
        simp
      calc
        g (sphereAntipode x) = g (sphereNeg x) := by rw [← hx]
        _ = (-1 : ℝ) ^ n * g x := sphereRestriction_sphereNeg_of_mem_continuousHarmonicSphereDegreeSubmodule hg x
        _ = g x := by simp [hpow]
    have hcenter_even :
        centeredNorthZonalProfile g (negIcc z) = centeredNorthZonalProfile g z :=
      centeredNorthZonalProfile_even_of_isNorthZonal_of_antipode_even hgz hanti z
    have habs : absIcc z = negIcc z := by
      apply Subtype.ext
      simp [absIcc, negIcc, abs_of_neg (lt_of_not_ge hz)]
    calc
      centeredNorthZonalProfile g z
          = centeredNorthZonalProfile g (negIcc z) := by simpa using hcenter_even.symm
      _ = centeredNorthZonalProfile g (absIcc z) := by rw [habs]
      _ = c * z.1 ^ 2 := hsq

private lemma isNorthZonal_eq_const_add_sq_of_sqquotient_const_of_even
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hnEven : Even n)
    (hgz : IsNorthZonal g)
    {c : ℝ}
    (hq : ∀ u : unitIcc, sqCenteredNorthZonalProfile g u = u.1 * c) :
    ∀ x : spherePoint3, g x = g sphereE2 + c * sphereCoordZ x ^ 2 := by
  intro x
  have hcent :=
    centeredNorthZonalProfile_eq_sqquotient_const_of_even hg hnEven hgz hq
      ⟨sphereCoordZ x, snd_mem_Icc x⟩
  have hprof := northZonalProfile_eq_of_isNorthZonal hgz x
  calc
    g x = northZonalProfile g ⟨sphereCoordZ x, snd_mem_Icc x⟩ := by
      simpa [sphereCoordZ] using hprof.symm
    _ = centeredNorthZonalProfile g ⟨sphereCoordZ x, snd_mem_Icc x⟩ +
          northZonalProfile g zeroIcc := by
            simp [centeredNorthZonalProfile]
    _ = c * sphereCoordZ x ^ 2 + g sphereE2 := by
          rw [hcent, northZonalProfile_zero_of_isNorthZonal hgz]
    _ = g sphereE2 + c * sphereCoordZ x ^ 2 := by ring

theorem distinguishedSqquotientPolynomial_not_constant_of_even_gt_two
    {n : ℕ} (hnEven : Even n) (hn2 : 2 < n) :
    ∀ q : ℝ[X],
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))) u =
          u.1 * q.eval u.1) →
      q ≠ Polynomial.C (q.coeff 0) := by
  intro q hq hconst
  let g : C(spherePoint3, ℝ) :=
    s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
      C(S2, ℝ))))
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n :=
    s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule_distinguishedZonalSector n
  have hgz : IsNorthZonal g := isNorthZonal_s2Pullback_distinguishedZonalSector n
  have hqconst : ∀ u : unitIcc, sqCenteredNorthZonalProfile g u = u.1 * q.coeff 0 := by
    intro u
    calc
      sqCenteredNorthZonalProfile g u = u.1 * q.eval u.1 := hq u
      _ = u.1 * q.coeff 0 := by rw [hconst]; simp
  have hrep :
      ∀ x : spherePoint3, g x = g sphereE2 + q.coeff 0 * sphereCoordZ x ^ 2 :=
    isNorthZonal_eq_const_add_sq_of_sqquotient_const_of_even hg hnEven hgz hqconst
  rcases hg with ⟨f, hf, hfg⟩
  rcases hnEven with ⟨k, hk⟩
  have hk1 : 1 ≤ k - 1 := by
    omega
  have hgzero : g = 0 := by
    exact eq_zero_of_even_degree_gt_two_of_sphere_low_profile (k := k - 1) hk1
      (by simpa [hk, two_mul, Nat.sub_add_cancel (by omega : 1 ≤ k)] using hf)
      hfg hrep
  have hsector_zero :
      (((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)) = 0 := by
    apply s2Pullback.injective
    simpa [g] using hgzero
  exact distinguishedZonalSector_ne_zero n (by
    apply Subtype.ext
    exact hsector_zero)

theorem northZonalSqQuotientPolynomial_ne_self_of_even_distinguishedZonalSector_gt_two
    {n : ℕ} (hnEven : Even n) (hn2 : 2 < n) :
    ∀ q : ℝ[X],
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))) u =
          u.1 * q.eval u.1) →
      northZonalSqQuotientPolynomial q ≠ q := by
  intro q hq hfix
  have hconst : q = Polynomial.C (q.coeff 0) := by
    simpa [hfix] using northZonalSqQuotientPolynomial_eq_C_of_fixed q hfix
  exact distinguishedSqquotientPolynomial_not_constant_of_even_gt_two hnEven hn2 q hq hconst

theorem northZonalSqQuotientPolynomial_ne_neg_self_of_even_distinguishedZonalSector_gt_two
    {n : ℕ} (hnEven : Even n) (hn2 : 2 < n) :
    ∀ q : ℝ[X],
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))) u =
          u.1 * q.eval u.1) →
      northZonalSqQuotientPolynomial q ≠ -q := by
  intro q hq hneg
  have hconst : q = Polynomial.C (q.coeff 0) := by
    ext k
    cases k with
    | zero =>
        have hcoeff :=
          congrArg (fun r : ℝ[X] => r.coeff 0) hneg
        simpa [coeff_northZonalSqQuotientPolynomial] using hcoeff
    | succ k =>
        have hcoeff :
            northZonalSqQuotientScalarCoeff k.succ * q.coeff k.succ = -q.coeff k.succ := by
          have := congrArg (fun r : ℝ[X] => r.coeff k.succ) hneg
          simpa [coeff_northZonalSqQuotientPolynomial] using this
        have hqzero : q.coeff k.succ = 0 := by
          by_contra hqnz
          have hscal : northZonalSqQuotientScalarCoeff k.succ = -1 := by
            exact mul_right_cancel₀ hqnz (by linarith [hcoeff])
          have hnonneg : 0 ≤ northZonalSqQuotientScalarCoeff k.succ :=
            northZonalSqQuotientScalarCoeff_nonneg k.succ
          linarith
        simp [hqzero]
  exact distinguishedSqquotientPolynomial_not_constant_of_even_gt_two hnEven hn2 q hq hconst

theorem northZonalSqQuotientAverage_toContinuousMapOn_ne_self_of_even_distinguishedZonalSector_gt_two
    {n : ℕ} (hnEven : Even n) (hn2 : 2 < n) :
    ∀ q : ℝ[X],
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))) u =
          u.1 * q.eval u.1) →
      northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) ≠ q.toContinuousMapOn unitIcc := by
  intro q hq hfix
  have hpoly :
      northZonalSqQuotientPolynomial q = q := by
    have hcont :
        (northZonalSqQuotientPolynomial q).toContinuousMapOn unitIcc =
          q.toContinuousMapOn unitIcc := by
      simpa [northZonalSqQuotientAverage_toContinuousMapOn] using hfix
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.Icc (0 : ℝ) 1) ?_
      (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num))
    intro x hx
    have hx' := congrArg (fun f : C(unitIcc, ℝ) => f ⟨x, hx⟩) hcont
    simpa using hx'
  exact northZonalSqQuotientPolynomial_ne_self_of_even_distinguishedZonalSector_gt_two
    hnEven hn2 q hq hpoly

theorem northZonalSqQuotientAverage_toContinuousMapOn_ne_neg_self_of_even_distinguishedZonalSector_gt_two
    {n : ℕ} (hnEven : Even n) (hn2 : 2 < n) :
    ∀ q : ℝ[X],
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))) u =
          u.1 * q.eval u.1) →
      northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) ≠
        -q.toContinuousMapOn unitIcc := by
  intro q hq hneg
  have hpoly :
      northZonalSqQuotientPolynomial q = -q := by
    have hcont :
        (northZonalSqQuotientPolynomial q).toContinuousMapOn unitIcc =
          -q.toContinuousMapOn unitIcc := by
      simpa [northZonalSqQuotientAverage_toContinuousMapOn] using hneg
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.Icc (0 : ℝ) 1) ?_
      (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num))
    intro x hx
    have hx' := congrArg (fun f : C(unitIcc, ℝ) => f ⟨x, hx⟩) hcont
    simpa using hx'
  exact northZonalSqQuotientPolynomial_ne_neg_self_of_even_distinguishedZonalSector_gt_two
    hnEven hn2 q hq hpoly

end GleasonS2Bridge
