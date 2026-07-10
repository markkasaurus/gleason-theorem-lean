import Gleason.Harmonic.Profile.SquaredProfilePoleAverage
import Gleason.Harmonic.Sphere.S2DistinguishedNorthZonal

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real

namespace GleasonS2Bridge

open SphericalHarmonics

theorem two_mul_poleAverageLinear_specialZPoint_sub_two_zero_eq_sqMul_northZonalSqQuotientAverage
    {f : C(spherePoint3, ℝ)}
    (hfz : IsNorthZonal f)
    (hanti : ∀ x : spherePoint3, f (sphereAntipode x) = f x)
    (q : C(unitIcc, ℝ))
    (hq : ∀ u : unitIcc, sqCenteredNorthZonalProfile f u = u.1 * q u)
    (r : Set.Icc (0 : ℝ) 1) :
    2 * poleAverageLinear f (specialZPoint r) - 2 * northZonalProfile f zeroIcc =
      (r.1 ^ 2) * northZonalSqQuotientAverage q
        ⟨r.1 ^ 2, sq_mem_Icc (nonnegIccToIcc r)⟩ := by
  let u : unitIcc := ⟨r.1 ^ 2, sq_mem_Icc (nonnegIccToIcc r)⟩
  have hu_eq : u.1 = r.1 ^ 2 := by
    rfl
  have hu :
      northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap f) u =
        2 * poleAverageLinear f (specialZPoint r) - 2 * northZonalProfile f zeroIcc := by
    calc
      northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap f) u
          =
            2 * poleAverageLinear f
              (specialZPoint
                ⟨Real.sqrt u.1, by
                  constructor
                  · exact Real.sqrt_nonneg u.1
                  · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
                      exact Real.sq_sqrt u.2.1
                    have hle : Real.sqrt u.1 ≤ 1 := by
                      nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
                    simpa using hle⟩) -
              2 * northZonalProfile f zeroIcc := by
                exact
                  northZonalSqProfileAverage_apply_eq_two_mul_poleAverageLinear_sub_zero_of_isNorthZonal_of_antipode_even
                    hfz hanti u
      _ =
            2 * poleAverageLinear f (specialZPoint r) -
              2 * northZonalProfile f zeroIcc := by
                have hs :
                    specialZPoint
                      ⟨Real.sqrt u.1, by
                        constructor
                        · exact Real.sqrt_nonneg u.1
                        · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
                            exact Real.sq_sqrt u.2.1
                          have hle : Real.sqrt u.1 ≤ 1 := by
                            nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
                          simpa using hle⟩ =
                    specialZPoint r := by
                  apply Subtype.ext
                  simp [specialZPoint, u, Real.sqrt_sq, r.2.1]
                simp [hs]
  calc
    2 * poleAverageLinear f (specialZPoint r) - 2 * northZonalProfile f zeroIcc
        = northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap f) u := by
            symm
            exact hu
    _ = northZonalSqProfileAverage (sqMulContinuousMap q) u := by
          have hsq :
              sqCenteredNorthZonalContinuousMap f = sqMulContinuousMap q := by
            ext v
            simpa [sqCenteredNorthZonalContinuousMap, sqMulContinuousMap_apply] using hq v
          simp [hsq]
    _ = sqMulContinuousMap (northZonalSqQuotientAverage q) u := by
          simpa using congrArg (fun g : C(unitIcc, ℝ) => g u)
            (northZonalSqProfileAverage_sqMulContinuousMap q)
    _ = (r.1 ^ 2) * northZonalSqQuotientAverage q u := by
          simp [sqMulContinuousMap_apply, hu_eq]

theorem exists_sqquotient_specialZ_bridge_of_even_distinguishedZonalSector
    {n : ℕ} (hnEven : Even n) :
    ∃ q : C(unitIcc, ℝ),
      ∀ r : Set.Icc (0 : ℝ) 1,
        2 * poleAverageLinear
            (s2Pullback
              (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))))
            (specialZPoint r) -
            2 * northZonalProfile
              (s2Pullback
                (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
                  C(S2, ℝ)))))
              zeroIcc =
          (r.1 ^ 2) * northZonalSqQuotientAverage q
            ⟨r.1 ^ 2, sq_mem_Icc (nonnegIccToIcc r)⟩ := by
  rcases exists_sqCenteredNorthZonalProfile_quotient_of_even_distinguishedZonalSector
      (n := n) hnEven with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  intro r
  refine
    two_mul_poleAverageLinear_specialZPoint_sub_two_zero_eq_sqMul_northZonalSqQuotientAverage
      (f :=
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))))
      (hfz := isNorthZonal_s2Pullback_distinguishedZonalSector n)
      ?_ q hq r
  intro x
  have hg :
      s2Pullback
        (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) ∈
          continuousHarmonicSphereDegreeSubmodule n :=
    s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule_distinguishedZonalSector n
  have hpow : (-1 : ℝ) ^ n = 1 := by
    rcases hnEven with ⟨k, hk⟩
    subst hk
    simp
  calc
    s2Pullback
        (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
        (sphereAntipode x)
      =
        (-1 : ℝ) ^ n *
          s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))
            x := by
              exact
                sphereRestriction_sphereNeg_of_mem_continuousHarmonicSphereDegreeSubmodule
                  hg x
    _ =
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
          x := by simp [hpow]

end GleasonS2Bridge
