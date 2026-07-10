import Gleason.Harmonic.Sphere.S2NorthZonalBridge
import Gleason.Harmonic.Zonal.NorthZonalSquaredFactorBridge
import Gleason.Harmonic.Zonal.NorthFixedMeridian

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics
open GleasonNorthFixed

theorem distinguishedZonalSector_ne_zero (n : ℕ) :
    ((distinguishedZonalSector n : northFixedSector n) : sector n) ≠ 0 := by
  intro hz
  have hz' : (distinguishedZonalSector n : northFixedSector n) = 0 := by
    apply Subtype.ext
    exact hz
  have hL2 :
      ((northFixedSectorToNorthFixedSectorL2Equiv n).toLinearMap)
        (distinguishedZonalSector n) = 0 := by
    rw [hz']
    exact map_zero _
  have hvec :
      (⟨distinguishedZonalVector n (northFixedSectorL2_ne_bot n),
        distinguishedZonalVector_mem n (northFixedSectorL2_ne_bot n)⟩ :
        northFixedSectorL2 n) = 0 := by
    simpa [distinguishedZonalSector] using hL2
  have hvec0 :
      distinguishedZonalVector n (northFixedSectorL2_ne_bot n) = 0 := by
    exact congrArg Subtype.val hvec
  exact distinguishedZonalVector_ne_zero n (northFixedSectorL2_ne_bot n) hvec0

theorem s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule_distinguishedZonalSector
    (n : ℕ) :
    s2Pullback
      (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) ∈
        continuousHarmonicSphereDegreeSubmodule n := by
  exact s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule
    (((distinguishedZonalSector n : northFixedSector n) : sector n).property)

theorem exists_sqCenteredNorthZonalProfile_quotient_of_even_distinguishedZonalSector
    {n : ℕ} (hnEven : Even n) :
    ∃ q : C(unitIcc, ℝ),
      ∀ u : unitIcc,
        sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ)))))
            u =
          u.1 * q u := by
  apply exists_sqCenteredNorthZonalProfile_quotient_of_even_mem_continuousHarmonicSphereDegreeSubmodule
  · exact
      s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule_distinguishedZonalSector n
  · exact isNorthZonal_s2Pullback_distinguishedZonalSector n
  · exact hnEven

theorem exists_nonzero_northMeridianPolynomial_of_distinguishedZonalSector
    (n : ℕ) :
    ∃ p : harmonicHomogeneousSubmodule n,
      restrictToSphere p.1 =
        (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) ∧
      northMeridianPolynomial p.1 ≠ 0 := by
  rcases exists_fixed_ambientRepresentative_of_mem_northFixedSector
      ((distinguishedZonalSector n).property) with ⟨p, hpRes, hpFix⟩
  refine ⟨p, hpRes, ?_⟩
  have hpNorth : p.1 ∈ northFixedAmbientHarmonicSubmodule n := by
    refine ⟨p.2, ?_⟩
    simpa using hpFix
  have hp0 : p.1 ≠ 0 := by
    intro hpz
    have hpSub : p = 0 := by
      apply restrictToSphere_injective_on_harmonicHomogeneousSubmodule n
      simpa [hpz] using hpRes
    have hdz :
        (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) = 0 := by
      simpa [hpSub] using hpRes.symm
    exact distinguishedZonalSector_ne_zero n <| Subtype.ext hdz
  exact northMeridianPolynomial_ne_zero_of_mem_northFixedAmbientHarmonicSubmodule hpNorth hp0

end GleasonS2Bridge
