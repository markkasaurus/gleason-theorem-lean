import Gleason.Harmonic.Sphere.S2L2ToContinuous
import Gleason.Harmonic.Sphere.S2L2Odd
import Gleason.Harmonic.Sphere.SphereDegreeProjection
import Gleason.Harmonic.Zonal.NorthZonalEquation
import Gleason.Harmonic.Sphere.S2FinalWitnessReduction

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

theorem continuousSphereFrameSubmoduleS2_eq_lowSectorS2_of_even_sector_intersections_bot
    (hbotEven : ∀ n : ℕ, Even n → n ≠ 0 → n ≠ 2 →
      continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n = ⊥) :
    continuousSphereFrameSubmoduleS2 = lowSectorS2 := by
  apply continuousSphereFrameSubmoduleS2_eq_lowSectorS2_of_sector_intersections_bot
  intro n hn0 hn2
  by_cases hnodd : Odd n
  · exact continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_odd hnodd
  · exact hbotEven n (Nat.not_odd_iff_even.mp hnodd) hn0 hn2

theorem continuousSphereFrameSubmoduleS2_eq_lowSectorS2_of_no_northFixed_pointConstraint_witness_even
    (hwitness :
      ∀ n : ℕ, Even n → n ≠ 0 → n ≠ 2 →
        ¬ ∃ g : C(S2, ℝ),
          g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
          g ∈ northFixedSubmodule ∧
          ambientSectorProjectionContinuous n g =
            ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    continuousSphereFrameSubmoduleS2 = lowSectorS2 := by
  apply continuousSphereFrameSubmoduleS2_eq_lowSectorS2_of_even_sector_intersections_bot
  intro n hnEven hn0 hn2
  exact
    continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_no_northFixed_pointConstraint_witness
      (hwitness n hnEven hn0 hn2)

theorem continuousSphereFrameSubmoduleS2_eq_lowSectorS2_of_special_pointConstraint_zero_even
    (hspecial :
      ∀ n : ℕ, Even n → n ≠ 0 → n ≠ 2 →
        ∀ g : C(S2, ℝ),
          g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 →
          g ∈ northFixedSubmodule →
          ambientSectorProjectionContinuous n g =
            ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) →
          ∀ r : Set.Icc (0 : ℝ) 1,
            greatCirclePointConstraintLinear
              (specialXPoint r) sphereE2 (specialZPoint r)
              (specialXPoint_inner_sphereE2 r)
              (specialXPoint_inner_specialZPoint r)
              (sphereE2_inner_specialZPoint r)
              (harmonicDegreeProjectionContinuous n (s2Pullback g)) = 0) :
    continuousSphereFrameSubmoduleS2 = lowSectorS2 := by
  apply continuousSphereFrameSubmoduleS2_eq_lowSectorS2_of_even_sector_intersections_bot
  intro n hnEven hn0 hn2
  have hn2lt : 2 < n := by
    rcases hnEven with ⟨k, rfl⟩
    omega
  exact
    continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_special_pointConstraint_zero
      hn0 hnEven hn2lt (hspecial n hnEven hn0 hn2)

end GleasonS2Bridge
