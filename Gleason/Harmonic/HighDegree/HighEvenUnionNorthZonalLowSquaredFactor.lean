import Gleason.Harmonic.HighDegree.HighEvenUnionClosed
import Gleason.Harmonic.HighDegree.HighEvenUnionNorthZonalLowSquaredProfileExact
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileFixedContinuousTame

noncomputable section

open Complex InnerProductSpace
open Polynomial
theorem mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotient_factor
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {q : C(unitIcc, ℝ)}
    (hq :
      ∀ u : Set.Icc (0 : ℝ) 1,
        sqCenteredNorthZonalProfile g u = u.1 * q u) :
    g ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
  have hfix :
      northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g) =
        sqCenteredNorthZonalContinuousMap g :=
    northZonalSqProfileAverage_sqCenteredNorthZonalContinuousMap_of_mem_frame hg.2 hgz
  have hsq :
      sqCenteredNorthZonalContinuousMap g =
        (C (q zeroUnitIcc) * X).toContinuousMapOn unitIcc :=
    northZonalSqProfileAverage_eq_linear_of_fixed_of_sqquotient_factor
      (sqCenteredNorthZonalContinuousMap g) hfix q <| by
        ext u
        simpa [sqCenteredNorthZonalContinuousMap, sqMulContinuousMap_apply] using hq u
  let p : ℝ[X] := C (q zeroUnitIcc) * X
  refine
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_eq_polynomial
      (q := p) hg hgz ?_
  intro u
  have hsq' := congrArg (fun r : C(unitIcc, ℝ) => r u) hsq
  simpa [p, sqCenteredNorthZonalContinuousMap, Polynomial.eval_C, Polynomial.eval_X] using hsq'
