import Gleason.Harmonic.HighDegree.HighEvenUnionEvenClosure

noncomputable section

open Complex InnerProductSpace Polynomial

theorem norm_sub_lowSqProfileMode_eq_sqprofile_of_mem_topologicalClosure_highEvenUnion_of_isNorthZonal
    {g : C(spherePoint3, ℝ)} {b : ℝ}
    (hg : g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure)
    (hgz : IsNorthZonal g) :
    ‖g - lowSqProfileMode (g sphereE1) b‖ =
      ‖sqCenteredNorthZonalContinuousMap g - (C b * X).toContinuousMapOn unitIcc‖ := by
  exact
    norm_sub_lowSqProfileMode_eq_sqprofile_of_isNorthZonal_of_antipode_even
      (hhz := hgz)
      (hheven := antipode_even_of_mem_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hg)

theorem norm_sub_lowSqProfileMode_eq_sqprofile_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)} {b : ℝ}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ‖g - lowSqProfileMode (g sphereE1) b‖ =
      ‖sqCenteredNorthZonalContinuousMap g - (C b * X).toContinuousMapOn unitIcc‖ := by
  exact
    norm_sub_lowSqProfileMode_eq_sqprofile_of_mem_topologicalClosure_highEvenUnion_of_isNorthZonal
      (hg := hg.1) (hgz := hgz)
