import Gleason.Harmonic.Profile.SquaredProfileLowmodeAmbient

noncomputable section

open Complex InnerProductSpace

theorem highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereEvenSubmodule :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule ≤ continuousSphereEvenSubmodule := by
  intro f hf
  exact antipode_even_of_mem_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hf

theorem
    topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereEvenSubmodule :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ≤
      continuousSphereEvenSubmodule := by
  exact Submodule.topologicalClosure_minimal
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereEvenSubmodule
    isClosed_continuousSphereEvenSubmodule

theorem sphereEvenSymm_eq_of_mem_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure) :
    sphereEvenSymm f = f := by
  exact sphereEvenSymm_eq_of_mem_continuousSphereEvenSubmodule <|
    topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereEvenSubmodule hf

theorem antipode_even_of_mem_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure) :
    ∀ x : spherePoint3, f (sphereAntipode x) = f x := by
  exact
    topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereEvenSubmodule
      hf
