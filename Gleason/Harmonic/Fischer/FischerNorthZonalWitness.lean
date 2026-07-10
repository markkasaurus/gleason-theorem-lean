import Gleason.Harmonic.Fischer.FischerNorthOrbit
import Gleason.Harmonic.Zonal.NorthZonalReduction
import Gleason.Harmonic.Zonal.NorthZonalClosed

noncomputable section

open Complex InnerProductSpace

theorem exists_nonzero_northZonal_mem_harmonicPolyHomogeneousImageSubmodule_of_north_nonzero
    {n : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule n)
    (hf_north : f sphereE3 ≠ 0) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ harmonicPolyHomogeneousImageSubmodule n ∧
      g ≠ 0 ∧
      IsNorthZonal g := by
  refine ⟨northOrbitAverage f,
    northOrbitAverage_mem_harmonicPolyHomogeneousImageSubmodule hf,
    northOrbitAverage_ne_zero_of_sphereE3_ne_zero hf_north,
    northOrbitAverage_isNorthZonal f⟩

theorem northOrbitAverage_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule) :
    northOrbitAverage f ∈ continuousSphereFrameSubmodule := by
  have hclosed : IsClosed (continuousSphereFrameSubmodule : Set C(spherePoint3, ℝ)) :=
    isClosed_continuousSphereFrameSubmodule
  have hinv :
      ∀ t : ℝ,
        continuousSphereFrameSubmodule ≤
          continuousSphereFrameSubmodule.comap (spherePrecomp (northRotation t)) := by
    intro t
    exact continuousSphereFrameSubmodule_invariant_under_spherePrecomp (northRotation t)
  exact northOrbitAverage_mem_of_isClosed_of_invariant hclosed hinv hf

theorem exists_nonzero_northZonal_mem_harmonicPolyHomogeneousImageSubmodule_and_frame_of_north_nonzero
    {n : ℕ} {f : C(spherePoint3, ℝ)}
    (hfH : f ∈ harmonicPolyHomogeneousImageSubmodule n)
    (hfF : f ∈ continuousSphereFrameSubmodule)
    (hf_north : f sphereE3 ≠ 0) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ harmonicPolyHomogeneousImageSubmodule n ∧
      g ∈ continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g := by
  refine ⟨northOrbitAverage f,
    northOrbitAverage_mem_harmonicPolyHomogeneousImageSubmodule hfH,
    northOrbitAverage_mem_continuousSphereFrameSubmodule hfF,
    northOrbitAverage_ne_zero_of_sphereE3_ne_zero hf_north,
    northOrbitAverage_isNorthZonal f⟩
