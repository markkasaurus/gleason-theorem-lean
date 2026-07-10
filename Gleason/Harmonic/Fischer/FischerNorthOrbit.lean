import Gleason.Harmonic.Fischer.FischerNorthRotation
import Gleason.Harmonic.Zonal.NorthOrbitAverage
import Gleason.Harmonic.Zonal.NorthZonalClosed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalAverage

noncomputable section

open Complex InnerProductSpace MeasureTheory

instance harmonicPolyHomogeneousImageSubmodule_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (harmonicPolyHomogeneousImageSubmodule n) := by
  exact Submodule.finiteDimensional_of_le
    (harmonicPolyHomogeneousImageSubmodule_le_homogeneousImage n)

theorem isClosed_harmonicPolyHomogeneousImageSubmodule (n : ℕ) :
    IsClosed ((harmonicPolyHomogeneousImageSubmodule n : Submodule ℝ C(spherePoint3, ℝ)) :
      Set C(spherePoint3, ℝ)) := by
  exact Submodule.closed_of_finiteDimensional _

theorem northOrbitAverage_eq_intervalAverage (f : C(spherePoint3, ℝ)) :
    northOrbitAverage f = ⨍ t in 0..2 * Real.pi, spherePrecomp (northRotation t) f := by
  rw [northOrbitAverage, interval_average_eq]
  ring_nf

theorem northOrbitAverage_mem_harmonicPolyHomogeneousImageSubmodule
    {n : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule n) :
    northOrbitAverage f ∈ harmonicPolyHomogeneousImageSubmodule n := by
  let S : Submodule ℝ C(spherePoint3, ℝ) := harmonicPolyHomogeneousImageSubmodule n
  have hclosed : IsClosed (S : Set C(spherePoint3, ℝ)) :=
    isClosed_harmonicPolyHomogeneousImageSubmodule n
  have hinv :
      ∀ t : ℝ, S ≤ S.comap (spherePrecomp (northRotation t)) := by
    intro t g hg
    exact spherePrecomp_northRotation_mem_harmonicPolyHomogeneousImageSubmodule t hg
  exact northOrbitAverage_mem_of_isClosed_of_invariant hclosed hinv hf

theorem exists_nonzero_northOrbitAverage_mem_harmonicPolyHomogeneousImageSubmodule
    {n : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule n)
    (hf_north : f sphereE3 ≠ 0) :
    northOrbitAverage f ∈ harmonicPolyHomogeneousImageSubmodule n ∧
      northOrbitAverage f ≠ 0 := by
  exact ⟨northOrbitAverage_mem_harmonicPolyHomogeneousImageSubmodule hf,
    northOrbitAverage_ne_zero_of_sphereE3_ne_zero hf_north⟩
