import SphericalHarmonics.InvariantSubspace
import SphericalHarmonics.FiniteDimensional
import SphericalHarmonics.SectorOrthogonality

namespace SphericalHarmonics

/-- The `L²` space on `S²` built from the finite rotation-invariant surface measure
`rotationMeasure`. -/
noncomputable abbrev L2S2 := MeasureTheory.Lp ℝ 2 rotationMeasure

/-- If the actual continuous harmonic sectors are orthogonal in `L²`, then the corresponding `L²`
sectors form a Hilbert sum. Completeness is supplied by the all-degrees Fischer decomposition. -/
theorem sectorL2_isHilbertSum_of_orthogonal
    (horth : OrthogonalFamily ℝ (fun n : ℕ => sectorL2 n)
      fun n => (sectorL2 n).subtypeₗᵢ) :
    IsHilbertSum ℝ (fun n : ℕ => sectorL2 n) fun n => (sectorL2 n).subtypeₗᵢ := by
  refine IsHilbertSum.mkInternal (F := sectorL2) horth ?_
  rw [sectorL2_topologicalClosure_eq_top]

/-- The actual harmonic degree sectors on `L²(S²)` form a Hilbert sum once each sector is known to
be complete. Orthogonality is supplied by the concrete `L²` spherical-harmonic orthogonality
theorem. -/
theorem sectorL2_isHilbertSum
    : IsHilbertSum ℝ (fun n : ℕ => sectorL2 n) fun n => (sectorL2 n).subtypeₗᵢ :=
  sectorL2_isHilbertSum_of_orthogonal sectorL2_orthogonalFamily

/-- Closed subspaces of `L²(S²)` that are stable under the orthogonal projections onto the actual
harmonic degree sectors decompose as the closure of the sum of their sector intersections. -/
theorem ClosedSubmodule.toSubmodule_eq_topologicalClosure_iSup_inf_sectorL2_of_orthogonal
    (horth : OrthogonalFamily ℝ (fun n : ℕ => sectorL2 n)
      fun n => (sectorL2 n).subtypeₗᵢ)
    (K : ClosedSubmodule ℝ L2S2)
    (hK : ∀ n x, x ∈ K.toSubmodule →
      ((sectorL2 n).starProjection x : L2S2) ∈ K.toSubmodule) :
    K.toSubmodule = (⨆ n : ℕ, K.toSubmodule ⊓ sectorL2 n).topologicalClosure := by
  exact
    ClosedSubmodule.toSubmodule_eq_topologicalClosure_iSup_inf_of_isHilbertSum_projection_invariant
      (V := sectorL2)
      (sectorL2_isHilbertSum_of_orthogonal horth)
      K hK

/-- Closed subspaces of `L²(S²)` that are stable under the harmonic-sector projections decompose as
the closure of the sum of their sector intersections. This is the specialization of the abstract
Hilbert-sum theorem to the actual spherical-harmonic sector family. -/
theorem ClosedSubmodule.toSubmodule_eq_topologicalClosure_iSup_inf_sectorL2
    (K : ClosedSubmodule ℝ L2S2)
    (hK : ∀ n x, x ∈ K.toSubmodule →
      ((sectorL2 n).starProjection x : L2S2) ∈ K.toSubmodule) :
    K.toSubmodule = (⨆ n : ℕ, K.toSubmodule ⊓ sectorL2 n).topologicalClosure :=
  ClosedSubmodule.toSubmodule_eq_topologicalClosure_iSup_inf_sectorL2_of_orthogonal
    sectorL2_orthogonalFamily K hK

end SphericalHarmonics
