import SphericalHarmonics.SectorProjectionInvariant

namespace SphericalHarmonics

/-- A closed `L²(S²)` subspace that is invariant under the geometric rotation action is the closure
of the sum of its harmonic-degree sectors. -/
theorem ClosedSubmodule.toSubmodule_eq_topologicalClosure_iSup_inf_sectorL2_of_isRotationInvariant
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K) :
    K.toSubmodule = (⨆ n : ℕ, K.toSubmodule ⊓ sectorL2 n).topologicalClosure :=
  ClosedSubmodule.toSubmodule_eq_topologicalClosure_iSup_inf_sectorL2 K
    (fun n _ hx =>
      ClosedSubmodule.sectorL2_starProjection_mem_of_isRotationInvariant K hK n hx)

end SphericalHarmonics
