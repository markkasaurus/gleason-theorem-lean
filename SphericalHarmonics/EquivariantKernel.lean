import SphericalHarmonics.GeometricDecomposition

namespace SphericalHarmonics

namespace ContinuousLinearMap

/-- A continuous linear endomorphism of `L²(S²)` is rotation-equivariant if it commutes with the
geometric rotation action. -/
def IsRotationEquivariant (T : L2S2Geom →L[ℝ] L2S2Geom) : Prop :=
  ∀ (ρ : Rotation) (x : L2S2Geom),
    T (Rotation.compL2Rotation ρ x) = Rotation.compL2Rotation ρ (T x)

/-- The closed kernel of a continuous linear endomorphism of `L²(S²)`. -/
def closedKer (T : L2S2Geom →L[ℝ] L2S2Geom) : ClosedSubmodule ℝ L2S2Geom :=
  ClosedSubmodule.comap T ⊥

@[simp] theorem mem_closedKer_iff (T : L2S2Geom →L[ℝ] L2S2Geom) (x : L2S2Geom) :
    x ∈ (closedKer T).toSubmodule ↔ T x = 0 := by
  simp [closedKer]

@[simp] theorem closedKer_toSubmodule (T : L2S2Geom →L[ℝ] L2S2Geom) :
    (closedKer T).toSubmodule = LinearMap.ker T := by
  ext x
  simp [closedKer]

theorem closedKer_isRotationInvariant (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hT : IsRotationEquivariant T) :
    ClosedSubmodule.IsRotationInvariant (closedKer T) := by
  intro ρ x hx
  rw [mem_closedKer_iff] at hx ⊢
  calc
    T (Rotation.compL2Rotation ρ x)
        = Rotation.compL2Rotation ρ (T x) := hT ρ x
    _ = 0 := by simp [hx]

theorem sectorL2_starProjection_mem_closedKer (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hT : IsRotationEquivariant T) (n : ℕ) {x : L2S2Geom}
    (hx : x ∈ (closedKer T).toSubmodule) :
    (sectorL2 n).starProjection x ∈ (closedKer T).toSubmodule := by
  exact
    ClosedSubmodule.sectorL2_starProjection_mem_of_isRotationInvariant
      (closedKer T) (closedKer_isRotationInvariant T hT) n hx

/-- The kernel of a rotation-equivariant operator decomposes as the closure of the sum of its
harmonic-degree intersections. -/
theorem closedKer_eq_topologicalClosure_iSup_inf_sectorL2
    (T : L2S2Geom →L[ℝ] L2S2Geom) (hT : IsRotationEquivariant T) :
    (closedKer T).toSubmodule =
      (⨆ n : ℕ, (closedKer T).toSubmodule ⊓ sectorL2 n).topologicalClosure := by
  exact
    ClosedSubmodule.toSubmodule_eq_topologicalClosure_iSup_inf_sectorL2_of_isRotationInvariant
      (closedKer T) (closedKer_isRotationInvariant T hT)

end ContinuousLinearMap

end SphericalHarmonics
