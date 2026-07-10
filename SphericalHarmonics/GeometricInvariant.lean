import SphericalHarmonics.RotationInvariant

namespace SphericalHarmonics

/-- The `L²` space on `S²` for the rotation-invariant surface measure. -/
noncomputable abbrev L2S2Geom := MeasureTheory.Lp ℝ 2 rotationMeasure

namespace ClosedSubmodule

/-- A closed subspace of `L²(S²)` is rotation-invariant if it is stable under the geometric
rotation action. -/
def IsRotationInvariant (K : ClosedSubmodule ℝ L2S2Geom) : Prop :=
  ∀ ρ : Rotation, ∀ x, x ∈ K.toSubmodule → Rotation.compL2Rotation ρ x ∈ K.toSubmodule

instance (K : ClosedSubmodule ℝ L2S2Geom) : CompleteSpace K.toSubmodule :=
  K.isClosed.completeSpace_coe

theorem toSubmodule_map_compL2Rotation_eq
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : IsRotationInvariant K) (ρ : Rotation) :
    K.toSubmodule.map (Rotation.compL2Rotation ρ).toLinearMap = K.toSubmodule := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hK ρ y hy
  · intro x hx
    refine ⟨Rotation.compL2Rotation ρ.symm x, hK ρ.symm x hx, ?_⟩
    exact compL2Rotation_compL2Rotation_symm_apply ρ x

theorem starProjection_compL2Rotation_apply
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : IsRotationInvariant K) (ρ : Rotation) (x : L2S2Geom) :
    K.toSubmodule.starProjection (Rotation.compL2Rotation ρ x) =
      Rotation.compL2Rotation ρ (K.toSubmodule.starProjection x) := by
  have hmap : Submodule.map (Rotation.compL2Rotation ρ) K.toSubmodule = K.toSubmodule := by
    simpa using toSubmodule_map_compL2Rotation_eq K hK ρ
  simpa [hmap] using
    (LinearIsometry.map_starProjection'
      (f := Rotation.compL2Rotation ρ) (p := K.toSubmodule) x).symm

theorem orthogonal_isRotationInvariant
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : IsRotationInvariant K) :
    IsRotationInvariant K.toSubmoduleᗮ.closure := by
  intro ρ x hx
  have hcl : K.toSubmoduleᗮ.closure = K.toSubmoduleᗮ :=
    K.toSubmodule.isClosed_orthogonal.submodule_topologicalClosure_eq
  rw [hcl] at hx ⊢
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  let z : L2S2Geom := Rotation.compL2Rotation ρ.symm y
  have hz : z ∈ K.toSubmodule := hK ρ.symm y hy
  have hyz : Rotation.compL2Rotation ρ z = y := by
    simpa [z] using compL2Rotation_compL2Rotation_symm_apply ρ y
  calc
    inner ℝ (Rotation.compL2Rotation ρ x) y
        = inner ℝ (Rotation.compL2Rotation ρ x) (Rotation.compL2Rotation ρ z) := by
            simpa [hyz]
    _ = inner ℝ x z := by
            exact (Rotation.compL2Rotation ρ).inner_map_map x z
    _ = 0 := hx z hz

end ClosedSubmodule

end SphericalHarmonics
