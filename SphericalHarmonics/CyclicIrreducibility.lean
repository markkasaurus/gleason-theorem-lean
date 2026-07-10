import SphericalHarmonics.SectorProjectionInvariant

noncomputable section

namespace SphericalHarmonics

/-- The orbit span of a vector in the degree-`n` harmonic sector under the rotation action. -/
def sectorRotationOrbitSpan (n : ℕ) (u : sectorL2 n) : Submodule ℝ (sectorL2 n) :=
  Submodule.span ℝ (Set.range fun ρ : Rotation => sectorCompL2Rotation ρ n u)

/-- A submodule of a fixed harmonic degree sector is rotation-invariant if it is stable under the
restricted rotation action. -/
def SectorSubmodule.IsRotationInvariant (n : ℕ) (W : Submodule ℝ (sectorL2 n)) : Prop :=
  ∀ (ρ : Rotation) (x : sectorL2 n), x ∈ W → sectorCompL2Rotation ρ n x ∈ W

/-- The sector-valued points of a closed rotation-invariant ambient subspace. -/
def sectorSubmoduleInClosed (K : ClosedSubmodule ℝ L2S2Geom) (n : ℕ) :
    Submodule ℝ (sectorL2 n) :=
  K.toSubmodule.comap (sectorL2 n).subtypeL

@[simp] theorem mem_sectorSubmoduleInClosed_iff
    (K : ClosedSubmodule ℝ L2S2Geom) (n : ℕ) (x : sectorL2 n) :
    x ∈ sectorSubmoduleInClosed K n ↔ (x : L2S2Geom) ∈ K.toSubmodule := by
  simp [sectorSubmoduleInClosed]

theorem sectorRotationOrbitSpan_le_of_mem_of_isRotationInvariant
    {n : ℕ} {W : Submodule ℝ (sectorL2 n)}
    (hW : SectorSubmodule.IsRotationInvariant n W) {u : sectorL2 n} (hu : u ∈ W) :
    sectorRotationOrbitSpan n u ≤ W := by
  refine Submodule.span_le.mpr ?_
  intro x hx
  rcases hx with ⟨ρ, rfl⟩
  simpa using hW ρ u hu

theorem eq_top_of_mem_of_orbitSpan_eq_top
    {n : ℕ} {W : Submodule ℝ (sectorL2 n)}
    (hW : SectorSubmodule.IsRotationInvariant n W) {u : sectorL2 n} (hu : u ∈ W)
    (hcyc : sectorRotationOrbitSpan n u = ⊤) :
    W = ⊤ := by
  apply top_unique
  simpa [hcyc] using sectorRotationOrbitSpan_le_of_mem_of_isRotationInvariant hW hu

theorem sectorSubmoduleInClosed_isRotationInvariant
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K) (n : ℕ) :
    SectorSubmodule.IsRotationInvariant n (sectorSubmoduleInClosed K n) := by
  intro ρ x hx
  rw [mem_sectorSubmoduleInClosed_iff] at hx ⊢
  exact hK ρ x hx

theorem sectorSubmoduleInClosed_eq_top_of_mem_of_orbitSpan_eq_top
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    {n : ℕ} {u : sectorL2 n} (hu : (u : L2S2Geom) ∈ K.toSubmodule)
    (hcyc : sectorRotationOrbitSpan n u = ⊤) :
    sectorSubmoduleInClosed K n = ⊤ := by
  exact
    eq_top_of_mem_of_orbitSpan_eq_top
      (sectorSubmoduleInClosed_isRotationInvariant K hK n)
      ((mem_sectorSubmoduleInClosed_iff K n u).2 hu) hcyc

theorem sectorL2_le_of_mem_of_orbitSpan_eq_top
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    {n : ℕ} {u : sectorL2 n} (hu : (u : L2S2Geom) ∈ K.toSubmodule)
    (hcyc : sectorRotationOrbitSpan n u = ⊤) :
    sectorL2 n ≤ K.toSubmodule := by
  intro x hx
  have htop : sectorSubmoduleInClosed K n = ⊤ :=
    sectorSubmoduleInClosed_eq_top_of_mem_of_orbitSpan_eq_top K hK hu hcyc
  have hx' : (⟨x, hx⟩ : sectorL2 n) ∈ sectorSubmoduleInClosed K n := by
    simp [htop]
  exact (mem_sectorSubmoduleInClosed_iff K n ⟨x, hx⟩).1 hx'

end SphericalHarmonics
