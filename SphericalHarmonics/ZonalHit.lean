import SphericalHarmonics.ZonalFixed
import SphericalHarmonics.CyclicLineCriterion
import Gleason.Harmonic.Sphere.SphericalSectorProjection

noncomputable section

namespace SphericalHarmonics

/-- The north-axis fixed slice inside the continuous degree-`n` sector. -/
def northFixedSector (n : ℕ) : Submodule ℝ (sector n) :=
  northFixedSubmodule.comap (sector n).subtypeL

@[simp] theorem mem_northFixedSector_iff {n : ℕ} {f : sector n} :
    f ∈ northFixedSector n ↔ ((f : C(S2, ℝ)) ∈ northFixedSubmodule) := by
  rfl

theorem exists_nonzero_mem_inf_northFixedSector_of_isRotationInvariant_of_ne_bot
    {n : ℕ} {W : Submodule ℝ (sector n)}
    (hWrot : SectorContinuousSubmodule.IsRotationInvariant n W)
    (hWne : W ≠ ⊥) :
    ∃ f : sector n, f ∈ W ⊓ northFixedSector n ∧ f ≠ 0 := by
  rcases exists_nonzero_mem_inf_northFixed_of_isRotationInvariant_of_ne_bot hWrot hWne with
    ⟨f, hfW, hf0, hffix⟩
  exact ⟨f, ⟨hfW, hffix⟩, hf0⟩

@[simp] theorem sectorToSectorL2_compContinuous
    (ρ : Rotation) (n : ℕ) (f : sector n) :
    sectorToSectorL2 n
        ⟨Rotation.compContinuous ρ f.1, compContinuous_mem_sector ρ n f.2⟩ =
      sectorCompL2Rotation ρ.symm n (sectorToSectorL2 n f) := by
  apply Subtype.ext
  simpa [sectorToSectorL2, sectorCompL2Rotation] using
    (continuousToLp_compContinuous_symm ρ.symm f.1).symm

theorem comap_sectorToSectorL2_isRotationInvariant
    {n : ℕ} {W : Submodule ℝ (sectorL2 n)}
    (hW : SectorSubmodule.IsRotationInvariant n W) :
    SectorContinuousSubmodule.IsRotationInvariant n (W.comap (sectorToSectorL2 n)) := by
  intro ρ x hx
  rw [Submodule.mem_comap] at hx ⊢
  simpa [sectorToSectorL2_compContinuous] using hW ρ.symm (sectorToSectorL2 n x) hx

theorem comap_sectorToSectorL2_ne_bot_of_ne_bot
    {n : ℕ} {W : Submodule ℝ (sectorL2 n)}
    (hWne : W ≠ ⊥) :
    W.comap (sectorToSectorL2 n) ≠ ⊥ := by
  intro hbot
  apply hWne
  rw [Submodule.eq_bot_iff] at hbot ⊢
  intro y hy
  rcases sectorToSectorL2_surjective n y with ⟨x, rfl⟩
  have hx : x ∈ W.comap (sectorToSectorL2 n) := hy
  simpa using congrArg (sectorToSectorL2 n) (hbot x hx)

/-- The north-axis fixed slice transported to the `L²` degree-`n` sector. -/
def northFixedSectorL2 (n : ℕ) : Submodule ℝ (sectorL2 n) :=
  Submodule.map (sectorToSectorL2 n) (northFixedSector n)

theorem exists_nonzero_mem_inf_northFixedSectorL2_of_isRotationInvariant_of_ne_bot
    {n : ℕ} {W : Submodule ℝ (sectorL2 n)}
    (hWrot : SectorSubmodule.IsRotationInvariant n W)
    (hWne : W ≠ ⊥) :
    ∃ u : sectorL2 n, u ∈ W ⊓ northFixedSectorL2 n ∧ u ≠ 0 := by
  let Wc : Submodule ℝ (sector n) := W.comap (sectorToSectorL2 n)
  have hWcrot : SectorContinuousSubmodule.IsRotationInvariant n Wc :=
    comap_sectorToSectorL2_isRotationInvariant hWrot
  have hWcne : Wc ≠ ⊥ :=
    comap_sectorToSectorL2_ne_bot_of_ne_bot hWne
  rcases exists_nonzero_mem_inf_northFixedSector_of_isRotationInvariant_of_ne_bot hWcrot hWcne with
    ⟨f, hf, hf0⟩
  refine ⟨sectorToSectorL2 n f, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact hf.1
    · exact ⟨f, hf.2, rfl⟩
  · intro hu0
    apply hf0
    exact sectorToSectorL2_injective n hu0

theorem exists_mem_northFixedSectorL2_ne_zero_of_ne_bot
    (n : ℕ) (hne : northFixedSectorL2 n ≠ ⊥) :
    ∃ u : sectorL2 n, u ∈ northFixedSectorL2 n ∧ u ≠ 0 := by
  by_contra h
  apply hne
  rw [Submodule.eq_bot_iff]
  intro u hu
  by_contra hu0
  exact h ⟨u, hu, hu0⟩

/-- A chosen nonzero vector in the north-axis fixed slice of `sectorL2 n`. -/
noncomputable def distinguishedZonalVector (n : ℕ)
    (hne : northFixedSectorL2 n ≠ ⊥) : sectorL2 n :=
  Classical.choose (exists_mem_northFixedSectorL2_ne_zero_of_ne_bot n hne)

theorem distinguishedZonalVector_mem (n : ℕ)
    (hne : northFixedSectorL2 n ≠ ⊥) :
    distinguishedZonalVector n hne ∈ northFixedSectorL2 n :=
  (Classical.choose_spec (exists_mem_northFixedSectorL2_ne_zero_of_ne_bot n hne)).1

theorem distinguishedZonalVector_ne_zero (n : ℕ)
    (hne : northFixedSectorL2 n ≠ ⊥) :
    distinguishedZonalVector n hne ≠ 0 := by
  exact (Classical.choose_spec (exists_mem_northFixedSectorL2_ne_zero_of_ne_bot n hne)).2

/-- The candidate distinguished zonal line in the degree-`n` `L²` sector. -/
def distinguishedZonalLine (n : ℕ) (hne : northFixedSectorL2 n ≠ ⊥) :
    Submodule ℝ (sectorL2 n) :=
  cyclicLine (distinguishedZonalVector n hne)

theorem distinguishedZonalLine_le_northFixedSectorL2
    (n : ℕ) (hne : northFixedSectorL2 n ≠ ⊥) :
    distinguishedZonalLine n hne ≤ northFixedSectorL2 n := by
  refine Submodule.span_le.mpr ?_
  intro u hu
  rcases Set.mem_singleton_iff.mp hu with rfl
  exact distinguishedZonalVector_mem n hne

theorem distinguishedZonalLine_hit_of_eq_northFixedSectorL2
    {n : ℕ} (hne : northFixedSectorL2 n ≠ ⊥)
    (hline : distinguishedZonalLine n hne = northFixedSectorL2 n) :
    ∀ W : Submodule ℝ (sectorL2 n),
      SectorSubmodule.IsRotationInvariant n W →
      W ≠ ⊥ →
      distinguishedZonalLine n hne ⊓ W ≠ ⊥ := by
  intro W hWrot hWne
  rcases exists_nonzero_mem_inf_northFixedSectorL2_of_isRotationInvariant_of_ne_bot hWrot hWne with
    ⟨u, hu, hu0⟩
  intro hbot
  have hbot' : northFixedSectorL2 n ⊓ W = ⊥ := by
    simpa [hline] using hbot
  have hu' : u ∈ northFixedSectorL2 n ⊓ W := by
    simpa [Submodule.mem_inf, and_comm, and_left_comm, and_assoc] using hu
  have : u = 0 := by
    have hu'' : u ∈ (⊥ : Submodule ℝ (sectorL2 n)) := by
      simpa [hbot'] using hu'
    simpa [Submodule.mem_bot] using hu''
  exact hu0 this

theorem sectorRotationOrbitSpan_eq_top_of_distinguishedZonalLine_eq_northFixedSectorL2
    {n : ℕ} (hne : northFixedSectorL2 n ≠ ⊥)
    (hline : distinguishedZonalLine n hne = northFixedSectorL2 n) :
    sectorRotationOrbitSpan n (distinguishedZonalVector n hne) = ⊤ := by
  apply sectorRotationOrbitSpan_eq_top_of_cyclicLine_meets_every_nonzero_invariant_submodule
  exact distinguishedZonalLine_hit_of_eq_northFixedSectorL2 hne hline

end SphericalHarmonics
