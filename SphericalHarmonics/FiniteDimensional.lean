import SphericalHarmonics.Density

namespace SphericalHarmonics

noncomputable instance finiteDimensional_homogeneousSubmodule (n : ℕ) :
    FiniteDimensional ℝ (homogeneousSubmodule n) :=
  homogeneousSubmodule_moduleFinite n

noncomputable instance finiteDimensional_harmonicHomogeneousSubmodule (n : ℕ) :
    FiniteDimensional ℝ (harmonicHomogeneousSubmodule n) :=
  Submodule.finiteDimensional_of_le (inf_le_left : harmonicHomogeneousSubmodule n ≤ homogeneousSubmodule n)

/-- Restriction to the sphere, with codomain restricted to the degree-`n` sector. -/
noncomputable def restrictToSector (n : ℕ) :
    harmonicHomogeneousSubmodule n →ₗ[ℝ] sector n where
  toFun p := ⟨restrictToSphere p.1, ⟨p.1, p.2, rfl⟩⟩
  map_add' p q := by
    ext x
    simp
  map_smul' a p := by
    ext x
    simp

theorem restrictToSector_surjective (n : ℕ) :
    Function.Surjective (restrictToSector n) := by
  intro f
  rcases f.2 with ⟨p, hp, hpf⟩
  refine ⟨⟨p, hp⟩, ?_⟩
  exact Subtype.ext hpf

noncomputable instance finiteDimensional_sector (n : ℕ) :
    FiniteDimensional ℝ (sector n) :=
  FiniteDimensional.of_surjective (restrictToSector n) (restrictToSector_surjective n)

/-- The canonical map from the continuous degree-`n` sector to the corresponding `L²` sector. -/
noncomputable def sectorToSectorL2 (n : ℕ) :
    sector n →ₗ[ℝ] sectorL2 n where
  toFun f := ⟨continuousToLp f.1, ⟨f.1, f.2, rfl⟩⟩
  map_add' f g := by
    ext
    rfl
  map_smul' a f := by
    ext
    rfl

theorem sectorToSectorL2_surjective (n : ℕ) :
    Function.Surjective (sectorToSectorL2 n) := by
  intro f
  rcases f.2 with ⟨g, hg, hgf⟩
  refine ⟨⟨g, hg⟩, ?_⟩
  exact Subtype.ext hgf

noncomputable instance finiteDimensional_sectorL2 (n : ℕ) :
    FiniteDimensional ℝ (sectorL2 n) :=
  FiniteDimensional.of_surjective (sectorToSectorL2 n) (sectorToSectorL2_surjective n)

noncomputable instance completeSpace_sectorL2 (n : ℕ) :
    CompleteSpace (sectorL2 n) :=
  FiniteDimensional.complete ℝ (sectorL2 n)

end SphericalHarmonics
