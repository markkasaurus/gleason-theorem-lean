import SphericalHarmonics.CyclicIrreducibility
import SphericalHarmonics.EquivariantKernel

noncomputable section
set_option synthInstance.maxHeartbeats 300000

namespace SphericalHarmonics

namespace SectorEndomorphism

/-- A continuous endomorphism of a fixed harmonic sector is rotation-equivariant if it commutes
with the restricted rotation action. -/
def IsRotationEquivariant {n : ℕ} (A : sectorL2 n →L[ℝ] sectorL2 n) : Prop :=
  ∀ (ρ : Rotation) (x : sectorL2 n),
    A (sectorCompL2Rotation ρ n x) = sectorCompL2Rotation ρ n (A x)

/-- Scalar multiples of the identity on a fixed harmonic sector. -/
def scalarId (n : ℕ) (a : ℝ) : sectorL2 n →L[ℝ] sectorL2 n :=
  a • ContinuousLinearMap.id ℝ (sectorL2 n)

/-- Restriction of an ambient operator to a fixed harmonic sector, given sector preservation. -/
def restrictToSector (n : ℕ) (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hT : ∀ ⦃x : L2S2Geom⦄, x ∈ sectorL2 n → T x ∈ sectorL2 n) :
    sectorL2 n →L[ℝ] sectorL2 n where
  toFun x := ⟨T x, hT x.2⟩
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

theorem restrictToSector_isRotationEquivariant
    {n : ℕ} (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hTrot : ContinuousLinearMap.IsRotationEquivariant T)
    (hT : ∀ ⦃x : L2S2Geom⦄, x ∈ sectorL2 n → T x ∈ sectorL2 n) :
    IsRotationEquivariant (restrictToSector n T hT) := by
  intro ρ x
  apply Subtype.ext
  simpa [restrictToSector] using hTrot ρ (x : L2S2Geom)

theorem eq_smul_on_orbit_of_eq_smul
    {n : ℕ} {A : sectorL2 n →L[ℝ] sectorL2 n} (hA : IsRotationEquivariant A)
    {u : sectorL2 n} {a : ℝ} (hau : A u = a • u) (ρ : Rotation) :
    A (sectorCompL2Rotation ρ n u) = a • sectorCompL2Rotation ρ n u := by
  calc
    A (sectorCompL2Rotation ρ n u)
        = sectorCompL2Rotation ρ n (A u) := hA ρ u
    _ = a • sectorCompL2Rotation ρ n u := by simp [hau]

theorem eq_smul_id_of_eq_smul_on_cyclic
    {n : ℕ} {A : sectorL2 n →L[ℝ] sectorL2 n} (hA : IsRotationEquivariant A)
    {u : sectorL2 n} (hcyc : sectorRotationOrbitSpan n u = ⊤)
    {a : ℝ} (hau : A u = a • u) :
    A = scalarId n a := by
  let B : sectorL2 n →ₗ[ℝ] sectorL2 n := A.toLinearMap - (scalarId n a).toLinearMap
  have horbit :
      sectorRotationOrbitSpan n u ≤ LinearMap.ker B := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with ⟨ρ, rfl⟩
    change B (sectorCompL2Rotation ρ n u) = 0
    simp [B, scalarId, eq_smul_on_orbit_of_eq_smul hA hau ρ]
  have hker_top : (⊤ : Submodule ℝ (sectorL2 n)) ≤ LinearMap.ker B := by
    simpa [hcyc] using horbit
  have hker_eq_top : LinearMap.ker B = ⊤ := top_unique hker_top
  have hlin_zero : B = 0 := LinearMap.ker_eq_top.mp hker_eq_top
  have hlin_eq : A.toLinearMap = (scalarId n a).toLinearMap := by
    exact sub_eq_zero.mp (by simpa [B] using hlin_zero)
  exact ContinuousLinearMap.coe_injective (by simpa using hlin_eq)

end SectorEndomorphism

end SphericalHarmonics
