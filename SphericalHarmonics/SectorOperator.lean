import SphericalHarmonics.CyclicSchur
import SphericalHarmonics.CrossSchur
import SphericalHarmonics.SectorDimension
import SphericalHarmonics.SectorProjectionInvariant

noncomputable section
set_option synthInstance.maxHeartbeats 300000

namespace SphericalHarmonics

namespace ContinuousLinearMap

/-- An ambient operator on `L²(S²)` preserves the degree-`n` sector if it maps that sector into
itself. -/
def PreservesSector (T : L2S2Geom →L[ℝ] L2S2Geom) (n : ℕ) : Prop :=
  ∀ ⦃x : L2S2Geom⦄, x ∈ sectorL2 n → T x ∈ sectorL2 n

/-- The `(m,n)` harmonic block of an ambient `L²(S²)` operator. -/
noncomputable def sectorBlock (T : L2S2Geom →L[ℝ] L2S2Geom) (m n : ℕ) :
    sectorL2 m →L[ℝ] sectorL2 n :=
  (sectorL2 n).orthogonalProjection ∘L T ∘L (sectorL2 m).subtypeL

@[simp] theorem sectorBlock_coe_apply
    (T : L2S2Geom →L[ℝ] L2S2Geom) (m n : ℕ) (u : sectorL2 m) :
    ((sectorBlock T m n u : sectorL2 n) : L2S2Geom) =
      (sectorL2 n).starProjection (T u.1) := rfl

theorem sectorBlock_isRotationEquivariant
    {T : L2S2Geom →L[ℝ] L2S2Geom}
    (hTrot : IsRotationEquivariant T) (m n : ℕ) :
    SectorHom.IsRotationEquivariant (sectorBlock T m n) := by
  intro ρ u
  apply Subtype.ext
  change
    (sectorL2 n).starProjection (T (Rotation.compL2Rotation ρ u.1)) =
      Rotation.compL2Rotation ρ ((sectorL2 n).starProjection (T u.1))
  calc
    (sectorL2 n).starProjection (T (Rotation.compL2Rotation ρ u.1))
        = (sectorL2 n).starProjection (Rotation.compL2Rotation ρ (T u.1)) := by
            rw [hTrot ρ u.1]
    _ = Rotation.compL2Rotation ρ ((sectorL2 n).starProjection (T u.1)) := by
          exact sectorL2_starProjection_compL2Rotation_apply ρ n (T u.1)

theorem sectorBlock_eq_zero_of_ne
    {T : L2S2Geom →L[ℝ] L2S2Geom}
    (hTrot : IsRotationEquivariant T)
    {m n : ℕ} (hmn : m ≠ n) :
    sectorBlock T m n = 0 := by
  apply SectorHom.eq_zero_of_finrank_ne
  · exact sectorBlock_isRotationEquivariant hTrot m n
  · rw [finrank_sectorL2, finrank_sectorL2]
    omega

@[simp] theorem sectorBlock_apply_eq_zero_of_ne
    {T : L2S2Geom →L[ℝ] L2S2Geom}
    (hTrot : IsRotationEquivariant T)
    {m n : ℕ} (hmn : m ≠ n) (u : sectorL2 m) :
    sectorBlock T m n u = 0 := by
  simp [sectorBlock_eq_zero_of_ne hTrot hmn]

/-- A continuous rotation-equivariant operator on `L²(S²)` preserves every harmonic sector.

This is the block-diagonal part of the real Funk--Hecke principle: rotation equivariance alone
forces all off-diagonal harmonic blocks to vanish. -/
theorem preservesSector_of_isRotationEquivariant
    {T : L2S2Geom →L[ℝ] L2S2Geom}
    (hTrot : IsRotationEquivariant T) (n : ℕ) :
    PreservesSector T n := by
  intro x hx
  let y : L2S2Geom := T x
  have hsum : HasSum (fun m : ℕ => (sectorL2 m).starProjection y) y :=
    hasSum_sectorL2_starProjection y
  have hterms :
      ∀ m : ℕ, m ≠ n → (sectorL2 m).starProjection y = 0 := by
    intro m hmn
    let u : sectorL2 n := ⟨x, hx⟩
    have hblock : sectorBlock T n m u = 0 := by
      exact sectorBlock_apply_eq_zero_of_ne hTrot hmn.symm u
    simpa [sectorBlock, u, y] using congrArg (fun v : sectorL2 m => (v : L2S2Geom)) hblock
  have hfun :
      (fun m : ℕ => (sectorL2 m).starProjection y) =
        fun m : ℕ => if m = n then (sectorL2 n).starProjection y else 0 := by
    funext m
    by_cases hm : m = n
    · simp [hm]
    · simp [hm, hterms m hm]
  have hsum' :
      HasSum (fun m : ℕ => if m = n then (sectorL2 n).starProjection y else 0) y := by
    simpa [hfun] using hsum
  have hsingle :
      HasSum (fun m : ℕ => if m = n then (sectorL2 n).starProjection y else 0)
        ((sectorL2 n).starProjection y) :=
    hasSum_ite_eq n ((sectorL2 n).starProjection y)
  have hy : (sectorL2 n).starProjection y = y := hsingle.unique hsum'
  exact (sectorL2 n).starProjection_eq_self_iff.mp hy

/-- A continuous rotation-equivariant operator commutes with the harmonic-sector projections.

This is the projection form of the real Funk--Hecke spectral theorem for abstract
rotation-equivariant `L²(S²)` endomorphisms. -/
theorem sectorL2_starProjection_commute_of_isRotationEquivariant
    {T : L2S2Geom →L[ℝ] L2S2Geom}
    (hTrot : IsRotationEquivariant T) (n : ℕ) (x : L2S2Geom) :
    (sectorL2 n).starProjection (T x) =
      T ((sectorL2 n).starProjection x) := by
  have hsum_x : HasSum (fun m : ℕ => (sectorL2 m).starProjection x) x :=
    hasSum_sectorL2_starProjection x
  have hsum_T :
      HasSum (fun m : ℕ => T ((sectorL2 m).starProjection x)) (T x) :=
    T.hasSum hsum_x
  have hsum_proj :
      HasSum
        (fun m : ℕ => (sectorL2 n).starProjection (T ((sectorL2 m).starProjection x)))
        ((sectorL2 n).starProjection (T x)) :=
    ((sectorL2 n).starProjection).hasSum hsum_T
  have hterms :
      ∀ m : ℕ, m ≠ n →
        (sectorL2 n).starProjection (T ((sectorL2 m).starProjection x)) = 0 := by
    intro m hmn
    let u : sectorL2 m := ⟨(sectorL2 m).starProjection x,
      (sectorL2 m).starProjection_apply_mem x⟩
    have hblock : sectorBlock T m n u = 0 :=
      sectorBlock_apply_eq_zero_of_ne hTrot hmn u
    simpa [sectorBlock, u] using congrArg (fun v : sectorL2 n => (v : L2S2Geom)) hblock
  have hfun :
      (fun m : ℕ => (sectorL2 n).starProjection (T ((sectorL2 m).starProjection x))) =
        fun m : ℕ =>
          if m = n then
            (sectorL2 n).starProjection (T ((sectorL2 n).starProjection x))
          else 0 := by
    funext m
    by_cases hm : m = n
    · simp [hm]
    · simp [hm, hterms m hm]
  have hsum_single_target :
      HasSum
        (fun m : ℕ =>
          if m = n then
            (sectorL2 n).starProjection (T ((sectorL2 n).starProjection x))
          else 0)
        ((sectorL2 n).starProjection (T x)) := by
    simpa [hfun] using hsum_proj
  have hsum_single :
      HasSum
        (fun m : ℕ =>
          if m = n then
            (sectorL2 n).starProjection (T ((sectorL2 n).starProjection x))
          else 0)
        ((sectorL2 n).starProjection (T ((sectorL2 n).starProjection x))) :=
    hasSum_ite_eq n ((sectorL2 n).starProjection (T ((sectorL2 n).starProjection x)))
  have hproj_eq :
      (sectorL2 n).starProjection (T x) =
        (sectorL2 n).starProjection (T ((sectorL2 n).starProjection x)) :=
    (hsum_single.unique hsum_single_target).symm
  have hmem :
      T ((sectorL2 n).starProjection x) ∈ sectorL2 n :=
    preservesSector_of_isRotationEquivariant hTrot n
      ((sectorL2 n).starProjection_apply_mem x)
  have hfix :
      (sectorL2 n).starProjection (T ((sectorL2 n).starProjection x)) =
        T ((sectorL2 n).starProjection x) :=
    (sectorL2 n).starProjection_eq_self_iff.mpr hmem
  exact hproj_eq.trans hfix

theorem restrictToSector_eq_smul_id_of_eq_smul_on_cyclic
    {n : ℕ} (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hTrot : IsRotationEquivariant T) (hTsec : PreservesSector T n)
    {u : sectorL2 n} (hcyc : sectorRotationOrbitSpan n u = ⊤)
    {a : ℝ}
    (hau : SectorEndomorphism.restrictToSector n T hTsec u = a • u) :
    SectorEndomorphism.restrictToSector n T hTsec = SectorEndomorphism.scalarId n a := by
  exact
    SectorEndomorphism.eq_smul_id_of_eq_smul_on_cyclic
      (SectorEndomorphism.restrictToSector_isRotationEquivariant T hTrot hTsec)
      hcyc hau

theorem restrictToSector_eq_zero_of_eq_zero_on_cyclic
    {n : ℕ} (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hTrot : IsRotationEquivariant T) (hTsec : PreservesSector T n)
    {u : sectorL2 n} (hcyc : sectorRotationOrbitSpan n u = ⊤)
    (hu0 : SectorEndomorphism.restrictToSector n T hTsec u = 0) :
    SectorEndomorphism.restrictToSector n T hTsec = 0 := by
  have hu0' : SectorEndomorphism.restrictToSector n T hTsec u = (0 : ℝ) • u := by
    simpa using hu0
  have hscalar :
      SectorEndomorphism.restrictToSector n T hTsec = SectorEndomorphism.scalarId n 0 :=
    restrictToSector_eq_smul_id_of_eq_smul_on_cyclic T hTrot hTsec hcyc
      (a := 0) hu0'
  have hzeroid : SectorEndomorphism.scalarId n 0 = 0 := by
    ext x
    simp [SectorEndomorphism.scalarId]
  exact hscalar.trans hzeroid

end ContinuousLinearMap

end SphericalHarmonics
