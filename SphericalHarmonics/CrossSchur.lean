import SphericalHarmonics.NorthFixedSectorDimension

noncomputable section

namespace SphericalHarmonics

namespace SectorHom

/-- A continuous linear map between two harmonic sectors is rotation-equivariant if it intertwines
the restricted rotation actions. -/
def IsRotationEquivariant {m n : ℕ} (A : sectorL2 m →L[ℝ] sectorL2 n) : Prop :=
  ∀ (ρ : Rotation) (x : sectorL2 m),
    A (sectorCompL2Rotation ρ m x) = sectorCompL2Rotation ρ n (A x)

theorem ker_isRotationInvariant
    {m n : ℕ} {A : sectorL2 m →L[ℝ] sectorL2 n}
    (hA : IsRotationEquivariant A) :
    SectorSubmodule.IsRotationInvariant m (LinearMap.ker A.toLinearMap) := by
  intro ρ x hx
  rw [LinearMap.mem_ker] at hx ⊢
  calc
    A (sectorCompL2Rotation ρ m x)
        = sectorCompL2Rotation ρ n (A x) := hA ρ x
    _ = 0 := by
      have hx' : A x = 0 := Subtype.ext (by simpa using hx)
      rw [hx']
      simp

theorem range_isRotationInvariant
    {m n : ℕ} {A : sectorL2 m →L[ℝ] sectorL2 n}
    (hA : IsRotationEquivariant A) :
    SectorSubmodule.IsRotationInvariant n (LinearMap.range A.toLinearMap) := by
  intro ρ y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨sectorCompL2Rotation ρ m x, ?_⟩
  simpa using hA ρ x

private theorem mem_of_cyclicLine_inf_ne_bot
    {n : ℕ} {u : sectorL2 n}
    {W : Submodule ℝ (sectorL2 n)}
    (hW : cyclicLine u ⊓ W ≠ ⊥) :
    u ∈ W := by
  rw [Submodule.ne_bot_iff] at hW
  rcases hW with ⟨x, hx, hx0⟩
  have hxline : x ∈ cyclicLine u := hx.1
  rcases Submodule.mem_span_singleton.mp hxline with ⟨c, rfl⟩
  have hc : c ≠ 0 := by
    intro hc
    apply hx0
    simp [hc]
  have hcx : c • u ∈ W := hx.2
  have hu_eq : u = c⁻¹ • (c • u) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hu_eq]
  exact Submodule.smul_mem W _ hcx

private theorem eq_zero_of_apply_distinguished_eq_zero
    {m n : ℕ} (A : sectorL2 m →L[ℝ] sectorL2 n)
    (hA : IsRotationEquivariant A)
    (hu0 :
      A (distinguishedZonalVector m (northFixedSectorL2_ne_bot m)) = 0) :
    A = 0 := by
  let u := distinguishedZonalVector m (northFixedSectorL2_ne_bot m)
  have hu_mem : u ∈ LinearMap.ker A.toLinearMap := by
    simpa [LinearMap.mem_ker] using hu0
  have hker_top :
      LinearMap.ker A.toLinearMap = ⊤ := by
    apply eq_top_of_mem_of_orbitSpan_eq_top
      (ker_isRotationInvariant hA) hu_mem
    exact sectorRotationOrbitSpan_eq_top_of_distinguishedZonalVector m
  have hlin : A.toLinearMap = 0 :=
    LinearMap.ker_eq_top.mp hker_top
  exact ContinuousLinearMap.coe_injective hlin

private theorem range_eq_top_of_ne_zero
    {m n : ℕ} (A : sectorL2 m →L[ℝ] sectorL2 n)
    (hA : IsRotationEquivariant A)
    (hA0 : A ≠ 0) :
    LinearMap.range A.toLinearMap = ⊤ := by
  let um := distinguishedZonalVector m (northFixedSectorL2_ne_bot m)
  let un := distinguishedZonalVector n (northFixedSectorL2_ne_bot n)
  have hum_ne : um ≠ 0 := distinguishedZonalVector_ne_zero m (northFixedSectorL2_ne_bot m)
  have hun_ne : un ≠ 0 := distinguishedZonalVector_ne_zero n (northFixedSectorL2_ne_bot n)
  have hAum_ne : A um ≠ 0 := by
    intro hzero
    exact hA0 (eq_zero_of_apply_distinguished_eq_zero A hA hzero)
  have hhit :=
    distinguishedZonalLine_hit_of_eq_northFixedSectorL2
      (northFixedSectorL2_ne_bot n)
      (distinguishedZonalLine_eq_northFixedSectorL2 n (northFixedSectorL2_ne_bot n))
      (LinearMap.range A.toLinearMap) (range_isRotationInvariant hA) <| by
        intro hrange
        have hlin : A.toLinearMap = 0 := LinearMap.range_eq_bot.mp hrange
        exact hA0 (ContinuousLinearMap.coe_injective hlin)
  have hhit' :
      distinguishedZonalLine n (northFixedSectorL2_ne_bot n) ⊓ LinearMap.range A.toLinearMap ≠ ⊥ := by
    simpa [distinguishedZonalLine_eq_northFixedSectorL2 n (northFixedSectorL2_ne_bot n)] using hhit
  have hun_mem :
      un ∈ LinearMap.range A.toLinearMap := by
    have : un ∈ LinearMap.range A.toLinearMap := by
      simpa [distinguishedZonalLine] using mem_of_cyclicLine_inf_ne_bot hhit'
    exact this
  exact
    eq_top_of_mem_of_orbitSpan_eq_top
      (range_isRotationInvariant hA) hun_mem
      (sectorRotationOrbitSpan_eq_top_of_distinguishedZonalVector n)

theorem bijective_of_ne_zero
    {m n : ℕ} (A : sectorL2 m →L[ℝ] sectorL2 n)
    (hA : IsRotationEquivariant A)
    (hA0 : A ≠ 0) :
    Function.Bijective A := by
  constructor
  · intro x y hxy
    have hsub : x - y ∈ LinearMap.ker A.toLinearMap := by
      rw [LinearMap.mem_ker]
      simp [map_sub, hxy]
    have hker_top : LinearMap.ker A.toLinearMap ≠ ⊤ := by
      intro htop
      apply hA0
      exact ContinuousLinearMap.coe_injective (LinearMap.ker_eq_top.mp htop)
    have hker_bot : LinearMap.ker A.toLinearMap = ⊥ := by
      by_contra hne
      have hhit :=
        distinguishedZonalLine_hit_of_eq_northFixedSectorL2
          (northFixedSectorL2_ne_bot m)
          (distinguishedZonalLine_eq_northFixedSectorL2 m (northFixedSectorL2_ne_bot m))
          (LinearMap.ker A.toLinearMap) (ker_isRotationInvariant hA) hne
      have hhit' :
          distinguishedZonalLine m (northFixedSectorL2_ne_bot m) ⊓ LinearMap.ker A.toLinearMap ≠ ⊥ := by
        simpa [distinguishedZonalLine_eq_northFixedSectorL2 m (northFixedSectorL2_ne_bot m)] using hhit
      have hum_mem :
          distinguishedZonalVector m (northFixedSectorL2_ne_bot m) ∈ LinearMap.ker A.toLinearMap := by
        simpa [distinguishedZonalLine] using mem_of_cyclicLine_inf_ne_bot hhit'
      have hzero :
          A (distinguishedZonalVector m (northFixedSectorL2_ne_bot m)) = 0 := by
        simpa [LinearMap.mem_ker] using hum_mem
      exact hA0 (eq_zero_of_apply_distinguished_eq_zero A hA hzero)
    have hxy0 : x - y = 0 := by
      have : x - y ∈ (⊥ : Submodule ℝ (sectorL2 m)) := by simpa [hker_bot] using hsub
      simpa using this
    simpa using sub_eq_zero.mp hxy0
  · intro y
    have hrange_top : LinearMap.range A.toLinearMap = ⊤ :=
      range_eq_top_of_ne_zero A hA hA0
    have hy' : y ∈ LinearMap.range A.toLinearMap := by simpa [hrange_top]
    rcases hy' with ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem eq_zero_of_finrank_ne
    {m n : ℕ} (A : sectorL2 m →L[ℝ] sectorL2 n)
    (hA : IsRotationEquivariant A)
    (hfin :
      Module.finrank ℝ (sectorL2 m) ≠ Module.finrank ℝ (sectorL2 n)) :
    A = 0 := by
  by_contra hA0
  obtain ⟨hAinj, hAsurj⟩ := bijective_of_ne_zero A hA hA0
  let e : sectorL2 m ≃ₗ[ℝ] sectorL2 n :=
    LinearEquiv.ofBijective A.toLinearMap ⟨hAinj, hAsurj⟩
  exact hfin e.finrank_eq

end SectorHom

end SphericalHarmonics
