import SphericalHarmonics.NorthFixedDimension

noncomputable section

namespace SphericalHarmonics

/-- Restriction to the sphere, with codomain restricted to the north-axis fixed continuous degree
slice. -/
noncomputable def restrictToNorthFixedSector (n : ℕ) :
    northFixedAmbientHarmonicSubmodule n →ₗ[ℝ] northFixedSector n where
  toFun p :=
    ⟨⟨restrictToSphere p.1, restrict_mem_sector p.2.1⟩, by
      rw [mem_northFixedSector_iff, mem_northFixedSubmodule_iff]
      intro t
      calc
        Rotation.compContinuous (rotation01 t) (restrictToSphere p.1)
            = restrictToSphere ((rotation01 t).compPolynomial p.1) := by
                simpa using (Rotation.restrictToSphere_compPolynomial (rotation01 t) p.1).symm
        _ = restrictToSphere p.1 := by rw [p.2.2 t]⟩
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    simp
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    simp

theorem restrictToNorthFixedSector_injective (n : ℕ) :
    Function.Injective (restrictToNorthFixedSector n) := by
  intro p q hpq
  let p' : harmonicHomogeneousSubmodule n := ⟨p.1, p.2.1⟩
  let q' : harmonicHomogeneousSubmodule n := ⟨q.1, q.2.1⟩
  have hres : restrictToSphere p.1 = restrictToSphere q.1 := by
    simpa [restrictToNorthFixedSector] using
      congrArg (fun r : northFixedSector n => ((r : sector n) : C(S2, ℝ))) hpq
  have hsub : p' = q' :=
    restrictToSphere_injective_on_harmonicHomogeneousSubmodule n hres
  exact Subtype.ext (congrArg (fun r : harmonicHomogeneousSubmodule n => r.1) hsub)

theorem restrictToNorthFixedSector_surjective (n : ℕ) :
    Function.Surjective (restrictToNorthFixedSector n) := by
  intro f
  rcases exists_fixed_ambientRepresentative_of_mem_northFixedSector f.2 with
    ⟨p, hpres, hprot⟩
  refine ⟨⟨p.1, ⟨p.2, hprot⟩⟩, ?_⟩
  apply Subtype.ext
  exact Subtype.ext hpres

/-- The north-axis fixed ambient harmonic slice and the fixed continuous degree sector are
canonically isomorphic. -/
noncomputable def restrictToNorthFixedSectorEquiv (n : ℕ) :
    northFixedAmbientHarmonicSubmodule n ≃ₗ[ℝ] northFixedSector n :=
  LinearEquiv.ofBijective (restrictToNorthFixedSector n)
    ⟨restrictToNorthFixedSector_injective n, restrictToNorthFixedSector_surjective n⟩

theorem finrank_northFixedSector_eq_one (n : ℕ) :
    Module.finrank ℝ (northFixedSector n) = 1 := by
  rw [← (restrictToNorthFixedSectorEquiv n).finrank_eq]
  exact finrank_northFixedAmbientHarmonicSubmodule_eq_one n

/-- The canonical map from the fixed continuous degree slice to the fixed `L²` degree slice. -/
noncomputable def northFixedSectorToNorthFixedSectorL2 (n : ℕ) :
    northFixedSector n →ₗ[ℝ] northFixedSectorL2 n where
  toFun f := ⟨sectorToSectorL2 n f.1, ⟨f.1, f.2, rfl⟩⟩
  map_add' f g := by
    apply Subtype.ext
    ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    ext
    rfl

theorem northFixedSectorToNorthFixedSectorL2_injective (n : ℕ) :
    Function.Injective (northFixedSectorToNorthFixedSectorL2 n) := by
  intro f g hfg
  apply Subtype.ext
  exact sectorToSectorL2_injective n (congrArg Subtype.val hfg)

theorem northFixedSectorToNorthFixedSectorL2_surjective (n : ℕ) :
    Function.Surjective (northFixedSectorToNorthFixedSectorL2 n) := by
  intro u
  rcases u.2 with ⟨f, hf, hfu⟩
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  simpa [northFixedSectorToNorthFixedSectorL2] using hfu

/-- The fixed continuous and fixed `L²` degree slices are canonically isomorphic. -/
noncomputable def northFixedSectorToNorthFixedSectorL2Equiv (n : ℕ) :
    northFixedSector n ≃ₗ[ℝ] northFixedSectorL2 n :=
  LinearEquiv.ofBijective (northFixedSectorToNorthFixedSectorL2 n)
    ⟨northFixedSectorToNorthFixedSectorL2_injective n,
      northFixedSectorToNorthFixedSectorL2_surjective n⟩

theorem finrank_northFixedSectorL2_eq_one (n : ℕ) :
    Module.finrank ℝ (northFixedSectorL2 n) = 1 := by
  rw [← (northFixedSectorToNorthFixedSectorL2Equiv n).finrank_eq]
  exact finrank_northFixedSector_eq_one n

theorem northFixedSectorL2_ne_bot (n : ℕ) :
    northFixedSectorL2 n ≠ ⊥ := by
  intro hbot
  have hfin : Module.finrank ℝ (northFixedSectorL2 n) = 0 := by
    simpa [hbot] using (rfl : Module.finrank ℝ (⊥ : Submodule ℝ (sectorL2 n)) = 0)
  rw [finrank_northFixedSectorL2_eq_one n] at hfin
  norm_num at hfin

theorem distinguishedZonalLine_eq_northFixedSectorL2
    (n : ℕ) (hne : northFixedSectorL2 n ≠ ⊥) :
    distinguishedZonalLine n hne = northFixedSectorL2 n := by
  refine le_antisymm (distinguishedZonalLine_le_northFixedSectorL2 n hne) ?_
  intro w hw
  rw [distinguishedZonalLine, cyclicLine]
  let v : northFixedSectorL2 n := ⟨distinguishedZonalVector n hne, distinguishedZonalVector_mem n hne⟩
  have hv : v ≠ 0 := by
    intro hv0
    exact distinguishedZonalVector_ne_zero n hne (congrArg Subtype.val hv0)
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' v hv).mp (finrank_northFixedSectorL2_eq_one n) ⟨w, hw⟩
  have hc' : c • distinguishedZonalVector n hne = w := congrArg Subtype.val hc
  rw [← hc']
  exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))

theorem sectorRotationOrbitSpan_eq_top_of_distinguishedZonalVector (n : ℕ) :
    sectorRotationOrbitSpan n
      (distinguishedZonalVector n (northFixedSectorL2_ne_bot n)) = ⊤ := by
  apply sectorRotationOrbitSpan_eq_top_of_distinguishedZonalLine_eq_northFixedSectorL2
  exact distinguishedZonalLine_eq_northFixedSectorL2 n (northFixedSectorL2_ne_bot n)

/-- Every nonzero vector in a harmonic sector is cyclic under the rotation action. -/
theorem sectorRotationOrbitSpan_eq_top_of_ne_zero
    {n : ℕ} {u : sectorL2 n} (hu : u ≠ 0) :
    sectorRotationOrbitSpan n u = ⊤ := by
  let W : Submodule ℝ (sectorL2 n) := sectorRotationOrbitSpan n u
  have hWrot : SectorSubmodule.IsRotationInvariant n W :=
    sectorRotationOrbitSpan_isRotationInvariant n u
  have hWne : W ≠ ⊥ := by
    intro hbot
    have huW : u ∈ W := by
      exact Submodule.subset_span ⟨1, by simp⟩
    have huBot : u ∈ (⊥ : Submodule ℝ (sectorL2 n)) := by
      simpa [W, hbot] using huW
    exact hu (by simpa using huBot)
  have hhit :
      distinguishedZonalLine n (northFixedSectorL2_ne_bot n) ⊓ W ≠ ⊥ :=
    distinguishedZonalLine_hit_of_eq_northFixedSectorL2
      (northFixedSectorL2_ne_bot n)
      (distinguishedZonalLine_eq_northFixedSectorL2 n (northFixedSectorL2_ne_bot n))
      W hWrot hWne
  have hdistW :
      distinguishedZonalVector n (northFixedSectorL2_ne_bot n) ∈ W := by
    rw [Submodule.ne_bot_iff] at hhit
    rcases hhit with ⟨x, hx, hx0⟩
    have hxline : x ∈ distinguishedZonalLine n (northFixedSectorL2_ne_bot n) := hx.1
    rw [distinguishedZonalLine, cyclicLine] at hxline
    rcases Submodule.mem_span_singleton.mp hxline with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by
      intro hc0
      apply hx0
      rw [← hc, hc0, zero_smul]
    have hcxW : c • distinguishedZonalVector n (northFixedSectorL2_ne_bot n) ∈ W := by
      simpa [hc] using hx.2
    have hscale :
        distinguishedZonalVector n (northFixedSectorL2_ne_bot n) =
          c⁻¹ • (c • distinguishedZonalVector n (northFixedSectorL2_ne_bot n)) := by
      rw [smul_smul, inv_mul_cancel₀ hc_ne, one_smul]
    rw [hscale]
    exact W.smul_mem c⁻¹ hcxW
  exact
    eq_top_of_mem_of_orbitSpan_eq_top hWrot hdistW
      (sectorRotationOrbitSpan_eq_top_of_distinguishedZonalVector n)

/-- A nonzero linear functional on an irreducible harmonic sector cannot vanish on the full
rotation orbit of a nonzero vector. -/
theorem eq_zero_of_forall_linearFunctional_rotation_eq_zero
    {n : ℕ} {u : sectorL2 n} {ℓ : sectorL2 n →ₗ[ℝ] ℝ}
    (hℓ : ℓ ≠ 0)
    (hu : ∀ ρ : Rotation, ℓ (sectorCompL2Rotation ρ n u) = 0) :
    u = 0 := by
  by_contra hu0
  let W : Submodule ℝ (sectorL2 n) := sectorRotationOrbitSpan n u
  have hWtop : W = ⊤ := sectorRotationOrbitSpan_eq_top_of_ne_zero hu0
  have hWker : W ≤ LinearMap.ker ℓ := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with ⟨ρ, rfl⟩
    exact hu ρ
  have hkerTop : LinearMap.ker ℓ = ⊤ := by
    apply top_unique
    intro x hx
    exact hWker (by simp [W, hWtop])
  exact hℓ (LinearMap.ker_eq_top.mp hkerTop)

end SphericalHarmonics
