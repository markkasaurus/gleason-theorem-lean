import SphericalHarmonics.NorthFixedSectorDimension

noncomputable section

open MeasureTheory intervalIntegral

namespace SphericalHarmonics

theorem northAxisAverage_eq_self_of_mem_northFixedSubmodule
    {f : C(S2, ℝ)} (hf : f ∈ northFixedSubmodule) :
    northAxisAverage f = f := by
  ext x
  rw [northAxisAverage_apply]
  have hconst :
      (∫ t in 0..2 * Real.pi, f ((rotation01 t).toSphereEquiv.symm x)) =
        (2 * Real.pi) * f x := by
    have hfun :
        (fun t : ℝ => f ((rotation01 t).toSphereEquiv.symm x)) = fun _ : ℝ => f x := by
      funext t
      have hfix :=
        congrArg (fun g : C(S2, ℝ) => g x) ((mem_northFixedSubmodule_iff f).1 hf t)
      simpa [Rotation.compContinuous_apply] using hfix
    rw [hfun]
    simp
  rw [hconst]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hpi]

theorem northAxisAverage_mem_sector {n : ℕ} {f : C(S2, ℝ)}
    (hf : f ∈ sector n) :
    northAxisAverage f ∈ sector n := by
  let G : ℝ → sector n := fun t =>
    ⟨Rotation.compContinuous (rotation01 t) f,
      compContinuous_mem_sector (rotation01 t) n hf⟩
  have hGcont0 : Continuous fun t : ℝ => Rotation.compContinuous (rotation01 t) f := by
    simpa using northRotationOrbitContinuousS2 f
  have hGcont : Continuous G := by
    exact Continuous.subtype_mk hGcont0 (fun t => compContinuous_mem_sector (rotation01 t) n hf)
  have hGInt : IntervalIntegrable G volume 0 (2 * Real.pi) := hGcont.intervalIntegrable 0 (2 * Real.pi)
  let avg : sector n := ((2 * Real.pi)⁻¹ : ℝ) • ∫ t in 0..2 * Real.pi, G t
  have havg_eq :
      ((avg : sector n) : C(S2, ℝ)) = northAxisAverage f := by
    change (sector n).subtypeL (((2 * Real.pi)⁻¹ : ℝ) • ∫ t in 0..2 * Real.pi, G t) =
      northAxisAverage f
    unfold northAxisAverage
    rw [ContinuousLinearMap.map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm
      (sector n).subtypeL hGInt]
    rfl
  simpa [havg_eq] using avg.2

/-- North-axis averaging of a degree-`n` continuous spherical harmonic, packaged back in the
degree-`n` sector. -/
noncomputable def northAxisAverageSector {n : ℕ} (f : sector n) : sector n :=
  ⟨northAxisAverage (f : C(S2, ℝ)), northAxisAverage_mem_sector f.2⟩

theorem northAxisAverageSector_mem_northFixedSector {n : ℕ} (f : sector n) :
    northAxisAverageSector f ∈ northFixedSector n := by
  exact northAxisAverage_mem_northFixedSubmodule (f : C(S2, ℝ))

theorem northAxisAverage_eq_self_of_mem_northFixedSector
    {n : ℕ} {f : sector n} (hf : f ∈ northFixedSector n) :
    northAxisAverage (f : C(S2, ℝ)) = f := by
  exact northAxisAverage_eq_self_of_mem_northFixedSubmodule hf

/-- The canonical continuous north-fixed representative of the distinguished zonal vector in the
degree-`n` `L²` sector. -/
noncomputable def distinguishedZonalSector (n : ℕ) : northFixedSector n :=
  (northFixedSectorToNorthFixedSectorL2Equiv n).symm
    ⟨distinguishedZonalVector n (northFixedSectorL2_ne_bot n),
      distinguishedZonalVector_mem n (northFixedSectorL2_ne_bot n)⟩

theorem northAxisAverage_distinguishedZonalSector (n : ℕ) :
    northAxisAverage ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) =
      ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) := by
  exact northAxisAverage_eq_self_of_mem_northFixedSector
    ((distinguishedZonalSector n).property)

end SphericalHarmonics
