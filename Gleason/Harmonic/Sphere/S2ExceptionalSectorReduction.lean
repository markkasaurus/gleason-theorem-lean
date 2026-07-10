import Gleason.Harmonic.Sphere.S2PointConstraintRotation
import Gleason.Harmonic.Sphere.S2L2Frame
import Gleason.Harmonic.Sphere.S2DistinguishedNorthZonal
import SphericalHarmonics.NorthFixedSectorDimension
import SphericalHarmonics.NorthAxisAverageSector
import SphericalHarmonics.ZonalHit

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

theorem continuousToLp_ambientSectorProjectionContinuous
    (n : ℕ) (f : C(S2, ℝ)) :
    continuousToLp (ambientSectorProjectionContinuous n f) =
      (sectorL2 n).starProjection (continuousToLp f) := by
  let y : sectorL2 n :=
    (((sectorL2 n).starProjection.comp continuousToLp).codRestrict (sectorL2 n)
      (fun f =>
        ((sectorL2 n).starProjection_eq_self_iff).1 <| by
          change
            (sectorL2 n).starProjection
                (((sectorL2 n).starProjection.comp continuousToLp) f) =
              ((sectorL2 n).starProjection.comp continuousToLp) f
          have hidem := (sectorL2 n).isIdempotentElem_starProjection.eq
          exact congrArg (fun T : L2S2 →L[ℝ] L2S2 => T (continuousToLp f)) hidem)) f
  have hy : sectorToSectorL2 n (sectorProjectionContinuous n f) = y := by
    exact (sectorToSectorL2Equiv n).apply_symm_apply y
  change continuousToLp (ambientSectorProjectionContinuous n f) = ↑y
  simpa [ambientSectorProjectionContinuous, sectorProjectionContinuous, sectorToSectorL2,
    ContinuousLinearMap.comp_apply] using congrArg Subtype.val hy

/-- The `L²` image of the degree-`n` continuous point-constraint sector image. -/
def pointConstraintSectorImageL2S2 (n : ℕ) : Submodule ℝ L2S2Geom :=
  Submodule.map continuousToLp.toLinearMap (pointConstraintSectorImageSubmoduleS2 n)

theorem pointConstraintSectorImageL2S2_le_sectorL2 (n : ℕ) :
    pointConstraintSectorImageL2S2 n ≤ sectorL2 n := by
  intro x hx
  rcases hx with ⟨f, hf, rfl⟩
  exact continuousToLp_mem_sectorL2 (pointConstraintSectorImageSubmoduleS2_le_sector n hf)

theorem isClosed_pointConstraintSectorImageL2S2 (n : ℕ) :
    IsClosed (pointConstraintSectorImageL2S2 n : Set L2S2Geom) := by
  letI : FiniteDimensional ℝ (pointConstraintSectorImageL2S2 n) :=
    Submodule.finiteDimensional_of_le (pointConstraintSectorImageL2S2_le_sectorL2 n)
  simpa using Submodule.closed_of_finiteDimensional (pointConstraintSectorImageL2S2 n)

theorem continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_le_pointConstraintSectorImageL2S2
    (n : ℕ) :
    continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n ≤
      pointConstraintSectorImageL2S2 n := by
  intro x hx
  let T : L2S2Geom →L[ℝ] L2S2Geom := (sectorL2 n).starProjection
  have hmap :
      Set.MapsTo T (continuousSphereFrameImageL2S2 : Set L2S2Geom)
        (pointConstraintSectorImageL2S2 n : Set L2S2Geom) := by
    intro y hy
    rcases hy with ⟨f, hf, rfl⟩
    refine ⟨ambientSectorProjectionContinuous n f, ?_, ?_⟩
    · refine ⟨f, ?_, rfl⟩
      simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
        using hf
    · exact continuousToLp_ambientSectorProjectionContinuous n f
  have hTx :
      T x ∈ pointConstraintSectorImageL2S2 n := by
    exact hmap.closure_left T.continuous (isClosed_pointConstraintSectorImageL2S2 n) hx.1
  have hxfix : T x = x := by
    exact (sectorL2 n).starProjection_eq_self_iff.mpr hx.2
  simpa [T, hxfix] using hTx

theorem pointConstraintSectorImageSubmoduleS2_ne_bot_of_continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_ne_bot
    {n : ℕ}
    (hne :
      continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n ≠ ⊥) :
    pointConstraintSectorImageSubmoduleS2 n ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hne ⊢
  rcases hne with ⟨x, hx, hx0⟩
  have hximg :
      x ∈ pointConstraintSectorImageL2S2 n :=
    continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_le_pointConstraintSectorImageL2S2 n hx
  rcases hximg with ⟨f, hf, hfx⟩
  refine ⟨f, hf, ?_⟩
  intro hf0
  apply hx0
  simpa [hf0] using hfx.symm

theorem distinguishedZonalSector_mem_pointConstraintSectorImageSubmoduleS2_of_continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_ne_bot
    {n : ℕ}
    (hne :
      continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n ≠ ⊥) :
    ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) ∈
      pointConstraintSectorImageSubmoduleS2 n := by
  have hWne : pointConstraintSectorImageSubmoduleS2 n ≠ ⊥ :=
    pointConstraintSectorImageSubmoduleS2_ne_bot_of_continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_ne_bot
      hne
  let W : Submodule ℝ (sector n) :=
    (pointConstraintSectorImageSubmoduleS2 n).comap (sector n).subtypeL
  have hWrot : SectorContinuousSubmodule.IsRotationInvariant n W := by
    intro ρ x hx
    rw [Submodule.mem_comap] at hx ⊢
    exact pointConstraintSectorImageSubmoduleS2_invariant_under_compContinuous ρ n hx
  have hWne' : W ≠ ⊥ := by
    rw [Submodule.ne_bot_iff] at hWne ⊢
    rcases hWne with ⟨f, hf, hf0⟩
    refine ⟨⟨f, pointConstraintSectorImageSubmoduleS2_le_sector n hf⟩, ?_, ?_⟩
    · exact hf
    · intro hzero
      apply hf0
      exact Subtype.ext_iff.mp hzero
  rcases exists_nonzero_mem_inf_northFixedSector_of_isRotationInvariant_of_ne_bot hWrot hWne' with
    ⟨f, hf, hf0⟩
  obtain ⟨c, hc⟩ :
      ∃ c : ℝ, c • distinguishedZonalSector n = ⟨f, hf.2⟩ :=
    (finrank_eq_one_iff_of_nonzero' (distinguishedZonalSector n)
      (by
        intro hz
        exact distinguishedZonalSector_ne_zero n <|
          congrArg (fun z : northFixedSector n => ((z : sector n))) hz)).mp
      (finrank_northFixedSector_eq_one n) ⟨f, hf.2⟩
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hf0
    have : (⟨f, hf.2⟩ : northFixedSector n) = 0 := by
      simpa [hc0] using hc.symm
    simpa using congrArg (fun z : northFixedSector n => ((z : sector n) : C(S2, ℝ))) this
  have hcf :
      c • ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) = f := by
    exact congrArg (fun z : northFixedSector n => ((z : sector n) : C(S2, ℝ))) hc
  have hdist :
      ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) =
        c⁻¹ • f := by
    calc
      ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))
          = c⁻¹ • (c • ((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ)))) := by
                rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • f := by rw [hcf]
  rw [hdist]
  exact Submodule.smul_mem _ _ hf.1

theorem continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_distinguishedZonalSector_not_mem_pointConstraintSectorImageSubmoduleS2
    {n : ℕ}
    (hnot :
      ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) ∉
        pointConstraintSectorImageSubmoduleS2 n) :
    continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n = ⊥ := by
  by_contra hne
  exact hnot <|
    distinguishedZonalSector_mem_pointConstraintSectorImageSubmoduleS2_of_continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_ne_bot
      hne

end GleasonS2Bridge
