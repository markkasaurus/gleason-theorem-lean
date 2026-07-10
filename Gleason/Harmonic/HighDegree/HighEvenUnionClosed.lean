import Gleason.Harmonic.HighDegree.EvenUnionSplit
import Gleason.Continuity.Auxiliary.ClosedGreatCircle
import Gleason.Continuity.Auxiliary.ClosedFrame
import Gleason.Harmonic.Rotation.RotationEquiv
import Gleason.Harmonic.Zonal.NorthZonalClosed
import Gleason.Harmonic.Zonal.NorthOrbitAverage
import Gleason.Harmonic.Fischer.FischerNorthZonalWitness

noncomputable section

open Complex InnerProductSpace

def spherePrecompContinuousLinearEquiv
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3) :
    C(spherePoint3, ℝ) ≃L[ℝ] C(spherePoint3, ℝ) where
  toLinearEquiv := spherePrecompLinearEquiv e
  continuous_toFun := (spherePrecompCLM e).continuous
  continuous_invFun := (spherePrecompCLM e.symm).continuous

theorem highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.map
        (spherePrecompLinearEquiv e).toLinearMap =
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule := by
  unfold highEvenUnionHarmonicPolyHomogeneousImageSubmodule
  simp_rw [Submodule.map_iSup]
  refine iSup_congr ?_
  intro N
  exact highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_invariant_under_spherePrecomp N e

theorem topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure.map
        (spherePrecompLinearEquiv e).toLinearMap =
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure := by
  have hle :
      ∀ e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3,
        highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure.map
            (spherePrecompLinearEquiv e).toLinearMap
          ≤ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure := by
    intro e
    intro f hf
    rcases hf with ⟨g, hg, rfl⟩
    let T := spherePrecompContinuousLinearEquiv e
    let S : Set C(spherePoint3, ℝ) :=
      ((highEvenUnionHarmonicPolyHomogeneousImageSubmodule :
        Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ))
    have hmem :
        spherePrecomp e g ∈ T.toHomeomorph '' closure S := by
      exact ⟨g, by simpa [S, Submodule.topologicalClosure_coe] using hg, rfl⟩
    have himg :
        spherePrecomp e g ∈ closure ((spherePrecompLinearEquiv e) '' S) := by
      rw [T.toHomeomorph.image_closure S] at hmem
      simpa [T, spherePrecompContinuousLinearEquiv] using hmem
    have himage : (spherePrecompLinearEquiv e) '' S = S := by
      ext h
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hkmap :
            spherePrecomp e k ∈
              ((highEvenUnionHarmonicPolyHomogeneousImageSubmodule.map
                (spherePrecompLinearEquiv e).toLinearMap :
                  Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) := by
          exact ⟨k, hk, rfl⟩
        simpa [T, S, spherePrecompContinuousLinearEquiv, Submodule.map_coe,
          highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv e] using hkmap
      · intro hh
        have hhmap :
            h ∈
              ((highEvenUnionHarmonicPolyHomogeneousImageSubmodule.map
                (spherePrecompLinearEquiv e).toLinearMap :
                  Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) := by
          simpa [T, S, spherePrecompContinuousLinearEquiv, Submodule.map_coe,
            highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv e] using hh
        rcases hhmap with ⟨k, hk, hk_eq⟩
        exact ⟨k, hk, hk_eq⟩
    have himg' :
        spherePrecomp e g ∈ closure S := by
      simpa [himage] using himg
    simpa [S, Submodule.topologicalClosure_coe] using himg'
  apply le_antisymm (hle e)
  intro f hf
  refine ⟨spherePrecomp e.symm f, ?_, ?_⟩
  · exact hle e.symm <| ⟨f, hf, rfl⟩
  · ext x
    simp [spherePrecompLinearEquiv, spherePrecomp]

theorem isClosed_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule :
    IsClosed
      ((highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure :
          Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) := by
  exact Submodule.isClosed_topologicalClosure _

theorem northOrbitAverage_mem_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure) :
    northOrbitAverage f ∈
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure := by
  have hGinv :
      ∀ t : ℝ,
        highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ≤
          (highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure).comap
            (spherePrecomp (northRotation t)) := by
    intro t g hg
    have hmap :
        spherePrecomp (northRotation t) g ∈
          (highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure).map
            (spherePrecompLinearEquiv (northRotation t)).toLinearMap := by
      exact ⟨g, hg, rfl⟩
    simpa [topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv
      (northRotation t)] using hmap
  exact northOrbitAverage_mem_of_isClosed_of_invariant
    isClosed_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hGinv hf

theorem northOrbitAverage_mem_topologicalClosure_highEvenUnion_inf_frame
    {f : C(spherePoint3, ℝ)}
    (hf :
      f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule) :
    northOrbitAverage f ∈
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule := by
  refine ⟨northOrbitAverage_mem_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hf.1, ?_⟩
  exact northOrbitAverage_mem_continuousSphereFrameSubmodule hf.2

theorem exists_nonzero_northZonal_mem_topologicalClosure_highEvenUnion_inf_frame
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g := by
  let G : Submodule ℝ C(spherePoint3, ℝ) :=
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule
  have hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)) := by
    simpa [G] using
      (isClosed_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule).inter
        isClosed_continuousSphereFrameSubmodule
  have hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G := by
    intro e
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨?_, continuousSphereFrameSubmodule_invariant_under_spherePrecomp e hg.2⟩
      have hmap :
          spherePrecomp e g ∈
            (highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure).map
              (spherePrecompLinearEquiv e).toLinearMap := by
        exact ⟨g, hg.1, rfl⟩
      simpa [topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv e]
        using hmap
    · intro hf
      refine ⟨spherePrecomp e.symm f, ?_, ?_⟩
      · refine ⟨?_, continuousSphereFrameSubmodule_invariant_under_spherePrecomp e.symm hf.2⟩
        have hmap :
            spherePrecomp e.symm f ∈
              (highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure).map
                (spherePrecompLinearEquiv e.symm).toLinearMap := by
          exact ⟨f, hf.1, rfl⟩
        simpa [topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv e.symm]
          using hmap
      · ext x
        simp [spherePrecompLinearEquiv, spherePrecomp]
  simpa [G] using
    exists_nonzero_northZonal_mem_of_isClosed_of_rotationInvariant hGclosed hGrot hne

theorem exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g := by
  rcases exists_nonzero_northZonal_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz⟩
  exact ⟨g, hg, hgne, hgz, northOrbitAverage_eq_self_of_isNorthZonal hgz⟩
