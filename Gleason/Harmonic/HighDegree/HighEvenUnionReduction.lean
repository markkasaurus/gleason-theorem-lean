import Gleason.Harmonic.HighDegree.EvenUnionSplit
import Gleason.Harmonic.Fischer.FischerNorthOrbit
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

open Complex InnerProductSpace

instance lowHarmonicPolyHomogeneousImageSubmodule_finiteDimensional :
    FiniteDimensional ℝ lowHarmonicPolyHomogeneousImageSubmodule := by
  rw [lowHarmonicPolyHomogeneousImageSubmodule]
  infer_instance

theorem isClosed_lowHarmonicPolyHomogeneousImageSubmodule :
    IsClosed ((lowHarmonicPolyHomogeneousImageSubmodule : Submodule ℝ C(spherePoint3, ℝ)) :
      Set C(spherePoint3, ℝ)) := by
  exact Submodule.closed_of_finiteDimensional _

theorem continuousSphereFrameSubmodule_le_low_sup_topologicalClosure_highEvenUnion :
    continuousSphereFrameSubmodule ≤
      lowHarmonicPolyHomogeneousImageSubmodule ⊔
        highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure := by
  refine continuousSphereFrameSubmodule_le_evenBoundedHarmonicPolyImage_closure.trans ?_
  let H : Submodule ℝ C(spherePoint3, ℝ) :=
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure
  have hclosedLowMap :
      IsClosed ((Submodule.map H.mkQ lowHarmonicPolyHomogeneousImageSubmodule :
        Submodule ℝ (C(spherePoint3, ℝ) ⧸ H)) : Set (C(spherePoint3, ℝ) ⧸ H)) := by
    haveI : IsClosed ((H : Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) :=
      Submodule.isClosed_topologicalClosure _
    exact Submodule.closed_of_finiteDimensional _
  have hclosedLowSupHigh :
      IsClosed (((lowHarmonicPolyHomogeneousImageSubmodule ⊔ H :
        Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ))) := by
    have hclosedPreimage :
        IsClosed
          (H.mkQ ⁻¹'
            (((Submodule.map H.mkQ lowHarmonicPolyHomogeneousImageSubmodule :
              Submodule ℝ (C(spherePoint3, ℝ) ⧸ H)) :
              Set (C(spherePoint3, ℝ) ⧸ H)))) :=
      H.isOpenQuotientMap_mkQ.isQuotientMap.isClosed_preimage.2 hclosedLowMap
    have hclosedComap :
        IsClosed
          ((((Submodule.comap H.mkQ
            (Submodule.map H.mkQ lowHarmonicPolyHomogeneousImageSubmodule)) :
              Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ))) := by
      convert hclosedPreimage using 1
    simpa [H, Submodule.comap_map_mkQ, sup_comm] using hclosedComap
  exact Submodule.topologicalClosure_minimal
    evenUnionHarmonicPolyHomogeneousImageSubmodule
    ((evenUnionHarmonicPolyHomogeneousImageSubmodule_eq_low_sup_highEvenUnion).le.trans <|
      sup_le_sup le_rfl (Submodule.le_topologicalClosure _))
    hclosedLowSupHigh

theorem continuousSphereFrameSubmodule_le_low_of_topologicalClosure_highEvenUnion_inf_frame_le_low
    (hclosure :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≤
          lowHarmonicPolyHomogeneousImageSubmodule) :
    continuousSphereFrameSubmodule ≤ lowHarmonicPolyHomogeneousImageSubmodule := by
  intro f hf
  have hsum :
      f ∈ lowHarmonicPolyHomogeneousImageSubmodule ⊔
        highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure :=
    continuousSphereFrameSubmodule_le_low_sup_topologicalClosure_highEvenUnion hf
  rcases Submodule.mem_sup.mp hsum with ⟨f₁, hf₁, f₂, hf₂, rfl⟩
  have hf₁_frame : f₁ ∈ continuousSphereFrameSubmodule :=
    lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereFrameSubmodule hf₁
  have hf₂_frame : f₂ ∈ continuousSphereFrameSubmodule := by
    have : f₂ = (f₁ + f₂) - f₁ := by abel
    rw [this]
    exact Submodule.sub_mem _ hf hf₁_frame
  have hf₂_low : f₂ ∈ lowHarmonicPolyHomogeneousImageSubmodule :=
    hclosure ⟨hf₂, hf₂_frame⟩
  exact Submodule.add_mem _ hf₁ hf₂_low

theorem continuousSphereFrameSubmodule_eq_low_of_topologicalClosure_highEvenUnion_inf_frame_le_low
    (hclosure :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≤
          lowHarmonicPolyHomogeneousImageSubmodule) :
    continuousSphereFrameSubmodule = lowHarmonicPolyHomogeneousImageSubmodule := by
  apply le_antisymm
  · exact
      continuousSphereFrameSubmodule_le_low_of_topologicalClosure_highEvenUnion_inf_frame_le_low
        hclosure
  · exact lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereFrameSubmodule
