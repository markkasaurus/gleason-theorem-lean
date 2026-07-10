import Gleason.Harmonic.Fischer.FischerFiniteSum
import Gleason.Harmonic.Fischer.FischerRotationGeneral

noncomputable section

open Complex InnerProductSpace

def boundedHarmonicPolyHomogeneousImageSubmodule (N : ℕ) : Submodule ℝ C(spherePoint3, ℝ) :=
  ⨆ i : Set.Iic N, harmonicPolyHomogeneousImageSubmodule i.1

theorem boundedHarmonicPolyHomogeneousImageSubmodule_eq_sphereCoordTotalDegreeImage
    (N : ℕ) :
    boundedHarmonicPolyHomogeneousImageSubmodule N =
      (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map sphereCoordMvEval.toLinearMap := by
  symm
  exact sphereCoordTotalDegreeImage_eq_iSup_harmonicPolyImage_Iic N

instance boundedHarmonicPolyHomogeneousImageSubmodule_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ (boundedHarmonicPolyHomogeneousImageSubmodule N) := by
  rw [boundedHarmonicPolyHomogeneousImageSubmodule_eq_sphereCoordTotalDegreeImage]
  infer_instance

theorem isClosed_boundedHarmonicPolyHomogeneousImageSubmodule (N : ℕ) :
    IsClosed
      ((boundedHarmonicPolyHomogeneousImageSubmodule N : Submodule ℝ C(spherePoint3, ℝ)) :
        Set C(spherePoint3, ℝ)) := by
  exact Submodule.closed_of_finiteDimensional _

theorem boundedHarmonicPolyHomogeneousImageSubmodule_le_continuousSpherePolynomialHomogeneousDegreeSubmodule
    (N : ℕ) :
    boundedHarmonicPolyHomogeneousImageSubmodule N ≤
      continuousSpherePolynomialHomogeneousDegreeSubmodule := by
  rw [boundedHarmonicPolyHomogeneousImageSubmodule_eq_sphereCoordTotalDegreeImage]
  rw [continuousSpherePolynomialHomogeneousDegreeSubmodule_eq_iSup_harmonicPolyHomogeneousImageSubmodule]
  exact (sphereCoordTotalDegreeImage_le_iSup_harmonicPolyImage_Iic N).trans <| by
    refine iSup_le ?_
    intro i
    exact le_iSup (fun n : ℕ => harmonicPolyHomogeneousImageSubmodule n) i.1

theorem boundedHarmonicPolyHomogeneousImageSubmodule_invariant_under_spherePrecomp
    (N : ℕ) (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3) :
    (boundedHarmonicPolyHomogeneousImageSubmodule N).map
        (spherePrecompLinearEquiv e).toLinearMap =
      boundedHarmonicPolyHomogeneousImageSubmodule N := by
  unfold boundedHarmonicPolyHomogeneousImageSubmodule
  rw [Submodule.map_iSup]
  refine iSup_congr ?_
  intro i
  exact harmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv e i.1

theorem continuousSphereFrameSubmodule_le_boundedHarmonicPolyImage_closure :
    continuousSphereFrameSubmodule ≤
      (⨆ N : ℕ, boundedHarmonicPolyHomogeneousImageSubmodule N).topologicalClosure := by
  rw [show (⨆ N : ℕ, boundedHarmonicPolyHomogeneousImageSubmodule N) =
      ⨆ N : ℕ, ⨆ i : Set.Iic N, harmonicPolyHomogeneousImageSubmodule i.1 by rfl]
  exact continuousSphereFrameSubmodule_le_iSup_Iic_harmonicPolyImage_closure
