import Gleason.Harmonic.HighDegree.EvenCoordPoly
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

noncomputable section

open Complex InnerProductSpace

def sphereCoordPolyEvenTotalDegreeSubmodule (N : ℕ) :
    Submodule ℝ (MvPolynomial (Fin 3) ℝ) :=
  sphereCoordPolyEvenSubmodule ⊓ MvPolynomial.restrictTotalDegree (Fin 3) ℝ N

instance sphereCoordPolyEvenTotalDegreeSubmodule_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ (sphereCoordPolyEvenTotalDegreeSubmodule N) := by
  letI : FiniteDimensional ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N) := by
    infer_instance
  exact Submodule.finiteDimensional_of_le inf_le_right

instance sphereCoordPolyEvenTotalDegreeSubmodule_map_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ
      ((sphereCoordPolyEvenTotalDegreeSubmodule N).map sphereCoordMvEval.toLinearMap) := by
  infer_instance

theorem sphereCoordPolyEvenSubmodule_eq_iSup_totalDegree :
    sphereCoordPolyEvenSubmodule =
      ⨆ N : ℕ, sphereCoordPolyEvenTotalDegreeSubmodule N := by
  refine le_antisymm ?_ ?_
  · intro p hp
    let N : ℕ := p.totalDegree
    have hpdeg : p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ N := by
      exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := N) p).2 le_rfl
    exact (le_iSup (fun N => sphereCoordPolyEvenTotalDegreeSubmodule N) N) ⟨hp, hpdeg⟩
  · refine iSup_le ?_
    intro N
    exact inf_le_left

theorem continuousSphereEvenCoordinateSubmodule_eq_iSup_totalDegree_map :
    continuousSphereEvenCoordinateSubmodule =
      ⨆ N : ℕ, (sphereCoordPolyEvenTotalDegreeSubmodule N).map sphereCoordMvEval.toLinearMap := by
  rw [continuousSphereEvenCoordinateSubmodule_eq_map_sphereCoordPolyEvenSubmodule]
  rw [sphereCoordPolyEvenSubmodule_eq_iSup_totalDegree]
  simpa using
    (Submodule.map_iSup (f := sphereCoordMvEval.toLinearMap)
      (p := fun N : ℕ => sphereCoordPolyEvenTotalDegreeSubmodule N))

def continuousSphereEvenPolynomialDegreeSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  ⨆ N : ℕ, (sphereCoordPolyEvenTotalDegreeSubmodule N).map sphereCoordMvEval.toLinearMap

theorem isClosed_continuousSphereEvenPolynomialDegreePiece (N : ℕ) :
    IsClosed
      (((sphereCoordPolyEvenTotalDegreeSubmodule N).map sphereCoordMvEval.toLinearMap :
        Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) := by
  exact Submodule.closed_of_finiteDimensional _

def continuousSphereEvenPolynomialDegreeClosedPiece (N : ℕ) :
    ClosedSubmodule ℝ C(spherePoint3, ℝ) :=
  ⟨(sphereCoordPolyEvenTotalDegreeSubmodule N).map sphereCoordMvEval.toLinearMap,
    isClosed_continuousSphereEvenPolynomialDegreePiece N⟩

theorem continuousSphereFrameSubmodule_le_evenPolynomialDegreeClosure :
    continuousSphereFrameSubmodule ≤
      continuousSphereEvenPolynomialDegreeSubmodule.topologicalClosure := by
  rw [show continuousSphereEvenPolynomialDegreeSubmodule =
      ⨆ N : ℕ, (sphereCoordPolyEvenTotalDegreeSubmodule N).map sphereCoordMvEval.toLinearMap
      by rfl]
  rw [← continuousSphereEvenCoordinateSubmodule_eq_iSup_totalDegree_map]
  exact continuousSphereFrameSubmodule_le_evenCoordinateClosure
