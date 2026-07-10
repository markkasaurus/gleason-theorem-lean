import Gleason.Harmonic.HighDegree.EvenCoordDegree
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

noncomputable section

open Complex InnerProductSpace

theorem restrictTotalDegree_eq_iSup_homogeneousSubmodule (N : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin 3) ℝ N =
      ⨆ i : Set.Iic N, MvPolynomial.homogeneousSubmodule (Fin 3) ℝ i := by
  refine le_antisymm ?_ ?_
  · intro p hp
    have hpdeg :
        p.totalDegree ≤ N :=
      (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := N) p).1 hp
    rw [← MvPolynomial.sum_homogeneousComponent (φ := p)]
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hi' : i ≤ N := by
      exact Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hpdeg
    show MvPolynomial.homogeneousComponent i p ∈
      ⨆ j : Set.Iic N, MvPolynomial.homogeneousSubmodule (Fin 3) ℝ ↑j
    have hle :
        MvPolynomial.homogeneousSubmodule (Fin 3) ℝ i ≤
          ⨆ j : Set.Iic N, MvPolynomial.homogeneousSubmodule (Fin 3) ℝ ↑j :=
      le_iSup (fun j : Set.Iic N => MvPolynomial.homogeneousSubmodule (Fin 3) ℝ ↑j)
        (⟨i, hi'⟩ : Set.Iic N)
    exact hle (MvPolynomial.homogeneousComponent_mem i p)
  · refine iSup_le ?_
    intro i p hp
    exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := N) p).2 <|
      le_trans hp.totalDegree_le i.2

theorem sphereCoordTotalDegreeImage_eq_iSup_homogeneousImage (N : ℕ) :
    (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map sphereCoordMvEval.toLinearMap =
      ⨆ i : Set.Iic N,
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ i).map sphereCoordMvEval.toLinearMap := by
  rw [restrictTotalDegree_eq_iSup_homogeneousSubmodule]
  exact
    (Submodule.map_iSup (f := sphereCoordMvEval.toLinearMap)
      (p := fun i : Set.Iic N => MvPolynomial.homogeneousSubmodule (Fin 3) ℝ i))

theorem homogeneousSubmodule_le_restrictTotalDegree (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n ≤
      MvPolynomial.restrictTotalDegree (Fin 3) ℝ n := by
  intro p hp
  exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := n) p).2 hp.totalDegree_le

instance homogeneousSubmodule_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) := by
  letI : FiniteDimensional ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ n) := by
    infer_instance
  exact Submodule.finiteDimensional_of_le (homogeneousSubmodule_le_restrictTotalDegree n)

instance homogeneousSubmodule_map_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ
      ((MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap) := by
  infer_instance

def continuousSpherePolynomialHomogeneousDegreeSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  ⨆ n : ℕ, (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap

theorem isClosed_continuousSpherePolynomialHomogeneousDegreePiece (n : ℕ) :
    IsClosed
      (((MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap :
        Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) := by
  exact Submodule.closed_of_finiteDimensional _

def continuousSpherePolynomialHomogeneousDegreeClosedPiece (n : ℕ) :
    ClosedSubmodule ℝ C(spherePoint3, ℝ) :=
  ⟨(MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap,
    isClosed_continuousSpherePolynomialHomogeneousDegreePiece n⟩

theorem continuousSphereEvenPolynomialDegreeSubmodule_le_polynomialHomogeneousDegreeSubmodule :
    continuousSphereEvenPolynomialDegreeSubmodule ≤
      continuousSpherePolynomialHomogeneousDegreeSubmodule := by
  refine iSup_le ?_
  intro N
  calc
    (sphereCoordPolyEvenTotalDegreeSubmodule N).map sphereCoordMvEval.toLinearMap
        ≤ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map sphereCoordMvEval.toLinearMap := by
            exact Submodule.map_mono inf_le_right
    _ = ⨆ i : Set.Iic N,
          (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ i).map
            sphereCoordMvEval.toLinearMap :=
          sphereCoordTotalDegreeImage_eq_iSup_homogeneousImage N
    _ ≤ continuousSpherePolynomialHomogeneousDegreeSubmodule := by
          refine iSup_le ?_
          intro i
          exact le_iSup (fun n : ℕ =>
            (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap) i.1

theorem continuousSphereFrameSubmodule_le_polynomialHomogeneousDegreeClosure :
    continuousSphereFrameSubmodule ≤
      continuousSpherePolynomialHomogeneousDegreeSubmodule.topologicalClosure := by
  calc
    continuousSphereFrameSubmodule
        ≤ continuousSphereEvenPolynomialDegreeSubmodule.topologicalClosure :=
          continuousSphereFrameSubmodule_le_evenPolynomialDegreeClosure
    _ ≤ continuousSpherePolynomialHomogeneousDegreeSubmodule.topologicalClosure :=
      Submodule.topologicalClosure_mono
        continuousSphereEvenPolynomialDegreeSubmodule_le_polynomialHomogeneousDegreeSubmodule
