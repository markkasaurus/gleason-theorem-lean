import Gleason.Harmonic.Fischer.FischerExact
import Gleason.Harmonic.Auxiliary.CoordHomogeneousDegree

noncomputable section

open Complex InnerProductSpace

def continuousSpherePolynomialHarmonicDegreeSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  ⨆ n : ℕ, harmonicPolyHomogeneousImageSubmodule n

private theorem homogeneousSubmodule_le_restrictTotalDegree_of_le
    {n N : ℕ} (hnN : n ≤ N) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n ≤
      MvPolynomial.restrictTotalDegree (Fin 3) ℝ N := by
  intro p hp
  exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := N) p).2 <|
    le_trans hp.totalDegree_le hnN

theorem homogeneousImage_le_iSup_harmonicPolyImage_Iic (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap ≤
      ⨆ i : Set.Iic n, harmonicPolyHomogeneousImageSubmodule i := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [homogeneousImage_eq_harmonicPolyImage_of_lt_two (by omega)]
      exact le_iSup (fun i : Set.Iic 0 => harmonicPolyHomogeneousImageSubmodule i.1) ⟨0, le_rfl⟩
  | one =>
      rw [homogeneousImage_eq_harmonicPolyImage_of_lt_two (by omega)]
      exact le_iSup (fun i : Set.Iic 1 => harmonicPolyHomogeneousImageSubmodule i.1) ⟨1, le_rfl⟩
  | more n ihn _ =>
      calc
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2)).map sphereCoordMvEval.toLinearMap
            = harmonicPolyHomogeneousImageSubmodule (n + 2) ⊔
                (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap := by
                  simpa using homogeneousImage_eq_harmonicPolyImage_sup_prev (n := n + 2) (by omega)
        _ ≤ ⨆ i : Set.Iic (n + 2), harmonicPolyHomogeneousImageSubmodule i.1 := by
          rw [sup_le_iff]
          exact ⟨
            le_iSup (fun i : Set.Iic (n + 2) => harmonicPolyHomogeneousImageSubmodule i.1)
              (⟨n + 2, show n + 2 ≤ n + 2 from le_rfl⟩ : Set.Iic (n + 2)),
            ihn.trans <| by
              refine iSup_le ?_
              intro i
              exact le_iSup (fun j : Set.Iic (n + 2) => harmonicPolyHomogeneousImageSubmodule j.1)
                ⟨i.1, Nat.le_trans i.2 (by omega)⟩
          ⟩

theorem sphereCoordTotalDegreeImage_le_iSup_harmonicPolyImage_Iic (N : ℕ) :
    (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map sphereCoordMvEval.toLinearMap ≤
      ⨆ i : Set.Iic N, harmonicPolyHomogeneousImageSubmodule i := by
  rw [sphereCoordTotalDegreeImage_eq_iSup_homogeneousImage]
  refine iSup_le ?_
  intro i
  exact (homogeneousImage_le_iSup_harmonicPolyImage_Iic i.1).trans <| by
    refine iSup_le ?_
    intro j
    exact le_iSup (fun k : Set.Iic N => harmonicPolyHomogeneousImageSubmodule k.1)
      ⟨j.1, Nat.le_trans j.2 i.2⟩

theorem iSup_harmonicPolyImage_Iic_le_sphereCoordTotalDegreeImage (N : ℕ) :
    (⨆ i : Set.Iic N, harmonicPolyHomogeneousImageSubmodule i) ≤
      (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map sphereCoordMvEval.toLinearMap := by
  refine iSup_le ?_
  intro i
  calc
    harmonicPolyHomogeneousImageSubmodule i.1
      ≤ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ i.1).map sphereCoordMvEval.toLinearMap :=
        harmonicPolyHomogeneousImageSubmodule_le_homogeneousImage i.1
    _ ≤ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map sphereCoordMvEval.toLinearMap :=
      Submodule.map_mono (homogeneousSubmodule_le_restrictTotalDegree_of_le i.2)

theorem sphereCoordTotalDegreeImage_eq_iSup_harmonicPolyImage_Iic (N : ℕ) :
    (MvPolynomial.restrictTotalDegree (Fin 3) ℝ N).map sphereCoordMvEval.toLinearMap =
      ⨆ i : Set.Iic N, harmonicPolyHomogeneousImageSubmodule i := by
  exact le_antisymm
    (sphereCoordTotalDegreeImage_le_iSup_harmonicPolyImage_Iic N)
    (iSup_harmonicPolyImage_Iic_le_sphereCoordTotalDegreeImage N)

theorem continuousSpherePolynomialHomogeneousDegreeSubmodule_eq_continuousSpherePolynomialHarmonicDegreeSubmodule :
    continuousSpherePolynomialHomogeneousDegreeSubmodule =
      continuousSpherePolynomialHarmonicDegreeSubmodule := by
  unfold continuousSpherePolynomialHarmonicDegreeSubmodule
  exact continuousSpherePolynomialHomogeneousDegreeSubmodule_eq_iSup_harmonicPolyHomogeneousImageSubmodule

theorem continuousSpherePolynomialHomogeneousDegreeSubmodule_eq_iSup_Iic_harmonicPolyImage :
    continuousSpherePolynomialHomogeneousDegreeSubmodule =
      ⨆ N : ℕ, ⨆ i : Set.Iic N, harmonicPolyHomogeneousImageSubmodule i.1 := by
  rw [continuousSpherePolynomialHomogeneousDegreeSubmodule_eq_continuousSpherePolynomialHarmonicDegreeSubmodule]
  unfold continuousSpherePolynomialHarmonicDegreeSubmodule
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro n
    exact le_iSup_of_le n <|
      le_iSup (fun i : Set.Iic n => harmonicPolyHomogeneousImageSubmodule i.1)
        (⟨n, show n ≤ n from le_rfl⟩ : Set.Iic n)
  · refine iSup_le ?_
    intro N
    exact iSup_le fun i =>
      le_iSup (fun n : ℕ => harmonicPolyHomogeneousImageSubmodule n) i.1

theorem continuousSphereFrameSubmodule_le_iSup_Iic_harmonicPolyImage_closure :
    continuousSphereFrameSubmodule ≤
      (⨆ N : ℕ, ⨆ i : Set.Iic N, harmonicPolyHomogeneousImageSubmodule i.1).topologicalClosure := by
  rw [← continuousSpherePolynomialHomogeneousDegreeSubmodule_eq_iSup_Iic_harmonicPolyImage]
  exact continuousSphereFrameSubmodule_le_polynomialHomogeneousDegreeClosure
