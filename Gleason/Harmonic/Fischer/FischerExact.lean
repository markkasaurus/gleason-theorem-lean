import Gleason.Harmonic.Fischer.FischerSectorClosure
import Gleason.Harmonic.Fischer.FischerBasic

noncomputable section

open Complex InnerProductSpace

def harmonicPolyHomogeneousImageSubmodule (n : ℕ) : Submodule ℝ C(spherePoint3, ℝ) :=
  (harmonicPolyHomogeneousSubmodule n).map sphereCoordMvEval.toLinearMap

theorem harmonicPolyHomogeneousImageSubmodule_le_homogeneousImage (n : ℕ) :
    harmonicPolyHomogeneousImageSubmodule n ≤
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap := by
  exact Submodule.map_mono inf_le_left

theorem homogeneousImage_eq_harmonicPolyImage_of_lt_two
    {n : ℕ} (hn : n < 2) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap =
      harmonicPolyHomogeneousImageSubmodule n := by
  apply le_antisymm
  · rintro f ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    refine ⟨hp, ?_⟩
    simpa [LinearMap.mem_ker] using
      polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_mod_two_lt_two hp hn
  · exact harmonicPolyHomogeneousImageSubmodule_le_homogeneousImage n

theorem homogeneousImage_eq_harmonicPolyImage_sup_prev
    {n : ℕ} (hn : 2 ≤ n) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap =
      harmonicPolyHomogeneousImageSubmodule n ⊔
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap := by
  apply le_antisymm
  · exact homogeneousImage_le_harmonicPolyImage_sup_prev n
  · exact sup_le_iff.2
      ⟨harmonicPolyHomogeneousImageSubmodule_le_homogeneousImage n,
        by
          rintro f ⟨p, hp, rfl⟩
          refine ⟨rhoPoly * p, ?_, ?_⟩
          · simpa [Nat.sub_add_cancel hn, add_assoc, add_left_comm, add_comm] using
              smul_rhoPoly_mem_homogeneousSubmodule_succ_two hp (1 : ℝ)
          · simpa [sphereCoordMvEval_rhoPoly_mul]⟩

theorem homogeneousImage_le_iSup_harmonicPolyHomogeneousImageSubmodule (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap ≤
      ⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule k := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [homogeneousImage_eq_harmonicPolyImage_of_lt_two (by omega)]
      exact le_iSup harmonicPolyHomogeneousImageSubmodule 0
  | one =>
      rw [homogeneousImage_eq_harmonicPolyImage_of_lt_two (by omega)]
      exact le_iSup harmonicPolyHomogeneousImageSubmodule 1
  | more n ihn _ =>
      calc
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2)).map sphereCoordMvEval.toLinearMap
            = harmonicPolyHomogeneousImageSubmodule (n + 2) ⊔
                (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap := by
                  simpa using homogeneousImage_eq_harmonicPolyImage_sup_prev (n := n + 2) (by omega)
        _ ≤ ⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule k := by
            rw [sup_le_iff]
            exact ⟨le_iSup harmonicPolyHomogeneousImageSubmodule (n + 2), ihn⟩

theorem continuousSpherePolynomialHomogeneousDegreeSubmodule_le_iSup_harmonicPolyHomogeneousImageSubmodule :
    continuousSpherePolynomialHomogeneousDegreeSubmodule ≤
      ⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule k := by
  refine iSup_le ?_
  intro n
  exact homogeneousImage_le_iSup_harmonicPolyHomogeneousImageSubmodule n

theorem iSup_harmonicPolyHomogeneousImageSubmodule_le_continuousSpherePolynomialHomogeneousDegreeSubmodule :
    (⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule k) ≤
      continuousSpherePolynomialHomogeneousDegreeSubmodule := by
  refine iSup_le ?_
  intro n
  calc
    harmonicPolyHomogeneousImageSubmodule n
      ≤ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap :=
        harmonicPolyHomogeneousImageSubmodule_le_homogeneousImage n
    _ ≤ continuousSpherePolynomialHomogeneousDegreeSubmodule :=
      le_iSup (fun k : ℕ =>
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ k).map sphereCoordMvEval.toLinearMap) n

theorem continuousSpherePolynomialHomogeneousDegreeSubmodule_eq_iSup_harmonicPolyHomogeneousImageSubmodule :
    continuousSpherePolynomialHomogeneousDegreeSubmodule =
      ⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule k := by
  exact le_antisymm
    continuousSpherePolynomialHomogeneousDegreeSubmodule_le_iSup_harmonicPolyHomogeneousImageSubmodule
    iSup_harmonicPolyHomogeneousImageSubmodule_le_continuousSpherePolynomialHomogeneousDegreeSubmodule

theorem continuousSphereFrameSubmodule_le_iSup_harmonicPolyHomogeneousImageSubmodule_closure :
    continuousSphereFrameSubmodule ≤
      (⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule k).topologicalClosure := by
  calc
    continuousSphereFrameSubmodule ≤
        continuousSpherePolynomialHomogeneousDegreeSubmodule.topologicalClosure :=
      continuousSphereFrameSubmodule_le_polynomialHomogeneousDegreeClosure
    _ ≤ (⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule k).topologicalClosure :=
      by
        rw [continuousSpherePolynomialHomogeneousDegreeSubmodule_eq_iSup_harmonicPolyHomogeneousImageSubmodule]
