import Gleason.Harmonic.Fischer.FischerHarmonicBridge

noncomputable section

open Complex InnerProductSpace

theorem homogeneousSubmodule_le_harmonicPolyHomogeneousSubmodule_of_lt_two
    {n : ℕ} (hn : n < 2) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n ≤ harmonicPolyHomogeneousSubmodule n := by
  intro p hp
  refine ⟨hp, ?_⟩
  simpa [LinearMap.mem_ker] using
    polyLaplacian_eq_zero_of_mem_homogeneousSubmodule_mod_two_lt_two hp hn

theorem homogeneousImage_le_continuousHarmonicSphereDegreeSubmodule_of_lt_two
    {n : ℕ} (hn : n < 2) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap ≤
      continuousHarmonicSphereDegreeSubmodule n := by
  calc
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap
      ≤ (harmonicPolyHomogeneousSubmodule n).map sphereCoordMvEval.toLinearMap := by
          exact Submodule.map_mono (homogeneousSubmodule_le_harmonicPolyHomogeneousSubmodule_of_lt_two hn)
    _ ≤ continuousHarmonicSphereDegreeSubmodule n :=
      harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule n

theorem homogeneousImage_le_iSup_continuousHarmonicSphereDegreeSubmodule (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap ≤
      ⨆ k : ℕ, continuousHarmonicSphereDegreeSubmodule k := by
  induction n using Nat.twoStepInduction with
  | zero =>
      exact (homogeneousImage_le_continuousHarmonicSphereDegreeSubmodule_of_lt_two (by omega)).trans
        (le_iSup (fun k : ℕ => continuousHarmonicSphereDegreeSubmodule k) 0)
  | one =>
      exact (homogeneousImage_le_continuousHarmonicSphereDegreeSubmodule_of_lt_two (by omega)).trans
        (le_iSup (fun k : ℕ => continuousHarmonicSphereDegreeSubmodule k) 1)
  | more n ihn _ =>
      calc
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n + 2)).map sphereCoordMvEval.toLinearMap
          ≤ continuousHarmonicSphereDegreeSubmodule (n + 2) ⊔
              (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap :=
            by simpa using homogeneousImage_le_continuousHarmonicSphere_sup_prev (n + 2)
        _ ≤ ⨆ k : ℕ, continuousHarmonicSphereDegreeSubmodule k := by
            rw [sup_le_iff]
            exact ⟨le_iSup (fun k : ℕ => continuousHarmonicSphereDegreeSubmodule k) (n + 2), ihn⟩

theorem continuousSpherePolynomialHomogeneousDegreeSubmodule_le_iSup_continuousHarmonicSphereDegreeSubmodule :
    continuousSpherePolynomialHomogeneousDegreeSubmodule ≤
      ⨆ k : ℕ, continuousHarmonicSphereDegreeSubmodule k := by
  refine iSup_le ?_
  intro n
  exact homogeneousImage_le_iSup_continuousHarmonicSphereDegreeSubmodule n

theorem continuousSphereFrameSubmodule_le_iSup_continuousHarmonicSphereDegreeSubmodule_closure :
    continuousSphereFrameSubmodule ≤
      (⨆ k : ℕ, continuousHarmonicSphereDegreeSubmodule k).topologicalClosure := by
  calc
    continuousSphereFrameSubmodule ≤
      continuousSpherePolynomialHomogeneousDegreeSubmodule.topologicalClosure :=
        continuousSphereFrameSubmodule_le_polynomialHomogeneousDegreeClosure
    _ ≤ (⨆ k : ℕ, continuousHarmonicSphereDegreeSubmodule k).topologicalClosure :=
      Submodule.topologicalClosure_mono
        continuousSpherePolynomialHomogeneousDegreeSubmodule_le_iSup_continuousHarmonicSphereDegreeSubmodule
