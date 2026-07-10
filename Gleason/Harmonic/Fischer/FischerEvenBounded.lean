import Gleason.Harmonic.Fischer.FischerBoundedClosure
import Gleason.Harmonic.HighDegree.EvenDensity
import Gleason.Harmonic.Fischer.FischerFrameIntersection
import Gleason.Harmonic.HighDegree.EvenCoordDegree
import Mathlib.Algebra.Ring.Parity

noncomputable section

open Complex InnerProductSpace

def evenBoundedHarmonicPolyHomogeneousImageSubmodule (N : ℕ) :
    Submodule ℝ C(spherePoint3, ℝ) :=
  ⨆ i : Set.Iic N, harmonicPolyHomogeneousImageSubmodule (2 * i.1)

private theorem sphereEvenSymm_eq_of_mem_harmonicPolyHomogeneousImageSubmodule_even
    {n : ℕ} (hn : Even n) {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule n) :
    sphereEvenSymm f = f := by
  rcases hf with ⟨p, hp, rfl⟩
  ext x
  rw [sphereEvenSymm_apply]
  have hant :
      sphereCoordMvEval p (sphereAntipode x) = (-1 : ℝ) ^ n * sphereCoordMvEval p x := by
    rw [sphereCoordMvEval_apply, sphereCoordMvEval_apply]
    have hcoords :
        (fun i => sphereCoordVec i (sphereAntipode x)) =
          fun i => (-1 : ℝ) * sphereCoordVec i x := by
      funext i
      fin_cases i <;> simp [sphereAntipode, sphereCoordVec, sphereCoordRe, sphereCoordIm, sphereCoordZ]
    rw [hcoords]
    exact eval_smul_of_isHomogeneous hp.1 (-1) (fun i => sphereCoordVec i x)
  change ((2 : ℝ)⁻¹) * (sphereCoordMvEval p x + sphereCoordMvEval p (sphereAntipode x)) =
      sphereCoordMvEval p x
  rw [hant, hn.neg_one_pow]
  ring

private theorem sphereEvenSymm_eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule_odd
    {n : ℕ} (hn : Odd n) {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule n) :
    sphereEvenSymm f = 0 := by
  rcases hf with ⟨p, hp, rfl⟩
  ext x
  rw [sphereEvenSymm_apply]
  have hant :
      sphereCoordMvEval p (sphereAntipode x) = (-1 : ℝ) ^ n * sphereCoordMvEval p x := by
    rw [sphereCoordMvEval_apply, sphereCoordMvEval_apply]
    have hcoords :
        (fun i => sphereCoordVec i (sphereAntipode x)) =
          fun i => (-1 : ℝ) * sphereCoordVec i x := by
      funext i
      fin_cases i <;> simp [sphereAntipode, sphereCoordVec, sphereCoordRe, sphereCoordIm, sphereCoordZ]
    rw [hcoords]
    exact eval_smul_of_isHomogeneous hp.1 (-1) (fun i => sphereCoordVec i x)
  change ((2 : ℝ)⁻¹) * (sphereCoordMvEval p x + sphereCoordMvEval p (sphereAntipode x)) = 0
  rw [hant, hn.neg_one_pow]
  ring

private theorem map_sphereEvenSymmLinear_harmonicPolyHomogeneousImageSubmodule_even
    {n : ℕ} (hn : Even n) :
    (harmonicPolyHomogeneousImageSubmodule n).map sphereEvenSymmLinear =
      harmonicPolyHomogeneousImageSubmodule n := by
  refine le_antisymm ?_ ?_
  · rintro f ⟨g, hg, rfl⟩
    have hfix : sphereEvenSymmLinear g = g := by
      simpa [sphereEvenSymm] using
        sphereEvenSymm_eq_of_mem_harmonicPolyHomogeneousImageSubmodule_even hn hg
    rw [hfix]
    exact hg
  · intro f hf
    exact ⟨f, hf,
      by simpa [sphereEvenSymm] using
        sphereEvenSymm_eq_of_mem_harmonicPolyHomogeneousImageSubmodule_even hn hf⟩

private theorem map_sphereEvenSymmLinear_harmonicPolyHomogeneousImageSubmodule_odd
    {n : ℕ} (hn : Odd n) :
    (harmonicPolyHomogeneousImageSubmodule n).map sphereEvenSymmLinear = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rcases hf with ⟨g, hg, rfl⟩
  simpa [sphereEvenSymm] using
    sphereEvenSymm_eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule_odd hn hg

theorem sphereEvenSymm_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ boundedHarmonicPolyHomogeneousImageSubmodule N) :
    sphereEvenSymm f ∈ evenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  have hmap :
      (boundedHarmonicPolyHomogeneousImageSubmodule N).map sphereEvenSymmLinear ≤
        evenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
    rw [boundedHarmonicPolyHomogeneousImageSubmodule, evenBoundedHarmonicPolyHomogeneousImageSubmodule]
    rw [Submodule.map_iSup (f := sphereEvenSymmLinear)
      (p := fun i : Set.Iic N => harmonicPolyHomogeneousImageSubmodule i.1)]
    refine iSup_le ?_
    intro i
    rcases Nat.even_or_odd i.1 with hiEven | hiOdd
    · rcases hiEven with ⟨k, hk⟩
      have hkEq : i.1 = 2 * k := by simpa [two_mul] using hk
      have hkN : k ≤ N := by
        calc
          k ≤ 2 * k := by omega
          _ = i.1 := hkEq.symm
          _ ≤ N := i.2
      calc
        (harmonicPolyHomogeneousImageSubmodule i.1).map sphereEvenSymmLinear
            = (harmonicPolyHomogeneousImageSubmodule (2 * k)).map sphereEvenSymmLinear := by
              rw [hkEq]
        _ = harmonicPolyHomogeneousImageSubmodule (2 * k) :=
              map_sphereEvenSymmLinear_harmonicPolyHomogeneousImageSubmodule_even (even_two_mul _)
        _ ≤ ⨆ j : Set.Iic N, harmonicPolyHomogeneousImageSubmodule (2 * j.1) :=
          le_iSup (fun j : Set.Iic N => harmonicPolyHomogeneousImageSubmodule (2 * j.1))
            ⟨k, hkN⟩
    · rw [map_sphereEvenSymmLinear_harmonicPolyHomogeneousImageSubmodule_odd hiOdd]
      exact bot_le
  have hfMap : sphereEvenSymm f ∈
      (boundedHarmonicPolyHomogeneousImageSubmodule N).map sphereEvenSymmLinear := by
    exact ⟨f, hf, rfl⟩
  exact hmap hfMap

theorem sphereCoordPolyEvenTotalDegreeSubmodule_map_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
    (N : ℕ) :
    (sphereCoordPolyEvenTotalDegreeSubmodule N).map sphereCoordMvEval.toLinearMap ≤
      evenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  rintro f ⟨p, hp, rfl⟩
  have hbounded : sphereCoordMvEval p ∈ boundedHarmonicPolyHomogeneousImageSubmodule N := by
    rw [boundedHarmonicPolyHomogeneousImageSubmodule_eq_sphereCoordTotalDegreeImage]
    exact ⟨p, hp.2, rfl⟩
  have heven :
      sphereEvenSymm (sphereCoordMvEval p) = sphereCoordMvEval p := by
    exact sphereEvenSymm_eq_of_mem_continuousSphereEvenSubmodule
      (sphereCoordMvEval_mem_continuousSphereEvenCoordinateSubmodule_of_mem_evenSubmodule hp.1).2
  have hs :
      sphereEvenSymm (sphereCoordMvEval p) ∈
        evenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    sphereEvenSymm_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule hbounded
  simpa [heven] using hs

theorem continuousSphereEvenPolynomialDegreeSubmodule_le_evenBoundedHarmonicPolyImage :
    continuousSphereEvenPolynomialDegreeSubmodule ≤
      ⨆ N : ℕ, evenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  refine iSup_le ?_
  intro N
  exact (sphereCoordPolyEvenTotalDegreeSubmodule_map_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
    N).trans <|
      le_iSup (fun N : ℕ => evenBoundedHarmonicPolyHomogeneousImageSubmodule N) N

theorem continuousSphereFrameSubmodule_le_evenBoundedHarmonicPolyImage_closure :
    continuousSphereFrameSubmodule ≤
      (⨆ N : ℕ, evenBoundedHarmonicPolyHomogeneousImageSubmodule N).topologicalClosure := by
  exact
    (continuousSphereFrameSubmodule_le_evenPolynomialDegreeClosure).trans <|
      Submodule.topologicalClosure_mono
        continuousSphereEvenPolynomialDegreeSubmodule_le_evenBoundedHarmonicPolyImage

theorem iSup_evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_iSup_even_harmonicPoly :
    (⨆ N : ℕ, evenBoundedHarmonicPolyHomogeneousImageSubmodule N) =
      ⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule (2 * k) := by
  unfold evenBoundedHarmonicPolyHomogeneousImageSubmodule
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro N
    refine iSup_le ?_
    intro i
    exact le_iSup (fun k : ℕ => harmonicPolyHomogeneousImageSubmodule (2 * k)) i.1
  · refine iSup_le ?_
    intro k
    exact le_iSup_of_le k <|
      le_iSup (fun i : Set.Iic k => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
        ⟨k, by simpa using (le_rfl : k ≤ k)⟩

theorem continuousSphereFrameSubmodule_le_even_harmonicPolyImage_closure :
    continuousSphereFrameSubmodule ≤
      (⨆ k : ℕ, harmonicPolyHomogeneousImageSubmodule (2 * k)).topologicalClosure := by
  rw [← iSup_evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_iSup_even_harmonicPoly]
  exact continuousSphereFrameSubmodule_le_evenBoundedHarmonicPolyImage_closure
