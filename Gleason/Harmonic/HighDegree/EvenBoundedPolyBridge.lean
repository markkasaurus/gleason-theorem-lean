import Gleason.Harmonic.Fischer.FischerEvenBounded
import Gleason.Harmonic.HighDegree.EvenCoordPoly

noncomputable section

open Complex InnerProductSpace

theorem sphereEvenSymm_eq_of_mem_harmonicPolyHomogeneousImageSubmodule_even
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
      fin_cases i <;>
        simp [sphereAntipode_apply_val, sphereCoordVec, sphereCoordRe, sphereCoordIm,
          sphereCoordZ]
    rw [hcoords]
    exact eval_smul_of_isHomogeneous hp.1 (-1) (fun i => sphereCoordVec i x)
  change ((2 : ℝ)⁻¹) * (sphereCoordMvEval p x + sphereCoordMvEval p (sphereAntipode x)) =
      sphereCoordMvEval p x
  rw [hant, hn.neg_one_pow]
  ring

theorem sphereEvenSymm_eq_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    sphereEvenSymm f = f := by
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule] at hf
  refine Submodule.iSup_induction
      (p := fun i : Set.Iic N => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
      (motive := fun g => sphereEvenSymm g = g) hf ?_ ?_ ?_
  · intro i g hg
    exact sphereEvenSymm_eq_of_mem_harmonicPolyHomogeneousImageSubmodule_even (even_two_mul i.1) hg
  · ext x
    simp [sphereEvenSymm_apply]
  · intro g h hg hh
    ext x
    have hgx : sphereEvenSymm g x = g x := congrArg (fun f : C(spherePoint3, ℝ) => f x) hg
    have hhx : sphereEvenSymm h x = h x := congrArg (fun f : C(spherePoint3, ℝ) => f x) hh
    simp [sphereEvenSymm_apply] at hgx hhx ⊢
    linarith

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_boundedHarmonicPolyHomogeneousImageSubmodule
    (N : ℕ) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      boundedHarmonicPolyHomogeneousImageSubmodule (2 * N) := by
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule]
  refine iSup_le ?_
  intro i
  have hi : i.1 ≤ N := i.2
  exact
    (le_iSup (fun j : Set.Iic (2 * N) => harmonicPolyHomogeneousImageSubmodule j.1)
      ⟨2 * i.1, Nat.mul_le_mul_left 2 hi⟩)

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereEvenCoordinateSubmodule
    (N : ℕ) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      continuousSphereEvenCoordinateSubmodule := by
  intro f hf
  have hfBounded :
      f ∈ boundedHarmonicPolyHomogeneousImageSubmodule (2 * N) :=
    evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_boundedHarmonicPolyHomogeneousImageSubmodule
      N hf
  have hcoord :
      f ∈ sphereCoordinateSubalgebra.toSubmodule := by
    rw [boundedHarmonicPolyHomogeneousImageSubmodule_eq_sphereCoordTotalDegreeImage] at hfBounded
    rcases hfBounded with ⟨p, hpdeg, rfl⟩
    rw [sphereCoordinateSubalgebra_eq_range_sphereCoordMvEval]
    exact ⟨p, rfl⟩
  have heven :
      f ∈ continuousSphereEvenSubmodule := by
    intro x
    have hfix := congrArg (fun g : C(spherePoint3, ℝ) => g x)
      (sphereEvenSymm_eq_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule hf)
    have hfix' : ((2 : ℝ)⁻¹) * (f x + f (sphereAntipode x)) = f x := by
      simpa [sphereEvenSymm_apply] using hfix
    linarith
  exact ⟨hcoord, heven⟩

theorem exists_even_mvPolynomial_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      sphereCoordMvEval p = f ∧ sphereCoordPolyAntipode p = p := by
  exact
    exists_even_mvPolynomial_of_mem_continuousSphereEvenCoordinateSubmodule
      (evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereEvenCoordinateSubmodule
        N hf)
