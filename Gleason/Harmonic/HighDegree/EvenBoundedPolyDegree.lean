import Gleason.Harmonic.HighDegree.EvenBoundedPolyBridge
import Gleason.Harmonic.Auxiliary.CoordHomogeneousDegree

noncomputable section

open Complex InnerProductSpace

theorem sphereCoordPolyAntipode_mem_homogeneousSubmodule
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n) :
    sphereCoordPolyAntipode p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
  change ((MvPolynomial.bind₁ (fun i : Fin 3 => -MvPolynomial.X i) p)).IsHomogeneous n
  convert
    (MvPolynomial.IsHomogeneous.aeval (τ := Fin 3) (S := ℝ) hp
      (fun i : Fin 3 => -MvPolynomial.X i) (fun i => by
        simpa using (MvPolynomial.isHomogeneous_X (R := ℝ) i).neg)) using 1
  · simp

theorem sphereCoordPolyAntipode_mem_restrictTotalDegree
    {N : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ N) :
    sphereCoordPolyAntipode p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ N := by
  rw [restrictTotalDegree_eq_iSup_homogeneousSubmodule] at hp ⊢
  refine Submodule.iSup_induction
      (p := fun i : Set.Iic N => MvPolynomial.homogeneousSubmodule (Fin 3) ℝ i.1)
      (motive := fun q =>
        sphereCoordPolyAntipode q ∈ ⨆ i : Set.Iic N, MvPolynomial.homogeneousSubmodule (Fin 3) ℝ i.1)
      hp
      ?_ ?_ ?_
  · intro i q hq
    exact
      le_iSup (fun j : Set.Iic N => MvPolynomial.homogeneousSubmodule (Fin 3) ℝ j.1) i
        (sphereCoordPolyAntipode_mem_homogeneousSubmodule hq)
  · simp [sphereCoordPolyAntipode]
  · intro q r hq hr
    simpa [map_add] using Submodule.add_mem _ hq hr

theorem sphereCoordPolyEvenSymm_mem_restrictTotalDegree
    {N : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ N) :
    sphereCoordPolyEvenSymm p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ N := by
  rw [sphereCoordPolyEvenSymm_apply]
  exact Submodule.smul_mem _ ((2 : ℝ)⁻¹)
    (Submodule.add_mem _ hp (sphereCoordPolyAntipode_mem_restrictTotalDegree hp))

theorem exists_even_mvPolynomial_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule_degree
    {N : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ (2 * N) ∧
      sphereCoordMvEval p = f ∧ sphereCoordPolyAntipode p = p := by
  have hfBounded :
      f ∈ boundedHarmonicPolyHomogeneousImageSubmodule (2 * N) :=
    evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_boundedHarmonicPolyHomogeneousImageSubmodule
      N hf
  rw [boundedHarmonicPolyHomogeneousImageSubmodule_eq_sphereCoordTotalDegreeImage] at hfBounded
  rcases hfBounded with ⟨q, hqdeg, hqeval⟩
  refine ⟨sphereCoordPolyEvenSymm q, sphereCoordPolyEvenSymm_mem_restrictTotalDegree hqdeg, ?_, ?_⟩
  · rw [sphereCoordMvEval_evenSymm]
    change sphereEvenSymm (sphereCoordMvEval.toLinearMap q) = f
    rw [hqeval]
    exact sphereEvenSymm_eq_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule hf
  · exact sphereCoordPolyAntipode_evenSymm q
