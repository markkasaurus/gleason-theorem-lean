import Gleason.Harmonic.Fischer.FischerBoundedClosure
import Gleason.Harmonic.Fischer.FischerHarmonicBridge

noncomputable section

open Complex InnerProductSpace

theorem exists_harmonic_mvPolynomial_of_mem_boundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ boundedHarmonicPolyHomogeneousImageSubmodule N) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ N ∧
      polyLaplacian p = 0 ∧
      sphereCoordMvEval p = f := by
  rw [boundedHarmonicPolyHomogeneousImageSubmodule] at hf
  refine Submodule.iSup_induction
      (p := fun i : Set.Iic N => harmonicPolyHomogeneousImageSubmodule i.1)
      (motive := fun g =>
        ∃ p : MvPolynomial (Fin 3) ℝ,
          p ∈ MvPolynomial.restrictTotalDegree (Fin 3) ℝ N ∧
          polyLaplacian p = 0 ∧
          sphereCoordMvEval p = g)
      hf
      ?_ ?_ ?_
  · intro i g hg
    rcases hg with ⟨p, hp, rfl⟩
    refine ⟨p, ?_, ?_, rfl⟩
    · exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := N) p).2 <|
        le_trans hp.1.totalDegree_le i.2
    · simpa [harmonicPolyHomogeneousSubmodule, LinearMap.mem_ker] using hp.2
  · refine ⟨0, by simp, by simp, by ext x; simp⟩
  · intro g h hg hh
    rcases hg with ⟨p, hpdeg, hpΔ, hpEval⟩
    rcases hh with ⟨q, hqdeg, hqΔ, hqEval⟩
    refine ⟨p + q, Submodule.add_mem _ hpdeg hqdeg, ?_, ?_⟩
    · rw [LinearMap.map_add, hpΔ, hqΔ]
      simp
    rw [map_add, hpEval, hqEval]
