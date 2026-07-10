import Gleason.Harmonic.HighDegree.EvenBoundedWitness
import Gleason.Harmonic.HighDegree.EvenLowSliceIntersection
import Gleason.Harmonic.Fischer.FischerEvenBounded
import Gleason.Harmonic.Fischer.FischerFrameIntersection
import Gleason.Harmonic.Fischer.FischerPairwise

noncomputable section

open Complex InnerProductSpace

def highEvenBoundedHarmonicPolyHomogeneousImageSubmodule (N : ℕ) :
    Submodule ℝ C(spherePoint3, ℝ) :=
  (Finset.Icc 2 N).sup fun k => harmonicPolyHomogeneousImageSubmodule (2 * k)

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
    (N : ℕ) :
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      evenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  unfold highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule]
  refine Finset.sup_le ?_
  intro k hk
  exact le_iSup (fun i : Set.Iic N => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
    ⟨k, (Finset.mem_Icc.mp hk).2⟩

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_boundedHarmonicPolyHomogeneousImageSubmodule
    (N : ℕ) :
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      boundedHarmonicPolyHomogeneousImageSubmodule (2 * N) := by
  unfold highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
  rw [boundedHarmonicPolyHomogeneousImageSubmodule]
  refine Finset.sup_le ?_
  intro k hk
  exact le_iSup (fun i : Set.Iic (2 * N) => harmonicPolyHomogeneousImageSubmodule i.1)
    ⟨2 * k, by
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      exact Nat.mul_le_mul_left 2 hkN⟩

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_invariant_under_spherePrecomp
    (N : ℕ) (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3) :
    (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).map
        (spherePrecompLinearEquiv e).toLinearMap =
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  unfold highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
  simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup]
  refine iSup_congr ?_
  intro k
  refine iSup_congr ?_
  intro hk
  exact harmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv e (2 * k)

theorem isClosed_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule (N : ℕ) :
    IsClosed
      ((highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :
        Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) := by
  letI : FiniteDimensional ℝ
      ↥(highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) :=
    Submodule.finiteDimensional_of_le
      (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_boundedHarmonicPolyHomogeneousImageSubmodule N)
  exact Submodule.closed_of_finiteDimensional _

theorem eq_bot_of_isClosed_of_rotationInvariant_of_le_highEvenBounded_of_le_frame_of_disjoint_low
    {N : ℕ} {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGbounded : G ≤ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hGframe : G ≤ continuousSphereFrameSubmodule)
    (hGlow : Disjoint G lowHarmonicPolyHomogeneousImageSubmodule) :
    G = ⊥ := by
  by_contra hGne
  rcases exists_nonzero_mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isClosed_of_rotationInvariant_of_le_evenBounded_of_le_frame
      hGclosed hGrot
      ((hGbounded).trans
        (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
          N))
      hGframe hGne with
    ⟨g, hgG, hgne, hgLow⟩
  have hzero :
      g = 0 := by
    exact (Submodule.disjoint_def.mp hGlow) g hgG hgLow
  exact hgne hzero
