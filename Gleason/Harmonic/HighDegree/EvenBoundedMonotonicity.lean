import Gleason.Harmonic.HighDegree.EvenBoundedProjection

noncomputable section

open Complex InnerProductSpace

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_mono
    {N M : ℕ} (hNM : N ≤ M) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      evenBoundedHarmonicPolyHomogeneousImageSubmodule M := by
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule,
    evenBoundedHarmonicPolyHomogeneousImageSubmodule]
  refine iSup_le ?_
  intro i
  exact le_iSup
    (fun j : Set.Iic M => harmonicPolyHomogeneousImageSubmodule (2 * j.1))
    ⟨i.1, le_trans i.2 hNM⟩

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono
    {N M : ℕ} (hNM : N ≤ M) :
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule M := by
  unfold highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
  simp_rw [Finset.sup_eq_iSup]
  refine iSup_le ?_
  intro k
  refine iSup_le ?_
  intro hk
  exact le_iSup_of_le k <|
    le_iSup_of_le (show k ∈ Finset.Icc 2 M by
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, le_trans hk.2 hNM⟩)
      le_rfl

def evenBoundedHarmonicPolyHomogeneousImageSubmodule_inclusion
    {N M : ℕ} (hNM : N ≤ M) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N →ₗ[ℝ]
      evenBoundedHarmonicPolyHomogeneousImageSubmodule M :=
  Submodule.inclusion (evenBoundedHarmonicPolyHomogeneousImageSubmodule_mono hNM)

@[simp] theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_inclusion_apply
    {N M : ℕ} (hNM : N ≤ M)
    (f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    (evenBoundedHarmonicPolyHomogeneousImageSubmodule_inclusion hNM f :
      C(spherePoint3, ℝ)) = f := by
  rfl

theorem highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_zero_of_mem_frame_inclusion
    {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : N ≤ M)
    {f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N}
    (hf : (f : C(spherePoint3, ℝ)) ∈ continuousSphereFrameSubmodule) :
    highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hM
      (evenBoundedHarmonicPolyHomogeneousImageSubmodule_inclusion hNM f) = 0 := by
  apply highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_zero_of_mem_frame hM
  simpa using hf
