import Gleason.Harmonic.HighDegree.EvenBoundedFrame
import Mathlib.LinearAlgebra.Projection

noncomputable section

open Complex InnerProductSpace

def lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    Submodule ℝ ↥(evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :=
  (evenBoundedHarmonicPolyHomogeneousImageSubmodule N).mapIic.symm
    ⟨lowHarmonicPolyHomogeneousImageSubmodule,
      lowHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
        hN⟩

def highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    (N : ℕ) :
    Submodule ℝ ↥(evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :=
  (evenBoundedHarmonicPolyHomogeneousImageSubmodule N).mapIic.symm
    ⟨highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
        N⟩

@[simp] theorem mapIic_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    ((evenBoundedHarmonicPolyHomogeneousImageSubmodule N).mapIic
      (lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN) : Submodule ℝ C(spherePoint3, ℝ)) =
      lowHarmonicPolyHomogeneousImageSubmodule := by
  simp [lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule]

@[simp] theorem mapIic_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    (N : ℕ) :
    ((evenBoundedHarmonicPolyHomogeneousImageSubmodule N).mapIic
      (highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) : Submodule ℝ C(spherePoint3, ℝ)) =
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  simp [highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule]

theorem lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_sup_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN ⊔
      highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N = ⊤ := by
  apply (evenBoundedHarmonicPolyHomogeneousImageSubmodule N).mapIic.injective
  rw [OrderIso.map_sup]
  apply Subtype.ext
  simpa [Submodule.coe_mapIic_apply,
    lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule,
    highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule] using
    (evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_low_sup_highEven hN).symm

theorem lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN ⊓
      highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N = ⊥ := by
  apply (evenBoundedHarmonicPolyHomogeneousImageSubmodule N).mapIic.injective
  rw [OrderIso.map_inf]
  apply Subtype.ext
  simpa [Submodule.coe_mapIic_apply,
    lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule,
    highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule] using
    lowHarmonicPolyHomogeneousImageSubmodule_inf_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_bot N

theorem isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    IsCompl
      (lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
      (highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro x hx
    simpa [lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
      hN] using hx
  · rw [codisjoint_iff]
    simpa using
      lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_sup_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
        hN

theorem existsUnique_low_high_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N)
    (f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ∃ l : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN,
      ∃ h : highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N,
        ((l : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN) :
            evenBoundedHarmonicPolyHomogeneousImageSubmodule N) + h = f ∧
          ∀ l' : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN,
            ∀ h' : highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N,
              ((l' : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN) :
                  evenBoundedHarmonicPolyHomogeneousImageSubmodule N) + h' = f →
                l' = l ∧ h' = h := by
  simpa using
    Submodule.existsUnique_add_of_isCompl
      (isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
        hN)
      f
