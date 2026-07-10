import Gleason.Harmonic.Fischer.FischerEvenBounded
import Gleason.Harmonic.HighDegree.HighEvenBoundedClosure
import Gleason.Harmonic.HighDegree.HighEvenClosedFinal
import Gleason.Harmonic.HighDegree.EvenLowSliceIntersection
import Mathlib.Order.ModularLattice

noncomputable section

open Complex InnerProductSpace

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_zero
    :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule 0 =
      harmonicPolyHomogeneousImageSubmodule 0 := by
  unfold evenBoundedHarmonicPolyHomogeneousImageSubmodule
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro i
    have hi0 : i.1 = 0 := Nat.eq_zero_of_le_zero i.2
    simpa [hi0]
  · exact le_iSup (fun i : Set.Iic 0 => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
      ⟨0, le_rfl⟩

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_low
    :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule 1 =
      lowHarmonicPolyHomogeneousImageSubmodule := by
  unfold evenBoundedHarmonicPolyHomogeneousImageSubmodule lowHarmonicPolyHomogeneousImageSubmodule
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro i
    have hi : i.1 ≤ 1 := i.2
    have hi01 : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi01 with hi0 | hi1
    · exact
        show harmonicPolyHomogeneousImageSubmodule (2 * i.1) ≤
            harmonicPolyHomogeneousImageSubmodule 0 ⊔ harmonicPolyHomogeneousImageSubmodule 2 by
          simpa [hi0] using
            (show harmonicPolyHomogeneousImageSubmodule 0 ≤
                harmonicPolyHomogeneousImageSubmodule 0 ⊔ harmonicPolyHomogeneousImageSubmodule 2 from
              le_sup_left)
    · simpa [hi1] using (le_sup_right : harmonicPolyHomogeneousImageSubmodule 2 ≤
        harmonicPolyHomogeneousImageSubmodule 0 ⊔ harmonicPolyHomogeneousImageSubmodule 2)
  · refine sup_le ?_ ?_
    · exact
          le_iSup (fun i : Set.Iic 1 => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
          ⟨0, Nat.zero_le 1⟩
    · exact
          le_iSup (fun i : Set.Iic 1 => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
          ⟨1, le_rfl⟩

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_low_sup_highEven
    {N : ℕ} (hN : 1 ≤ N) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N =
      lowHarmonicPolyHomogeneousImageSubmodule ⊔
        highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  unfold evenBoundedHarmonicPolyHomogeneousImageSubmodule
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro i
    have hi : i.1 ≤ N := i.2
    have hi_cases : i.1 = 0 ∨ i.1 = 1 ∨ 2 ≤ i.1 := by omega
    rcases hi_cases with hi0 | hi1 | hi2
    · exact le_sup_of_le_left <| by
        simpa [hi0, lowHarmonicPolyHomogeneousImageSubmodule] using
          (show harmonicPolyHomogeneousImageSubmodule 0 ≤
              lowHarmonicPolyHomogeneousImageSubmodule from
            by
              rw [lowHarmonicPolyHomogeneousImageSubmodule]
              exact le_sup_left)
    · exact le_sup_of_le_left <| by
        simpa [hi1, lowHarmonicPolyHomogeneousImageSubmodule] using
          (show harmonicPolyHomogeneousImageSubmodule 2 ≤
              lowHarmonicPolyHomogeneousImageSubmodule from
            by
              rw [lowHarmonicPolyHomogeneousImageSubmodule]
              exact le_sup_right)
    · exact le_sup_of_le_right <| by
        change harmonicPolyHomogeneousImageSubmodule (2 * i.1) ≤
          (Finset.Icc 2 N).sup (fun k => harmonicPolyHomogeneousImageSubmodule (2 * k))
        exact Finset.le_sup (f := fun k : ℕ => harmonicPolyHomogeneousImageSubmodule (2 * k))
          (s := Finset.Icc 2 N) <| Finset.mem_Icc.mpr ⟨hi2, i.2⟩
  · refine sup_le ?_ ?_
    · rw [lowHarmonicPolyHomogeneousImageSubmodule]
      refine sup_le ?_ ?_
      · exact
          le_iSup (fun i : Set.Iic N => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
            ⟨0, Nat.zero_le N⟩
      · exact
          le_iSup (fun i : Set.Iic N => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
            ⟨1, hN⟩
    · exact highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule N

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_zero
    :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule 0 ⊓ continuousSphereFrameSubmodule =
      harmonicPolyHomogeneousImageSubmodule 0 := by
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_zero]
  exact inf_eq_left.mpr harmonicPolyHomogeneousImageSubmodule_zero_le_continuousSphereFrameSubmodule

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_low
    {N : ℕ} (hN : 1 ≤ N) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N ⊓ continuousSphereFrameSubmodule =
      lowHarmonicPolyHomogeneousImageSubmodule := by
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_low_sup_highEven hN]
  rw [sup_inf_assoc_of_le
    (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereFrameSubmodule]
  rw [highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_bot,
    sup_bot_eq]
