import Gleason.Harmonic.GreatCircle.GreatCirclePointExclusion
import Gleason.Continuity.Auxiliary.ContinuousWithoutIndependence

noncomputable section

theorem continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereGreatCirclePointConstraintSubmodule :
    continuousHarmonicSphereDegreeSubmodule 0 ≤
      continuousSphereGreatCirclePointConstraintSubmodule :=
  continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereFrameSubmodule.trans
    continuousSphereFrameSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule

theorem continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereGreatCirclePointConstraintSubmodule :
    continuousHarmonicSphereDegreeSubmodule 2 ≤
      continuousSphereGreatCirclePointConstraintSubmodule :=
  continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereFrameSubmodule.trans
    continuousSphereFrameSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule

theorem continuousSphereGreatCirclePointConstraintSubmodule_eq_sup_zero_two_of_decomposition
    {s : Set ℕ}
    (hF :
      continuousSphereGreatCirclePointConstraintSubmodule =
        ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i) :
    continuousSphereGreatCirclePointConstraintSubmodule =
      continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 := by
  have hs_subset : s ⊆ ({0, 2} : Set ℕ) := by
    intro n hn
    have hQn :
        continuousHarmonicSphereDegreeSubmodule n ≤
          continuousSphereGreatCirclePointConstraintSubmodule := by
      rw [hF]
      exact le_iSup (fun i : s => continuousHarmonicSphereDegreeSubmodule i) ⟨n, hn⟩
    cases n with
    | zero =>
        simp
    | succ n =>
        cases n with
        | zero =>
            exact
              (not_continuousHarmonicSphereDegreeSubmodule_one_le_continuousSphereGreatCirclePointConstraintSubmodule
                hQn).elim
        | succ n' =>
            cases n' with
            | zero =>
                simp
            | succ n'' =>
                have hgt : 2 < Nat.succ (Nat.succ (Nat.succ n'')) := by
                  omega
                exact
                  (not_continuousHarmonicSphereDegreeSubmodule_gt_two_le_continuousSphereGreatCirclePointConstraintSubmodule
                    hgt hQn).elim
  have hs0 : 0 ∈ s := by
    by_contra h0
    have hFle :
        continuousSphereGreatCirclePointConstraintSubmodule ≤ continuousHarmonicSphereDegreeSubmodule 2 := by
      rw [hF]
      refine iSup_le ?_
      intro i
      have hi02 : (i : ℕ) = 0 ∨ (i : ℕ) = 2 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hs_subset i.2
      rcases hi02 with hi | hi
      · exact False.elim (h0 (hi ▸ i.2))
      · simp [hi]
    exact continuousHarmonicSphereDegreeSubmodule_zero_not_le_two <|
      continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereGreatCirclePointConstraintSubmodule.trans
        hFle
  have hs2 : 2 ∈ s := by
    by_contra h2
    have hFle :
        continuousSphereGreatCirclePointConstraintSubmodule ≤ continuousHarmonicSphereDegreeSubmodule 0 := by
      rw [hF]
      refine iSup_le ?_
      intro i
      have hi02 : (i : ℕ) = 0 ∨ (i : ℕ) = 2 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hs_subset i.2
      rcases hi02 with hi | hi
      · simp [hi]
      · exact False.elim (h2 (hi ▸ i.2))
    exact continuousHarmonicSphereDegreeSubmodule_two_not_le_zero <|
      continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereGreatCirclePointConstraintSubmodule.trans
        hFle
  have hs_eq : s = ({0, 2} : Set ℕ) := by
    ext n
    constructor
    · intro hn
      exact hs_subset hn
    · intro hn
      have h02 : n = 0 ∨ n = 2 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hn
      rcases h02 with rfl | rfl
      · exact hs0
      · exact hs2
  rw [hF, hs_eq]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro i
    rcases i with ⟨i, hi⟩
    rcases Set.mem_insert_iff.mp hi with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · exact le_iSup (fun i : ({0, 2} : Set ℕ) => continuousHarmonicSphereDegreeSubmodule i) ⟨0, by simp⟩
    · exact le_iSup (fun i : ({0, 2} : Set ℕ) => continuousHarmonicSphereDegreeSubmodule i) ⟨2, by simp⟩

theorem continuousSphereGreatCirclePointConstraintSubmodule_le_continuousSphereQuadraticSubmodule_of_decomposition
    {s : Set ℕ}
    (hF :
      continuousSphereGreatCirclePointConstraintSubmodule =
        ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i) :
    continuousSphereGreatCirclePointConstraintSubmodule ≤ continuousSphereQuadraticSubmodule := by
  apply eq_sup_zero_two_imp_le_continuousSphereQuadraticSubmodule
  exact continuousSphereGreatCirclePointConstraintSubmodule_eq_sup_zero_two_of_decomposition hF
