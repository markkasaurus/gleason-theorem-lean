import Gleason.Continuity.CircleFrame
import Gleason.Harmonic.Auxiliary.TestFunctions

noncomputable section

open Real

lemma not_circleCosMode_frame_of_pos_of_mod_ne_two {n : ℕ}
    (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    ¬ circleFrameFunction (circleCosMode n) := by
  intro hframe
  rcases (circleCosMode_frame_iff n).1 hframe with rfl | htwo
  · exact (Nat.lt_irrefl 0) hn
  · exact hmod (by simpa [Nat.ModEq] using htwo)

theorem explicit_surface_modes_not_both_circleFrame {n : ℕ} (hn : 2 < n) :
    ¬ (circleFrameFunction (fun θ => surfaceModeA n (Real.cos θ) (Real.sin θ) 0) ∧
        circleFrameFunction (fun θ => surfaceModeB n (Real.cos θ) (Real.sin θ) 0)) := by
  by_cases hmod : n % 4 = 2
  · intro hpair
    have hn2le : 2 ≤ n := le_of_lt hn
    have hn2pos : 0 < n - 2 := by omega
    have hmodB : (n - 2) % 4 ≠ 2 := by
      omega
    have hframeB : circleFrameFunction (circleCosMode (n - 2)) := by
      simpa [circleCosMode, surfaceModeB_equator hn2le] using hpair.2
    exact not_circleCosMode_frame_of_pos_of_mod_ne_two hn2pos hmodB hframeB
  · intro hpair
    have hnpos : 0 < n := lt_trans (by decide) hn
    have hframeA : circleFrameFunction (circleCosMode n) := by
      simpa [circleCosMode, surfaceModeA_equator] using hpair.1
    exact not_circleCosMode_frame_of_pos_of_mod_ne_two hnpos hmod hframeA
