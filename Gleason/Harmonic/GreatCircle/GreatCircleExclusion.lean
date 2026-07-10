import Gleason.Harmonic.GreatCircle.GreatCircleExclusionA
import Gleason.Harmonic.GreatCircle.GreatCircleExclusionB

noncomputable section

theorem not_continuousHarmonicSphereDegreeSubmodule_one_le_continuousSphereGreatCircleConstraintSubmodule :
    ¬ continuousHarmonicSphereDegreeSubmodule 1 ≤ continuousSphereGreatCircleConstraintSubmodule := by
  exact
    not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCircleConstraintSubmodule_of_mod_ne_two
      (by norm_num) (by norm_num)

theorem not_continuousHarmonicSphereDegreeSubmodule_gt_two_le_continuousSphereGreatCircleConstraintSubmodule
    {n : ℕ} (hn : 2 < n) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ continuousSphereGreatCircleConstraintSubmodule := by
  by_cases hmod : n % 4 = 2
  · exact
      not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCircleConstraintSubmodule_of_mod_eq_two
        hn hmod
  · exact
      not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCircleConstraintSubmodule_of_mod_ne_two
        (by omega) hmod
