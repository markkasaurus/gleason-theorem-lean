import Gleason.Harmonic.GreatCircle.GreatCirclePointConstraints
import Gleason.Harmonic.GreatCircle.GreatCirclePointKernel
import Gleason.Harmonic.GreatCircle.GreatCircleExclusionA
import Gleason.Harmonic.GreatCircle.GreatCircleExclusionB

noncomputable section

open Complex InnerProductSpace Real

lemma surfaceModeAL2_not_mem_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_ne_two
    {n : ℕ} (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    let g : C(spherePoint3, ℝ) :=
      ⟨sphereRestrictionLinear (surfaceModeAL2 n),
        continuous_sphereRestriction_of_harmonicHomogeneousDegree
          ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩⟩
    g ∉ continuousSphereGreatCirclePointConstraintSubmodule := by
  intro g hg
  have havg : northEquatorAverageLinear g = 0 := by
    simpa [g] using northEquatorAverage_surfaceModeAL2_zero_of_pos hn
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeAL2, sphereE1]
  have hg2_ne_neg_one : g sphereE2 ≠ -1 := by
    by_cases h0 : n % 4 = 0
    · have hg2 : g sphereE2 = 1 := by
        simpa [g] using surfaceModeAL2_sphereE2_mod_zero n h0
      linarith
    by_cases h1 : n % 4 = 1
    · have hg2 : g sphereE2 = 0 := by
        simpa [g] using surfaceModeAL2_sphereE2_mod_one n h1
      linarith
    have h3 : n % 4 = 3 := by
      omega
    have hg2 : g sphereE2 = 0 := by
      simpa [g] using surfaceModeAL2_sphereE2_mod_three n h3
    linarith
  have hstd :=
    (mem_continuousSphereGreatCirclePointConstraintSubmodule_iff g).1 hg
      sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  rw [greatCircleAverageLinear_std] at hstd
  have hg2 : g sphereE2 = -1 := by
    linarith [hstd, havg, hg1]
  exact hg2_ne_neg_one hg2

theorem not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_ne_two
    {n : ℕ} (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤
        continuousSphereGreatCirclePointConstraintSubmodule := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeAL2 n),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear (surfaceModeAL2 n) ∈ harmonicSphereDegreeSubmodule n
    exact ⟨surfaceModeAL2 n, ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩, rfl⟩
  exact
    surfaceModeAL2_not_mem_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_ne_two
      hn hmod (hle hg)

theorem not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_ne_two
    {n : ℕ} (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ stdGreatCirclePointConstraintSubmodule := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeAL2 n),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear (surfaceModeAL2 n) ∈ harmonicSphereDegreeSubmodule n
    exact ⟨surfaceModeAL2 n, ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩, rfl⟩
  have hstd : stdGreatCirclePointConstraintLinear g = 0 := by
    exact hle hg
  have havg : northEquatorAverageLinear g = 0 := by
    simpa [g] using northEquatorAverage_surfaceModeAL2_zero_of_pos hn
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeAL2, sphereE1]
  have hg2_ne_neg_one : g sphereE2 ≠ -1 := by
    by_cases h0 : n % 4 = 0
    · have hg2 : g sphereE2 = 1 := by
        simpa [g] using surfaceModeAL2_sphereE2_mod_zero n h0
      linarith
    by_cases h1 : n % 4 = 1
    · have hg2 : g sphereE2 = 0 := by
        simpa [g] using surfaceModeAL2_sphereE2_mod_one n h1
      linarith
    have h3 : n % 4 = 3 := by omega
    have hg2 : g sphereE2 = 0 := by
      simpa [g] using surfaceModeAL2_sphereE2_mod_three n h3
    linarith
  rw [stdGreatCirclePointConstraintLinear_apply] at hstd
  have hg2 : g sphereE2 = -1 := by
    linarith [hstd, havg, hg1]
  exact hg2_ne_neg_one hg2

lemma surfaceModeBL2_not_mem_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_eq_two
    {n : ℕ} (hn : 2 < n) (hmod : n % 4 = 2) :
    let g : C(spherePoint3, ℝ) :=
      ⟨sphereRestrictionLinear (surfaceModeBL2 n),
        continuous_sphereRestriction_of_harmonicHomogeneousDegree
          ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩⟩
    g ∉ continuousSphereGreatCirclePointConstraintSubmodule := by
  intro g hg
  have havg : northEquatorAverageLinear g = 0 := by
    simpa [g] using northEquatorAverage_surfaceModeBL2_zero_of_gt_two hn
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeBL2, sphereE1]
  have hg2 : g sphereE2 = 1 := by
    simpa [g] using surfaceModeBL2_sphereE2_mod_two_gt_two hn hmod
  have hstd :=
    (mem_continuousSphereGreatCirclePointConstraintSubmodule_iff g).1 hg
      sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  rw [greatCircleAverageLinear_std] at hstd
  linarith [hstd, havg, hg1, hg2]

theorem not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_eq_two
    {n : ℕ} (hn : 2 < n) (hmod : n % 4 = 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤
        continuousSphereGreatCirclePointConstraintSubmodule := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeBL2 n),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear (surfaceModeBL2 n) ∈ harmonicSphereDegreeSubmodule n
    exact ⟨surfaceModeBL2 n,
      ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩, rfl⟩
  exact
    surfaceModeBL2_not_mem_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_eq_two
      hn hmod (hle hg)

theorem not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_eq_two
    {n : ℕ} (hn : 2 < n) (hmod : n % 4 = 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ stdGreatCirclePointConstraintSubmodule := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeBL2 n),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear (surfaceModeBL2 n) ∈ harmonicSphereDegreeSubmodule n
    exact ⟨surfaceModeBL2 n,
      ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩, rfl⟩
  have hstd : stdGreatCirclePointConstraintLinear g = 0 := by
    exact hle hg
  have havg : northEquatorAverageLinear g = 0 := by
    simpa [g] using northEquatorAverage_surfaceModeBL2_zero_of_gt_two hn
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeBL2, sphereE1]
  have hg2 : g sphereE2 = 1 := by
    simpa [g] using surfaceModeBL2_sphereE2_mod_two_gt_two hn hmod
  rw [stdGreatCirclePointConstraintLinear_apply] at hstd
  linarith [hstd, havg, hg1, hg2]

theorem not_continuousHarmonicSphereDegreeSubmodule_one_le_continuousSphereGreatCirclePointConstraintSubmodule :
    ¬ continuousHarmonicSphereDegreeSubmodule 1 ≤
        continuousSphereGreatCirclePointConstraintSubmodule := by
  exact
    not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_ne_two
      (by norm_num) (by norm_num)

theorem not_continuousHarmonicSphereDegreeSubmodule_gt_two_le_continuousSphereGreatCirclePointConstraintSubmodule
    {n : ℕ} (hn : 2 < n) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤
        continuousSphereGreatCirclePointConstraintSubmodule := by
  by_cases hmod : n % 4 = 2
  · exact
      not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_eq_two
        hn hmod
  · exact
      not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule_of_mod_ne_two
        (by omega) hmod

theorem not_continuousHarmonicSphereDegreeSubmodule_one_le_stdGreatCirclePointConstraintSubmodule :
    ¬ continuousHarmonicSphereDegreeSubmodule 1 ≤ stdGreatCirclePointConstraintSubmodule := by
  exact
    not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_ne_two
      (by norm_num) (by norm_num)

theorem not_continuousHarmonicSphereDegreeSubmodule_gt_two_le_stdGreatCirclePointConstraintSubmodule
    {n : ℕ} (hn : 2 < n) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ stdGreatCirclePointConstraintSubmodule := by
  by_cases hmod : n % 4 = 2
  · exact
      not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_eq_two
        hn hmod
  · exact
      not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_ne_two
        (by omega) hmod

theorem not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_ne_zero_two
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ stdGreatCirclePointConstraintSubmodule := by
  cases n with
  | zero =>
      exact (hn0 rfl).elim
  | succ n =>
      cases n with
      | zero =>
          exact not_continuousHarmonicSphereDegreeSubmodule_one_le_stdGreatCirclePointConstraintSubmodule
      | succ n' =>
          exact
            not_continuousHarmonicSphereDegreeSubmodule_gt_two_le_stdGreatCirclePointConstraintSubmodule
              (by omega)
